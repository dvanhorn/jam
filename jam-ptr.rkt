#lang racket
(require redex/reduction-semantics)
(require "util.rkt"
	 "lang.rkt"
	 "util/test.rkt")
(provide (except-out (all-defined-out) test))
(test-suite test jam-ptr)

(define-metafunction JS
  ς-alloc : ς -> (n ...)
  [(ς-alloc (cont σ D (C2 C x e ρ) v))
   ((sto-alloc σ))]
  [(ς-alloc (cont σ D (C13 C) v))
   ((sto-alloc σ))]
  [(ς-alloc (appl σ D C (pr-app ((func (x ..._1) e) ρ) (v ..._1))))
   ,(build-list (length (term (x ...))) 
                (let ((b (term (sto-alloc σ))))
                  (λ (i) (+ i b))))]
  [(ς-alloc (appl σ (D3 D C x e ρ) C_0 (pr-throw v)))
   ((sto-alloc σ))])

(define-metafunction JS
  sto-extend* : (n ...) (v ...) σ -> σ
  [(sto-extend* () () σ) σ]
  [(sto-extend* (n n_0 ...) (v v_0 ...) σ)
   (sto-extend* (n_0 ...) (v_0 ...) (sto-extend n v σ))])

(define JAM*-step
  (reduction-relation 
   JS #:domain ς*
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   (--> (eval σ x ρ D C)
        (cont σ D C (sto-lookup σ (env-lookup x ρ))))   
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
   (--> (eval σ q ρ D C)
        (cont σ D C q))
   (--> (eval σ (func (x ...) e) ρ D C)
        (cont σ D C ((func (x ...) e) ρ)))
   (--> (eval σ (rec) ρ D C)
        (cont σ D C (rec)))
   (--> (eval σ (rec (s_0 e_0) (s e) ...) ρ D C)
        (eval σ e_0 ρ D (C5 C () s_0 ((s (e ρ)) ...))))
   (--> (eval σ (let (x e_0) e_1) ρ D C)
        (eval σ e_0 ρ D (C2 C x e_1 ρ)))
   (--> (eval σ (e_0 e_1 ...) ρ D C)
        (eval σ e_0 ρ D (C3 C ((e_1 ρ) ...))))
   (--> (eval σ (rec-ref e_0 e_1) ρ D C)
        (eval σ e_0 ρ D (C6 C e_1 ρ)))
   (--> (eval σ (rec-set e_0 e_1 e_2) ρ D C)
        (eval σ e_0 ρ D (C8 C e_1 e_2 ρ)))
   (--> (eval σ (rec-del e_0 e_1) ρ D C)
        (eval σ e_0 ρ D (C11 C e_1 ρ)))
   (--> (eval σ (ref e) ρ D C)
        (eval σ e ρ D (C13 C)))
   (--> (eval σ (deref e) ρ D C)
        (eval σ e ρ D (C14 C)))
   (--> (eval σ (set e_0 e_1) ρ D C)
        (eval σ e_0 ρ D (C15 C e_1 ρ)))
   (--> (eval σ (if e_0 e_1 e_2) ρ D C)
        (eval σ e_0 ρ D (C17 C e_1 ρ e_2 ρ)))
   (--> (eval σ (begin e_0 e_1) ρ D C)
        (eval σ e_0 ρ D (C18 C e_1 ρ)))
   (--> (eval σ (while e_0 e_1) ρ D C)
        (eval σ (if e_0 (begin e_1 (while e_0 e_1)) undefn) ρ D C))
   (--> (eval σ (label l e) ρ D C)
        (eval σ e ρ (D4 D C l) C1))
   (--> (eval σ (break l e) ρ D C)
        (eval σ e ρ D (C20 C l)))
   (--> (eval σ (try/catch e_0 x e_1) ρ D C)
        (eval σ e_0 ρ (D3 D C x e_1 ρ) C1))
   (--> (eval σ (try/finally e_0 e_1) ρ D C)
        (eval σ e_0 ρ (D2 D C e_1 ρ) C1))
   (--> (eval σ (throw e) ρ D C)
        (eval σ e ρ D (C19 C)))
   (--> (eval σ (prim op) ρ D C)
        (appl σ D C (pr-op op ())))
   (--> (eval σ (prim op e_0 e_1 ...) ρ D C)
        (eval σ e_0 ρ D (C21 C op () ((e_1 ρ) ...))))
   
   (--> (cont σ D1 C1 v)
        (val v σ))
   (--> (cont σ (D2 D C e ρ) C1 v)
        (eval σ e ρ D (C22 C v)))
   (--> (cont σ (D3 D C x e ρ) C1 v)
        (cont σ D C v))
   (--> (cont σ (D4 D C l) C1 v)
        (cont σ D C v))
   
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   (--> (cont σ D (C2 C x e ρ) v)
        (eval (sto-extend n v σ) e (env-extend (x) (n) ρ) D C)
        (where (n) (ς-alloc (cont σ D (C2 C x e ρ) v))))
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
   (--> (cont σ D (C3 C ()) v)
        (appl σ D C (pr-app v ())))
   (--> (cont σ D (C3 C ((e_0 ρ_0) (e_1 ρ_1) ...)) v)
        (eval σ e_0 ρ_0 D (C4 C v () ((e_1 ρ_1) ...))))
   (--> (cont σ D (C4 C v_0 (v_1 ...) ((e_0 ρ_0) (e_1 ρ_1) ...)) v)
        (eval σ e_0 ρ_0 D (C4 C v_0 (v_1 ... v) ((e_1 ρ_1) ...))))
   (--> (cont σ D (C4 C v_0 (v_1 ...) ()) v)
        (appl σ D C (pr-app v_0 (v_1 ... v))))
   (--> (cont σ D (C5 C ((s_0 v_0) ...) s ()) v)
        (cont σ D C (rec (s_0 v_0) ... (s v))))
   (--> (cont σ D (C5 C ((s_0 v_0) ...) s ((s_1 (e_1 ρ_1)) (s_2 (e_2 ρ_2)) ...)) v)
        (eval σ e_1 ρ_1 D (C5 C ((s_0 v_0) ... (s v)) s_1 ((s_2 (e_2 ρ_2)) ...))))
   (--> (cont σ D (C6 C e ρ) v)
        (eval σ e ρ D (C7 C v)))
   (--> (cont σ D (C7 C v_0) v)
        (appl σ D C (pr-rec-ref v_0 v)))
   (--> (cont σ D (C8 C e_0 e_1 ρ) v)
        (eval σ e_0 ρ D (C9 C v e_1 ρ)))
   (--> (cont σ D (C9 C v_0 e ρ) v)
        (eval σ e ρ D (C10 C v_0 v)))
   (--> (cont σ D (C10 C v_0 v_1) v)
        (appl σ D C (pr-rec-set v_0 v_1 v)))
   (--> (cont σ D (C11 C e ρ) v)
        (eval σ e ρ D (C12 C v)))
   (--> (cont σ D (C12 C v_0) v)
        (appl σ D C (pr-rec-del v_0 v)))
   (--> (cont σ D (C13 C) v)        
        (cont (sto-extend n v σ) D C (addr n))
        (where (n) (ς-alloc (cont σ D (C13 C) v))))
   (--> (cont σ D (C14 C) v)
        (appl σ D C (pr-deref v)))
   (--> (cont σ D (C15 C e ρ) v)
        (eval σ e ρ D (C16 C v)))
   (--> (cont σ D (C16 C v_0) v)
        (appl σ D C (pr-set v_0 v)))
   (--> (cont σ D (C17 C e_0 ρ_0 e_1 ρ_1) v)
        (appl σ D C (pr-if v e_0 ρ_0 e_1 ρ_1)))
   (--> (cont σ D (C18 C e ρ) v)
        (eval σ e ρ D C))
   (--> (cont σ D (C19 C) v)
        (appl σ D C (pr-throw v)))
   (--> (cont σ D (C20 C l) v)
        (appl σ D C (pr-break l v)))
   (--> (cont σ D (C21 C op (v_0 ...) ()) v)
        (appl σ D C (pr-op op (v_0 ... v))))
   (--> (cont σ D (C21 C op (v_0 ...) ((e_0 ρ_0) (e_1 ρ_1) ...)) v)
        (eval σ e_0 ρ_0 D (C21 C op (v_0 ... v) ((e_1 ρ_1) ...))))
   (--> (cont σ D (C22 C v_0) v)
        (cont σ D C v_0))
   (--> (cont σ D (C23 C v_0) v)
        (appl σ D C (pr-throw v_0)))
   (--> (cont σ D (C24 C l v_0) v)
        (appl σ D C (pr-break l v_0)))
   
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   (--> (appl σ D C (pr-app ((func (x ..._1) e) ρ) (v ..._1)))
        (eval (sto-extend* (n ...) (v ...) σ) e (env-extend (x ...) (n ...) ρ) D C)
        (where (n ...) (ς-alloc (appl σ D C (pr-app ((func (x ...) e) ρ) (v ...))))))
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
   (--> (appl σ D C (pr-app ((func (x ..._!_1) e) ρ) (v ..._!_1)))
        (appl σ D C (pr-throw "Arity mismatch")))
   (--> (appl σ D C (pr-app v (v_0 ...)))
        (appl σ D C (pr-throw "Not a function"))
        (side-condition (not (term (function? v)))))
   (--> (appl σ D C (pr-rec-ref (rec (s v) ...) s_0))
        (cont σ D C (rec-lookup ((s v) ...) s_0)))
   (--> (appl σ D C (pr-rec-ref v_0 v_1))
        (appl σ D C (pr-throw "Bad record ref"))
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))
   (--> (appl σ D C (pr-rec-set (rec (s v) ...) s_0 v_0))
        (cont σ D C (rec-update ((s v) ...) s_0 v_0)))
   (--> (appl σ D C (pr-rec-set v_0 v_1 v_2))
        (appl σ D C (pr-throw "Bad record set"))
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))
   (--> (appl σ D C (pr-rec-del (rec (s v) ...) s_0))
        (cont σ D C (rec-delete ((s v) ...) s_0)))
   (--> (appl σ D C (pr-rec-del v_0 v_1))
        (appl σ D C (pr-throw "Bad record del"))
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))
   (--> (appl σ D C (pr-if true e_0 ρ_0 e_1 ρ_1))
        (eval σ e_0 ρ_0 D C))
   (--> (appl σ D C (pr-if false e_0 ρ_0 e_1 ρ_1))
        (eval σ e_1 ρ_1 D C))
   (--> (appl σ D C (pr-if v e_0 ρ_0 e_1 ρ_1))
        (appl σ D C (pr-throw "Not a boolean"))
        (side-condition (not (term (boolean? v)))))
   ;; Inlined the well-defined cases in order to make testing feasible.
   #;
   (--> (appl σ D C (pr-op op (v ...)))
        (cont σ D C (δ op v ...))
        (side-condition (term (in-δ-dom? op v ...))))
   (--> (appl σ D C (pr-op + (n_0 n_1)))
        (cont σ D C (δ + n_0 n_1)))
   (--> (appl σ D C (pr-op number->string (n)))
        (cont σ D C (δ number->string n)))
   (--> (appl σ D C (pr-op op (v ...)))
        (appl σ D C (pr-throw "Bad primop"))
        (side-condition (not (term (in-δ-dom? op v ...)))))
   (--> (appl σ D C (pr-deref (addr n)))
        (cont σ D C (sto-lookup σ n))
        (side-condition (term (in-sto-dom? σ n))))
   (--> (appl σ D C (pr-deref (addr n)))
        (appl σ D C (pr-throw "Null pointer"))
        (side-condition (not (term (in-sto-dom? σ n)))))
   (--> (appl σ D C (pr-deref v))
        (appl σ D C (pr-throw "Not an address"))
        (side-condition (not (term (address? v)))))   
   (--> (appl σ D C (pr-set (addr n) v))
        (cont (sto-update σ n v) D C v)
        (side-condition (term (in-sto-dom? σ n))))   
   (--> (appl σ D C (pr-set (addr n) v))
        (appl σ D C (pr-throw "Null pointer"))
        (side-condition (not (term (in-sto-dom? σ n)))))
   (--> (appl σ D C (pr-set v_0 v_1))
        (appl σ D C (pr-throw "Not an address"))
        (side-condition (not (term (address? v_0)))))
   (--> (appl σ D1 C (pr-throw v))
        (err v σ))
   (--> (appl σ (D2 D C e ρ) C_0 (pr-throw v))
        (eval σ e ρ D (C23 C v)))
   
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   (--> (appl σ (D3 D C x e ρ) C_0 (pr-throw v))
        (eval (sto-extend n v σ) e (env-extend (x) (n) ρ) D C)
        (where (n) (ς-alloc (appl σ (D3 D C x e ρ) C_0 (pr-throw v)))))
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   
   (--> (appl σ (D4 D C l) C_0 (pr-throw v))
        (appl σ D C (pr-throw v)))
   (--> (appl σ D1 C (pr-break l v))
        (appl σ D1 C (pr-throw "Unlabeled break")))
   (--> (appl σ (D2 D C e ρ) C_0 (pr-break l v))
        (eval σ e ρ D (C24 C l v)))
   (--> (appl σ (D3 D C x e ρ) C_0 (pr-break l v))
        (appl σ D C (pr-break l v)))
   (--> (appl σ (D4 D C l) C_0 (pr-break l v))
        (cont σ D C v))
   (--> (appl σ (D4 D C l_0) C_0 (pr-break l_1 v))
        (appl σ D C (pr-break l_0 v))
        (side-condition (not (equal? (term l_0) (term l_1)))))
   ))

(test
 (define-metafunction JS
   close/store : e -> (eval σ* e ρ* D1 C1)
   [(close/store e)
    ,(let ((fv (set->list (term (fv e)))))
       (term (eval ,(build-list (length fv) (λ (i) (list i 0)))
		   e
		   ,(list (map list fv (build-list (length fv) (λ (i) i))))
		   D1
		   C1)))])

 #;
 (define-metafunction JS
   unload : ς* -> ς
   [(unload (eval σ* e ρ* D* C*))  ..]
   [(unload (cont σ* D* C* v*)) ...]
   [(unload (appl σ* D* C* pr*)) ...]
   [(unload (err v* σ*)) ...]
   [(unload (val v* σ*)) ...])
 
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; Property: for all expressions e, 
 ;; - (eval σ e ρ D1 C1)  --JAM*-->* ans, or 
 ;; - (eval σ e ρ D1 C1) --JAM*-->* ς' --JAM*--> ς'' --JAM*-->* ς'.
 ;; where ρ,σ closes e.
 
 (redex-check JS e
	      (match (apply-reduction-relation* JAM*-step (term (close/store e)))
                [(list) #t] ;; the program loops               
                [(list r)   ;; the program produced an answer
                 (redex-match JS ans r)])))
              
              
              