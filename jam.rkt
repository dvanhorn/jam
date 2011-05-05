#lang racket
(require redex/reduction-semantics)
(require "util.rkt"
	 "lang.rkt"
	 "util/test.rkt")
(provide JAM-step)
(test-suite test jam)

(define JAM-step
  (reduction-relation 
   JS #:domain ς
   (--> (eval σ x ρ D C)
        (cont σ D C (env-lookup x ρ)))
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
   (--> (eval σ (app e_0 e_1 ...) ρ D C)
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
   (--> (cont σ D (C2 C x e ρ) v)
        (eval σ e (env-extend (x) (v) ρ) D C))
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
        (where n (sto-alloc σ)))
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
   
   (--> (appl σ D C (pr-app ((func (x ..._1) e) ρ) (v ..._1)))
        (eval σ e (env-extend (x ...) (v ...) ρ) D C))
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
   (--> (appl σ (D3 D C x e ρ) C_0 (pr-throw v))
        (eval σ e (env-extend (x) (v) ρ) D C))
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
        (appl σ D C (pr-break l_1 v))
        (side-condition (not (equal? (term l_0) (term l_1)))))))

(test
 ;; Unit tests for metafunctions

 (test-equal (term (sto-lookup ((4 "x")) 4)) (term "x"))
 (test-equal (term (in-sto-dom? ((4 "x")) 4)) (term #t))
 (test-equal (term (in-sto-dom? ((4 "x")) 7)) (term #f))
 
 ;; Unit tests for reduction relation
 
 (test--> JAM-step
	  (term (eval () x (((x 5))) D1 C1))
	  (term (cont () D1 C1 5)))
 (test--> JAM-step
	  (term (eval () "x" () D1 C1))
	  (term (cont () D1 C1 "x")))
 (test--> JAM-step
	  (term (eval () 5 () D1 C1))
	  (term (cont () D1 C1 5)))
 (test--> JAM-step
	  (term (eval () true () D1 C1))
	  (term (cont () D1 C1 true)))
 (test--> JAM-step
	  (term (eval () false () D1 C1))
	  (term (cont () D1 C1 false)))
 (test--> JAM-step
	  (term (eval () undefn () D1 C1))
	  (term (cont () D1 C1 undefn)))
 (test--> JAM-step
	  (term (eval () null () D1 C1))
	  (term (cont () D1 C1 null)))
 (test--> JAM-step
	  (term (eval () (addr 5) () D1 C1))
	  (term (cont () D1 C1 (addr 5))))
 (test--> JAM-step
	  (term (eval () (func (x) z) (((z 5))) D1 C1))
	  (term (cont () D1 C1 ((func (x) z) (((z 5)))))))
 (test--> JAM-step
	  (term (eval () (rec) () D1 C1))
	  (term (cont () D1 C1 (rec))))
 (test--> JAM-step
	  (term (eval () (rec ("x" 5)) () D1 C1))
	  (term (eval () 5 () D1 (C5 C1 () "x" ()))))
 (test--> JAM-step
	  (term (eval () (let (x 5) x) () D1 C1))
	  (term (eval () 5 () D1 (C2 C1 x x ()))))
 (test--> JAM-step
	  (term (eval () (app f) () D1 C1))
	  (term (eval () f () D1 (C3 C1 ()))))
 (test--> JAM-step
	  (term (eval () (rec-ref x y) () D1 C1))
	  (term (eval () x () D1 (C6 C1 y ()))))
 (test--> JAM-step
	  (term (eval () (rec-set x y z) () D1 C1))
	  (term (eval () x () D1 (C8 C1 y z ()))))
 (test--> JAM-step
	  (term (eval () (rec-del x y) () D1 C1))
	  (term (eval () x () D1 (C11 C1 y ()))))
 (test--> JAM-step
	  (term (eval () (ref x) () D1 C1))
	  (term (eval () x () D1 (C13 C1))))
 (test--> JAM-step
	  (term (eval () (deref x) () D1 C1))
	  (term (eval () x () D1 (C14 C1))))
 (test--> JAM-step
	  (term (eval () (set x y) () D1 C1))
	  (term (eval () x () D1 (C15 C1 y ()))))
 (test--> JAM-step
	  (term (eval () (if x y z) () D1 C1))
	  (term (eval () x () D1 (C17 C1 y () z ()))))
 (test--> JAM-step
	  (term (eval () (begin x y) () D1 C1))
	  (term (eval () x () D1 (C18 C1 y ()))))
 (test--> JAM-step
	  (term (eval () (while x y) () D1 C1))
	  (term (eval () (if x (begin y (while x y)) undefn) () D1 C1)))
 (test--> JAM-step
	  (term (eval () (label "x" x) () D1 C1))
	  (term (eval () x () (D4 D1 C1 "x") C1)))
 (test--> JAM-step
	  (term (eval () (break "x" x) () D1 C1))
	  (term (eval () x () D1 (C20 C1 "x"))))
 (test--> JAM-step
	  (term (eval () (try/catch x y z) () D1 C1))
	  (term (eval () x () (D3 D1 C1 y z ()) C1)))
 (test--> JAM-step
	  (term (eval () (try/finally x y) () D1 C1))
	  (term (eval () x () (D2 D1 C1 y ()) C1)))
 (test--> JAM-step
	  (term (eval () (throw x) () D1 C1))
	  (term (eval () x () D1 (C19 C1))))
 (test--> JAM-step
	  (term (eval () (prim +) () D1 C1))
	  (term (appl () D1 C1 (pr-op + ()))))
 (test--> JAM-step
	  (term (eval () (prim + x y) () D1 C1))
	  (term (eval () x () D1 (C21 C1 + () ((y ()))))))
 (test--> JAM-step
	  (term (cont () D1 C1 5))
	  (term (val 5 ())))
 (test--> JAM-step
	  (term (cont () (D2 D1 C1 x ()) C1 5))
	  (term (eval () x () D1 (C22 C1 5))))
 (test--> JAM-step
	  (term (cont () (D3 D1 C1 x y ()) C1 5))
	  (term (cont () D1 C1 5)))
 (test--> JAM-step
	  (term (cont () (D4 D1 C1 "x") C1 5))
	  (term (cont () D1 C1 5)))
 (test--> JAM-step 
	  (term (cont () D1 (C2 C1 x y ()) 5))
	  (term (eval () y (((x 5))) D1 C1)))
 (test--> JAM-step
	  (term (cont () D1 (C3 C1 ()) 5))
	  (term (appl () D1 C1 (pr-app 5 ()))))
 (test--> JAM-step
	  (term (cont () D1 (C3 C1 ()) 5))
	  (term (appl () D1 C1 (pr-app 5 ()))))
 (test--> JAM-step
	  (term (cont () D1 (C3 C1 ((7 ()))) 5))
	  (term (eval () 7 () D1 (C4 C1 5 () ()))))
 (test--> JAM-step
	  (term (cont () D1 (C4 C1 0 (1) ((7 ()))) 8))
	  (term (eval () 7 () D1 (C4 C1 0 (1 8) ()))))
 (test--> JAM-step
	  (term (cont () D1 (C4 C1 0 (1) ()) 8))
	  (term (appl () D1 C1 (pr-app 0 (1 8)))))
 (test--> JAM-step
	  (term (cont () D1 (C5 C1 () "x" ()) 5))
	  (term (cont () D1 C1 (rec ("x" 5)))))
 (test--> JAM-step
	  (term (cont () D1 (C6 C1 5 ()) 7))
	  (term (eval () 5 () D1 (C7 C1 7))))
 
 (test--> JAM-step
	  (term (cont () D1 (C7 C1 0) 7))
	  (term (appl () D1 C1 (pr-rec-ref 0 7))))
 (test--> JAM-step 
	  (term (cont () D1 (C8 C1 0 1 ()) 7))
	  (term (eval () 0 () D1 (C9 C1 7 1 ()))))
 (test--> JAM-step
	  (term (cont () D1 (C9 C1 0 e ()) 7))
	  (term (eval () e () D1 (C10 C1 0 7))))
 (test--> JAM-step
	  (term (cont () D1 (C10 C1 0 1) 7))
	  (term (appl () D1 C1 (pr-rec-set 0 1 7))))
 (test--> JAM-step
	  (term (cont () D1 (C11 C1 0 ()) 7))
	  (term (eval () 0 () D1 (C12 C1 7))))
 (test--> JAM-step
	  (term (cont () D1 (C12 C1 0) 7))
	  (term (appl () D1 C1 (pr-rec-del 0 7))))
 ;;...
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-app ((func (x y z) x) ()) (1 2 3))))
	  (term (eval () x (((x 1) (y 2) (z 3))) D1 C1)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-app ((func () x) ()) (1 2 3))))
	  (term (appl () D1 C1 (pr-throw "Arity mismatch"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-app 5 (1 2 3))))
	  (term (appl () D1 C1 (pr-throw "Not a function"))))
 
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-ref (rec ("x" 5) ("y" 7)) "y")))
	  (term (cont () D1 C1 7)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-ref (rec ("x" 5) ("y" 7)) "z")))
	  (term (cont () D1 C1 undefn)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-ref 5 "z")))
	  (term (appl () D1 C1 (pr-throw "Bad record ref"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-ref (rec ("x" 5)) 7)))
	  (term (appl () D1 C1 (pr-throw "Bad record ref"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-set (rec ("x" 5)) "x" 7)))
	  (term (cont () D1 C1 (rec ("x" 7)))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-set (rec ("x" 5)) "y" 7)))
	  (term (cont () D1 C1 (rec ("y" 7) ("x" 5)))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-del (rec ("x" 5)) "x")))
	  (term (cont () D1 C1 (rec))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-del (rec ("x" 5)) "y")))
	  (term (cont () D1 C1 (rec ("x" 5)))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-del 5 "y")))
	  (term (appl () D1 C1 (pr-throw "Bad record del"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-rec-del (rec ("x" 5)) 7)))
	  (term (appl () D1 C1 (pr-throw "Bad record del"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-if true 5 () 7 ())))
	  (term (eval () 5 () D1 C1)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-if false 5 () 7 ())))
         (term (eval () 7 () D1 C1)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-if 8 5 () 7 ())))
	  (term (appl () D1 C1 (pr-throw "Not a boolean"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-op + (2 3))))
	  (term (cont () D1 C1 5)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-op + (2 3 5))))
         (term (appl () D1 C1 (pr-throw "Bad primop"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-op + ("2" "3"))))
	  (term (appl () D1 C1 (pr-throw "Bad primop"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-op number->string (5))))
	  (term (cont () D1 C1 "5")))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-op number->string ("5"))))
	  (term (appl () D1 C1 (pr-throw "Bad primop"))))
 (test--> JAM-step
	  (term (appl ((0 5)) D1 C1 (pr-deref (addr 0))))
	  (term (cont ((0 5)) D1 C1 5)))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-deref (addr 0))))
	  (term (appl () D1 C1 (pr-throw "Null pointer"))))
 (test--> JAM-step
	  (term (appl () D1 C1 (pr-deref 0)))
	  (term (appl () D1 C1 (pr-throw "Not an address"))))
 (test--> JAM-step
	  (term (appl ((0 5)) D1 C1 (pr-set (addr 0) 7)))
	  (term (cont ((0 7)) D1 C1 7))) 
 
 
 ;; Properties:
 
 (redex-check JS σ (not (term (in-sto-dom? σ (sto-alloc σ)))))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; Progress for JAM states:
 
 ;; Progress for closed eval states.
 (redex-check JS 
	      (eval σ e (frame ...) D C)
	      (one-step? JAM-step (term (eval σ e ((close/0 e) frame ...) D C))))
 
 ;; Progress for cont states.
 (redex-check JS 
	      (cont σ D C v)
	      (one-step? JAM-step (term (cont σ D C v))))
 
 ;; Progress for appl states.
 (redex-check JS
	      (appl σ D C pr)
	      (one-step? JAM-step (term (appl (sto-unique σ) D C (seal-pr/0 pr)))))
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
 ;; Property: for all closed states ς, 
 ;; - ς -->* ans, or 
 ;; - ς -->* ς' --> ς'' -->* ς'.
 
 ;; The above is obviously not a theorem because of the halting problem,
 ;; however it is highly unlikely that the test for the property will diverge.
 
 (redex-check JS ς
	      (match (apply-reduction-relation* JAM-step (term ς))
	        [(list) #t] ;; the program loops               
                [(list r)   ;; the program produced an answer
                 (redex-match JS ans r)])
	      #:source JAM-step
	      #:prepare (λ (ς) (term (seal-ς/0 ,ς)))))
              
              
              