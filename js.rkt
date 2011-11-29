#lang racket
(require redex/reduction-semantics)
(require "util.rkt"
	 "lang.rkt")
(provide λρJS-step)
(test-suite test js)

(define-metafunction JS
  A-norm : 𝓼 -> 𝓼
  [(A-norm (σ V)) (val V σ)]
  [(A-norm (σ (in-hole 𝓔 PR))) (σ (in-hole 𝓔 PR))] 
  [(A-norm (σ (in-hole 𝓔 (clos (rec (S E) ...) ρ))))
   (A-norm (σ (in-hole 𝓔 (rec (S (clos E ρ)) ...))))]
  [(A-norm (σ (in-hole 𝓔 (clos (let (X E_0) E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (let (X (clos E_0 ρ)) (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (app E_0 E_1 ...) ρ))))
   (A-norm (σ (in-hole 𝓔 (app (clos E_0 ρ) (clos E_1 ρ) ...))))]
  [(A-norm (σ (in-hole 𝓔 (clos (rec-ref E_0 E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (rec-ref (clos E_0 ρ) (clos e_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (rec-set E_0 E_1 E_2) ρ))))
   (A-norm (σ (in-hole 𝓔 (rec-set (clos E_0 ρ) (clos E_1 ρ) (clos E_2 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (rec-del E_0 E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (rec-del (clos E_0 ρ) (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (set E_0 E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (set (clos E_0 ρ) (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (ref E) ρ))))
   (A-norm (σ (in-hole 𝓔 (ref (clos E ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (deref E) ρ))))
   (A-norm (σ (in-hole 𝓔 (deref (clos E ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (if E_0 E_1 E_2) ρ))))
   (A-norm (σ (in-hole 𝓔 (if (clos E_0 ρ) (clos E_1 ρ) (clos E_2 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (begin E_0 E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (begin (clos E_0 ρ) (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (label L E) ρ))))
   (A-norm (σ (in-hole 𝓔 (label L (clos E ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (break L E) ρ))))
   (A-norm (σ (in-hole 𝓔 (break L (clos E ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (try/catch E_0 X E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (try/catch (clos E_0 ρ) X (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (try/finally E_0 E_1) ρ))))
   (A-norm (σ (in-hole 𝓔 (try/finally (clos E_0 ρ) (clos E_1 ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (throw E) ρ))))
   (A-norm (σ (in-hole 𝓔 (throw (clos E ρ)))))]
  [(A-norm (σ (in-hole 𝓔 (clos (prim OP E ...) ρ))))
   (A-norm (σ (in-hole 𝓔 (prim OP (clos E ρ) ...))))])

(define-metafunction JS
  sto : -> σ ;; FIXME extend for convenient sto notation.  Don't write literal stores.
  [(sto) ()])

(define-metafunction JS
  env : -> ρ ;; FIXME extend for convenient env notation.  Don't write literal environments.
  [(env) ()])

(test
 (test-equal (term (A-norm ((sto) (clos (rec) (env))))) (term (val (rec) (sto))))
 (test-equal (term (A-norm ((sto) (clos (rec ("x" (prim + 1 2))) (env)))))
             (term ((sto) (rec ("x" (prim + (clos 1 (env)) (clos 2 (env))))))))
 (test-equal (term (A-norm ((sto) (clos (if 1 2 3) (env)))))
             (term ((sto) (if (clos 1 (env)) (clos 2 (env)) (clos 3 (env)))))))
   
(define λρJS-step
  (reduction-relation 
   JS #:domain 𝓼
   ;; Final answer
   (--> (σ V) (val V σ))
   
   ;; While expansion
   (==> (clos (while E_0 E_1) ρ)
        (clos (if E_0 (begin E_1 (while E_0 e_1)) undefn) ρ))
   
   ;; Context-insensitive, store-insensitive rules
   (==> (clos X ρ)   ;; FIXME may or may not go through store
        (env-lookup X ρ))
   (==> (let (X V) (clos E ρ))   ;; FIXME rewrite to a bind form that may or may not go through the store.
        (clos E (env-extend (X) (V) ρ)))
   (==> (app ((func (X ..._1) E) ρ) V ..._1)
        (clos E (env-extend (X ...) (V ...) ρ)))
   (==> (app (clos (func (X ..._!_1) e) ρ) V ..._!_1)
        (throw "Arity mismatch"))
   (==> (app V V_0 ...)
        (throw "Not a function")
        (side-condition (not (term (function? V)))))
   (==> (rec-ref (rec (S V) ...) S_0)
        (rec-lookup ((S V) ...) S_0))   
   (==> (rec-ref V_0 V_1)
        (throw "Bad record ref")
        (side-condition (or (not (term (record? V_0)))
                            (not (term (string? V_1))))))   
   (==> (rec-set (rec (S V) ...) S_0 V_0)
        (rec-update ((S V) ...) S_0 V_0))
   (==> (rec-set V_0 V_1 V_2)
        (throw "Bad record set")
        (side-condition (or (not (term (record? V_0)))
                            (not (term (string? V_1))))))
   (==> (rec-del (rec (S V) ...) S_0)
        (rec-delete ((S V) ...) S_0))
   (==> (rec-del V_0 V_1)
        (throw "Bad record del")
        (side-condition (or (not (term (record? V_0)))
                            (not (term (string? V_1))))))
   (==> (if true c_0 c_1) c_0)   
   (==> (if false c_0 c_1) c_1)
   (==> (if v c_0 c_1)
        (throw "Not a boolean")
        (side-condition (not (term (boolean? V)))))
   (==> (begin V c) c)
   (==> (try/catch V X (clos E ρ)) V)
   (==> (try/finally V c) 
        (begin c V))
   (==> (label l V) V)
   ;; Inlined the well-defined cases in order to make testing feasible.
   #;
   (==> (prim OP V ...)
        (δ OP V ...)
        (side-condition (term (in-δ-dom? OP V ...))))
   (==> (prim + N_0 N_1)
        (δ + N_0 N_1))
   (==> (prim number->string N)
        (δ number->string N))
   (==> (prim OP V ...)
        (throw "Bad primop")
        (side-condition (not (term (in-δ-dom? OP V ...)))))
      
   ;; Context-sensitive, store-sensitive rules
   (--> (σ (in-hole 𝓔 (ref V)))
        ((sto-extend N V σ) (in-hole 𝓔 (addr N)))
        (where N (sto-alloc σ)))        
   (--> (σ (in-hole 𝓔 (deref (addr N))))
        (σ (in-hole 𝓔 (sto-lookup σ N)))
        (side-condition (term (in-sto-dom? σ N))))
   (--> (σ (in-hole 𝓔 (deref (addr N))))
        (σ (in-hole 𝓔 (throw "Null pointer")))
        (side-condition (not (term (in-sto-dom? σ N)))))   
   (==> (deref V)
        (throw "Not an address")
        (side-condition (not (term (address? V)))))   
   (--> (σ (in-hole 𝓔 (set (addr N) V)))
        ((sto-update σ N V) (in-hole 𝓔 V))
        (side-condition (term (in-sto-dom? σ N))))   
   (--> (σ (in-hole 𝓔 (set (addr N) V)))
        (σ (in-hole 𝓔 (throw "Null pointer")))
        (side-condition (not (term (in-sto-dom? σ N)))))   
   (==> (set V_0 V_1)
        (throw "Not an address")
        (side-condition (not (term (address? V_0)))))
   (--> (σ (in-hole 𝓒 (throw V)))
        (err V σ))
   (==> (try/finally (in-hole 𝓒 (throw V)) c)
        (begin c (throw V)))
   (==> (try/catch (in-hole 𝓒 (throw V)) X (clos E ρ))
        (clos E (env-extend (X) (V) ρ)))   
   (==> (label L (in-hole 𝓒 (throw V)))
        (throw V))
   (--> (σ (in-hole 𝓒 (break L V)))
        (σ (in-hole 𝓒 (throw "Unlabeled break"))))
   (==> (try/finally (in-hole 𝓒 (break L V)) c)
        (begin c (break L V)))
   (==> (try/catch (in-hole 𝓒 (break L V)) X (clos E ρ))
        (break L V))
   (==> (label L (in-hole 𝓒 (break L V)))
        V)
   (==> (label L_0 (in-hole 𝓒 (break L_1 V)))
        (break L_1 V)
        (side-condition (not (equal? (term L_0) (term L_1)))))   
   with
   [(--> (σ (in-hole 𝓔 c_0)) (σ (in-hole 𝓔 c_1)))
    (==> c_0 c_1)]))
  

#;
(test--> λρJS-step
         (term (() (((func () 5) ()) 7)))
         (term (() (throw "Arity mismatch"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Property: for all closed states 𝓼, 
;; - 𝓼 -->* ans, or 
;; - 𝓼 -->* 𝓼' --> 𝓼'' -->* 𝓼'.

#;
(test
 (redex-check JS 𝓼
	      (match (apply-reduction-relation* λρJS-step (term 𝓼))
                [(list) #t] ;; the program loops               
                [(list r)   ;; the program produced an answer
                 (redex-match JS ans r)])
	      #:source λρJS-step
	      #:prepare (λ (𝓼) (term (seal-𝓼/0 ,𝓼)))))
