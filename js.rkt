#lang racket
(require redex/reduction-semantics)
(require "util.rkt"
	 "lang.rkt")
(provide λρJS-step)
(test-suite test js)

(define λρJS-step
  (reduction-relation 
   JS #:domain 𝓼
   ;; Final answer
   (--> (σ v) (val v σ))
   
   ;; Environment elimination rules
   (==> (clos q ρ) q)
   (==> (clos (func (x ...) e) ρ) ((func (x ...) e) ρ))
   
   ;; Environment propagation rules   
   (==> (clos (rec (s e) ...) ρ)
        (rec (s (clos e ρ)) ...))
   (==> (clos (let (x e_0) e_1) ρ)
        (let (x (clos e_0 ρ)) (clos e_1 ρ)))
   (==> (clos (app e_0 e_1 ...) ρ)
        (app (clos e_0 ρ) (clos e_1 ρ) ...))
   (==> (clos (rec-ref e_0 e_1) ρ)
        (rec-ref (clos e_0 ρ) (clos e_1 ρ)))
   (==> (clos (rec-set e_0 e_1 e_2) ρ)
        (rec-set (clos e_0 ρ) (clos e_1 ρ) (clos e_2 ρ)))
   (==> (clos (rec-del e_0 e_1) ρ)
        (rec-del (clos e_0 ρ) (clos e_1 ρ)))
   (==> (clos (set e_0 e_1) ρ)
        (set (clos e_0 ρ) (clos e_1 ρ)))
   (==> (clos (ref e) ρ)
        (ref (clos e ρ)))
   (==> (clos (deref e) ρ)
        (deref (clos e ρ)))
   (==> (clos (if e_0 e_1 e_2) ρ)
        (if (clos e_0 ρ) (clos e_1 ρ) (clos e_2 ρ)))
   (==> (clos (begin e_0 e_1) ρ)
        (begin (clos e_0 ρ) (clos e_1 ρ)))
   (==> (clos (label l e) ρ)
        (label l (clos e ρ)))
   (==> (clos (break l e) ρ)
        (break l (clos e ρ)))
   (==> (clos (try/catch e_0 x e_1) ρ)
        (try/catch (clos e_0 ρ) x (clos e_1 ρ)))
   (==> (clos (try/finally e_0 e_1) ρ)
        (try/finally (clos e_0 ρ) (clos e_1 ρ)))
   (==> (clos (throw e) ρ)
        (throw (clos e ρ)))
   (==> (clos (prim op e ...) ρ)
        (prim op (clos e ρ) ...))
   
   ;; While expansion
   (==> (clos (while e_0 e_1) ρ)
        (clos (if e_0 (begin e_1 (while e_0 e_1)) undefn) ρ))
   
   ;; Context-insensitive, store-insensitive rules
   (==> (clos x ρ)
        (env-lookup x ρ))
   (==> (let (x v) (clos e ρ))
        (clos e (env-extend (x) (v) ρ)))
   (==> (app ((func (x ..._1) e) ρ) v ..._1)
        (clos e (env-extend (x ...) (v ...) ρ)))
   (==> (app ((func (x ..._!_1) e) ρ) v ..._!_1)
        (throw "Arity mismatch"))
   (==> (app v v_0 ...)
        (throw "Not a function")
        (side-condition (not (term (function? v)))))
   (==> (rec-ref (rec (s v) ...) s_0)
        (rec-lookup ((s v) ...) s_0))   
   (==> (rec-ref v_0 v_1)
        (throw "Bad record ref")
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))   
   (==> (rec-set (rec (s v) ...) s_0 v_0)
        (rec-update ((s v) ...) s_0 v_0))   
   (==> (rec-set v_0 v_1 v_2)
        (throw "Bad record set")
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))
   (==> (rec-del (rec (s v) ...) s_0)
        (rec-delete ((s v) ...) s_0))
   (==> (rec-del v_0 v_1)
        (throw "Bad record del")
        (side-condition (or (not (term (record? v_0)))
                            (not (term (string? v_1))))))   
   (==> (if true c_0 c_1) c_0)   
   (==> (if false c_0 c_1) c_1)   
   (==> (if v c_0 c_1)
        (throw "Not a boolean")
        (side-condition (not (term (boolean? v)))))
   (==> (begin v c) c)
   (==> (try/catch v x (clos e ρ)) v)
   (==> (try/finally v c) 
        (begin c v))
   (==> (label l v) v)   
   ;; Inlined the well-defined cases in order to make testing feasible.
   #;
   (==> (prim op v ...)
        (δ op v ...)
        (side-condition (term (in-δ-dom? op v ...))))
   (==> (prim + n_0 n_1)
        (δ + n_0 n_1))
   (==> (prim number->string n)
        (δ number->string n))
   (==> (prim op v ...)
        (throw "Bad primop")
        (side-condition (not (term (in-δ-dom? op v ...)))))
      
   ;; Context-sensitive, store-sensitive rules
   (--> (σ (in-hole 𝓔 (ref v)))
        ((sto-extend n v σ) (in-hole 𝓔 (addr n)))
        (where n (sto-alloc σ)))        
   (--> (σ (in-hole 𝓔 (deref (addr n))))
        (σ (in-hole 𝓔 (sto-lookup σ n)))
        (side-condition (term (in-sto-dom? σ n))))     
   (--> (σ (in-hole 𝓔 (deref (addr n))))
        (σ (in-hole 𝓔 (throw "Null pointer")))
        (side-condition (not (term (in-sto-dom? σ n)))))   
   (==> (deref v)
        (throw "Not an address")
        (side-condition (not (term (address? v)))))   
   (--> (σ (in-hole 𝓔 (set (addr n) v)))
        ((sto-update σ n v) (in-hole 𝓔 v))
        (side-condition (term (in-sto-dom? σ n))))   
   (--> (σ (in-hole 𝓔 (set (addr n) v)))
        (σ (in-hole 𝓔 (throw "Null pointer")))
        (side-condition (not (term (in-sto-dom? σ n)))))   
   (==> (set v_0 v_1)
        (throw "Not an address")
        (side-condition (not (term (address? v_0)))))
   (--> (σ (in-hole 𝓒 (throw v)))
        (err v σ))
   (==> (try/finally (in-hole 𝓒 (throw v)) c)
        (begin c (throw v)))
   (==> (try/catch (in-hole 𝓒 (throw v)) x (clos e ρ))
        (clos e (env-extend (x) (v) ρ)))   
   (==> (label l (in-hole 𝓒 (throw v)))
        (throw v))
   (--> (σ (in-hole 𝓒 (break l v)))
        (σ (in-hole 𝓒 (throw "Unlabeled break"))))
   (==> (try/finally (in-hole 𝓒 (break l v)) c)
        (begin c (break l v)))
   (==> (try/catch (in-hole 𝓒 (break l v)) x (clos e ρ))
        (break l v))
   (==> (label l (in-hole 𝓒 (break l v)))
        v)
   (==> (label l_0 (in-hole 𝓒 (break l_1 v)))
        (break l_1 v)
        (side-condition (not (equal? (term l_0) (term l_1)))))                      
   with
   [(--> (σ (in-hole 𝓔 c_0)) (σ (in-hole 𝓔 c_1)))
    (==> c_0 c_1)]))
  


(test--> λρJS-step
         (term (() (((func () 5) ()) 7)))
         (term (() (throw "Arity mismatch"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Property: for all closed states 𝓼, 
;; - 𝓼 -->* ans, or 
;; - 𝓼 -->* 𝓼' --> 𝓼'' -->* 𝓼'.

;; The above is obviously not a theorem because of the halting problem,
;; however it is highly unlikely that the test for the property will diverge.

(test
 (redex-check JS 𝓼
	      (match (apply-reduction-relation* λρJS-step (term 𝓼))
                [(list) #t] ;; the program loops               
                [(list r)   ;; the program produced an answer
                 (redex-match JS ans r)])
	      #:source λρJS-step
	      #:prepare (λ (𝓼) (term (seal-𝓼/0 ,𝓼)))))
