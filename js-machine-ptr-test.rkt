#lang racket
(require "js-machine-ptr.rkt" "js-lang.rkt" "js-test-common.rkt")
(require redex) 

(define-metafunction JS
  close/store : e -> (eval σ* e ρ* D1 C1)
  [(close/store e)
   ,(let ((fv (set->list (term (fv e)))))
      (term (eval ,(build-list (length fv) (λ (i) (list i 0)))
                  e
                  ,(list (map list fv (build-list (length fv) (λ (i) i))))
                  D1
                  C1)))])

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
                (redex-match JS ans r)]))






