#lang racket
(require redex)
(require "js-lang.rkt" "js-test-common.rkt" "js-reduction.rkt" "js-machine.rkt" "unload.rkt")

;; Theorem [Correspondence]:
;; For all programs e, (() (e ())) --λρJS-step--> ans <==> (eval () e () D1 C1) --JAM--> ans
(redex-check JS e
             (equal? (apply-reduction-relation* λρJS-step (term (() (clos e ((close/0 e))))))
                     (apply-reduction-relation* JAM-step (term (eval () e ((close/0 e)) D1 C1)))))

;; This is the main lemma to prove that JAM => λρJS.

;; Lemma: For all well formed states ς, if ς --JAM--> ς'
;; then either (unload/ς ς) == (unload/ς ς'), 
;; or (unload/ς ς) --λρJS-step-->  (unload/ς ς').
(redex-check JS ς
             (match (apply-reduction-relation JAM-step (term ς))
               [(list r)
                (or (equal? (term (unload/ς ς))
                            (term (unload/ς ,r)))
                    (match (apply-reduction-relation λρJS-step (term (unload/ς ς)))
                      [(list r*) 
                       (equal? r* (term (unload/ς ,r)))]))])               
             #:source JAM-step
             #:prepare (λ (ς) (term (seal-ς/0 ,ς))))
