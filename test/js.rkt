#lang racket
(require redex/reduction-semantics)
(require "../lang.rkt" 
	 "../js.rkt" 
	 "../util/test.rkt")

(test--> λρJS-step
         (term (() (((func () 5) ()) 7)))
         (term (() (throw "Arity mismatch"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Property: for all closed states 𝓼, 
;; - 𝓼 -->* ans, or 
;; - 𝓼 -->* 𝓼' --> 𝓼'' -->* 𝓼'.

;; The above is obviously not a theorem because of the halting problem,
;; however it is highly unlikely that the test for the property will diverge.

(redex-check JS 𝓼
             (match (apply-reduction-relation* λρJS-step (term 𝓼))
               [(list) #t] ;; the program loops               
               [(list r)   ;; the program produced an answer
                (redex-match JS ans r)])
             #:source λρJS-step
             #:prepare (λ (𝓼) (term (seal-𝓼/0 ,𝓼))))


