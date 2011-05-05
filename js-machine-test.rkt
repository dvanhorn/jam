#lang racket
(require "js-machine.rkt" "js-lang.rkt" "js-test-common.rkt")
(require redex) 

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
             #:prepare (λ (ς) (term (seal-ς/0 ,ς))))