#lang racket
(provide test-suite)
(require redex/reduction-semantics)

(define-syntax-rule (test-suite test suite)
  (begin (define test-thunk (box test-results))
	 (provide suite)
	 (define (suite) ((unbox test-thunk)))
	 (define-syntax-rule (test e (... ...))
	   (set-box! test-thunk
		     (let ((rest (unbox test-thunk)))
		       (lambda ()
			 e (... ...) (rest)))))))
