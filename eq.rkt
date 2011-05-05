#lang racket
(require redex/reduction-semantics)
(require "lang.rkt")

(define-metafunction JS
  direct : ς* -> ς
  [(direct (eval σ* e ρ* D* C*))
   (eval (direct-σ* σ*) (direct-e e σ*) (direct-ρ* ρ* σ*) (direct-D* D* σ*)  (direct-C* σ*))]
  [(direct any)
   (val 5 ())])

(define-metafunction JS
  [(kons any_0 any_1)
   ,(cons (term any_0) (term any_1))])

(define-metafunction JS
  direct-σ* : σ* -> σ
  [(direct-σ* ()) ()]
  [(direct-σ* (((cont n) v) (loc_0 v_0) ...))
   (direct-σ* ((loc_0 v_0) ...))]
  [(direct-σ* (((bind n) v) (loc_0 v_0) ...))
   (direct-σ* ((loc_0 v_0) ...))]
  [(direct-σ* ((n v) (loc_0 v_0) ...))
   (kons (n v) (direct-σ* ((loc_0 v_0) ...)))])

(redex-check JS σ*
             (term (direct-σ* σ*)))

(define-metafunction JS
  addrs : any -> any
  [(addrs (addr n))
   ,(set (term n))]
  [(addrs (any ...))
   ,(apply set-union (term ((addrs any) ...)))]
  [(addrs any) ,(set)])
  
(define-metafunction JS
  addr-subst : any n n -> any
  [(addr-subst (addr n_0) n_0 n_1)
   (addr n_1)]
  [(addr-subst (any ...) n_0 n_1)
   ((addr-subst any n_0 n_1) ...)]
  [(addr-subst any n_0 n_1) any])

(redex-check JS (ς n)
             (equal? (term ς) 
                     (term (addr-subst ς n n))))

(redex-check JS (e n)
             (equal? (term e) 
                     (term (addr-subst e n n))))

(redex-check JS (ρ n)
             (equal? (term ρ) 
                     (term (addr-subst ρ n n))))

(redex-check JS (v n)
             (equal? (term v) 
                     (term (addr-subst v n n))))
