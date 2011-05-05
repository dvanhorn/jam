#lang racket
(require redex)
(require "js-lang.rkt")
(provide (all-defined-out))

;; Helper metafunctions
(define-metafunction JS
  fv : e -> any
  [(fv q) ,(set)]
  [(fv x) ,(set (term x))]
  [(fv (func (x ...) e))
   ,(set-subtract (term (fv e))
                  (apply set (term (x ...))))]
  [(fv (rec (s e) ...))
   ,(apply set-union (set) (term ((fv e) ...)))]
  [(fv (let (x e_0) e_1))
   ,(set-union (term (fv e_0))
               (set-remove (term (fv e_1)) (term x)))]
  [(fv (app e_0 e_1 ...))
   ,(apply set-union (set) (term ((fv e_0) (fv e_1) ...)))]
  [(fv (e1 e)) (fv e)]
  [(fv (e2 e_0 e_1))
   ,(set-union (term (fv e_0))
               (term (fv e_1)))]
  [(fv (e3 e_0 e_1 e_2))
   ,(set-union (term (fv e_0))
               (term (fv e_1))
               (term (fv e_2)))]
  [(fv (label l e)) (fv e)]
  [(fv (break l e)) (fv e)]
  [(fv (try/catch e_0 x e_1))
   ,(set-union (term (fv e_0))
               (set-remove (term (fv e_1)) (term x)))]
  [(fv (prim op e ...))
   ,(apply set-union (set) (term ((fv e) ...)))])

(redex-check JS e (term (fv e)))
  
;; Metafunctions for cleaning up randomly generated programs.
(define-metafunction JS
  seal-v/0 : v -> v
  [(seal-v/0 q) q]
  [(seal-v/0 ((func (x ...) e) (frame ...)))
   ((func (x ...) e) (frame ... (close/0 (func (x ...) e))))]
  [(seal-v/0 (rec (s v) ...))
   (rec-unique (rec (s (seal-v/0 v)) ...))])

;; Close 𝓼 by mapping all free variables to 0, 
;; remove duplicate addresses in the store,
;; remove duplicate keys in records.
(define-metafunction JS
  seal-𝓼/0 : 𝓼 -> 𝓼
  [(seal-𝓼/0 (σ c))
   ((sto-unique σ) (seal-c/0 c))]
  [(seal-𝓼/0 ans)
   (seal-ans/0 ans)])

(define-metafunction JS
  seal-c/0 : c -> c
  [(seal-c/0 q) q]
  [(seal-c/0 v) (seal-v/0 v)]
  [(seal-c/0 (clos e (frame ...)))
   (clos e (frame ... (close/0 e)))]
  [(seal-c/0 (rec (s c) ...))
   (rec-unique (rec (s (seal-c/0 c)) ...))]
  [(seal-c/0 (app c_0 c_1 ...))
   (app (seal-c/0 c_0) (seal-c/0 c_1) ...)]
  [(seal-c/0 (let (x c) (clos e ρ)))
   (let (x (seal-c/0 c)) (seal-c/0 (clos e ρ)))]
  [(seal-c/0 (rec-ref c_0 c_1))
   (rec-ref (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (rec-set c_0 c_1 c_2))
   (rec-set (seal-c/0 c_0) (seal-c/0 c_1) (seal-c/0 c_2))]
  [(seal-c/0 (rec-del c_0 c_1))
   (rec-del (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (set c_0 c_1))
   (set (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (ref c))
   (ref (seal-c/0 c))]
  [(seal-c/0 (deref c))
   (deref (seal-c/0 c))]
  [(seal-c/0 (if c_0 c_1 c_2))
   (if (seal-c/0 c_0) (seal-c/0 c_1) (seal-c/0 c_2))]
  [(seal-c/0 (begin c_0 c_1))
   (begin (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (while c_0 c_1))
   (while (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (label l c))
   (label l (seal-c/0 c))]
  [(seal-c/0 (break l c))
   (break l (seal-c/0 c))]
  [(seal-c/0 (try/catch c x (clos e ρ)))
   (try/catch (seal-c/0 c) x (seal-c/0 (clos e ρ)))]
  [(seal-c/0 (try/finally c_0 c_1))
   (try/finally (seal-c/0 c_0) (seal-c/0 c_1))]
  [(seal-c/0 (throw c))
   (throw (seal-c/0 c))]
  [(seal-c/0 (prim op c ...))
   (prim op (seal-c/0 c) ...)])

(define-metafunction JS
  seal-ans/0 : ans -> ans
  [(seal-ans/0 (err v σ))
   (err (seal-v/0 v) (sto-unique σ))]
  [(seal-ans/0 (val v σ))
   (val (seal-v/0 v) (sto-unique σ))])

(define-metafunction JS
  seal-ς/0 : ς -> ς
  [(seal-ς/0 ans) (seal-ans/0 ans)]
  [(seal-ς/0 (eval σ e (frame ...) D C))
   (eval (sto-unique σ) e (frame ... (close/0 e)) (seal-D/0 D) (seal-C/0 C))]
  [(seal-ς/0 (cont σ D C v))
   (cont (sto-unique σ) (seal-D/0 D) (seal-C/0 C) (seal-v/0 v))]
  [(seal-ς/0 (appl σ D C pr))
   (appl (sto-unique σ) (seal-D/0 D) (seal-C/0 C) (seal-pr/0 pr))])

(define-metafunction JS
  seal-pr/0 : pr -> pr
  [(seal-pr/0 (pr-app v_0 (v_1 ...))) 
   (pr-app (seal-v/0 v_0) ((seal-v/0 v_1) ...))]
  [(seal-pr/0 (pr-rec-ref v_0 v_1)) 
   (pr-rec-ref (seal-v/0 v_0) (seal-v/0 v_1))]
  [(seal-pr/0 (pr-rec-set v_0 v_1 v_2)) 
   (pr-rec-set (seal-v/0 v_0) (seal-v/0 v_1) v_2)]
  [(seal-pr/0 (pr-rec-del v_0 v_1)) 
   (pr-rec-del (seal-v/0 v_0) (seal-v/0 v_1))]
  [(seal-pr/0 (pr-if v e_0 (frame_0 ...) e_1 (frame_1 ...)))
   (pr-if (seal-v/0 v) e_0 (frame_0 ... (close/0 e_0)) e_1 (frame_1 ... (close/0 e_1)))]
  [(seal-pr/0 (pr-op op (v ...))) 
   (pr-op op ((seal-v/0 v) ...))]
  [(seal-pr/0 (pr-set v_0 v_1)) 
   (pr-set (seal-v/0 v_0) (seal-v/0 v_1))]
  [(seal-pr/0 (pr-deref v)) 
   (pr-deref (seal-v/0 v))]
  [(seal-pr/0 (pr-throw v))
   (pr-throw (seal-v/0 v))]
  [(seal-pr/0 (pr-break l v)) 
   (pr-break l (seal-v/0 v))])

(define-metafunction JS
  seal-eρ/0 : e ρ -> (e ρ)
  [(seal-eρ/0 e (frame ...)) (e (frame ... (close/0 e)))])

(define-metafunction JS
  seal-C/0 : C -> C  
  [(seal-C/0 C1) C1]
  [(seal-C/0 (C2 C x e (frame ...))) 
   (C2 (seal-C/0 C) x e (frame ... (close/0 e)))]
  [(seal-C/0 (C3 C ((e ρ) ...))) 
   (C3 (seal-C/0 C) ((seal-eρ/0 e ρ) ...))] 
  [(seal-C/0 (C4 C v_0 (v_1 ...) ((e ρ) ...))) 
   (C4 (seal-C/0 C) (seal-v/0 v_0) ((seal-v/0 v_1) ...) ((seal-eρ/0 e ρ) ...))]
  [(seal-C/0 (C5 C ((s_0 v) ...) s_1 ((s_2 (e ρ)) ...))) 
   (C5 (seal-C/0 C) ((s_0 (seal-v/0 v)) ...) s_1 ((s_2 (seal-eρ/0 e ρ)) ...))]
  [(seal-C/0 (C6 C e (frame ...))) 
   (C6 (seal-C/0 C) e (frame ... (close/0 e)))]
  [(seal-C/0 (C7 C v)) 
   (C7 (seal-C/0 C) (seal-v/0 v))]
  [(seal-C/0 (C8 C e_0 e_1 (frame ...))) 
   (C8 (seal-C/0 C) e_0 e_1 (frame ... (close/0 e_0) (close/0 e_1)))]
  [(seal-C/0 (C9 C v e (frame ...))) 
   (C9 (seal-C/0 C) (seal-v/0 v) e (frame ... (close/0 e)))]
  [(seal-C/0 (C10 C v_0 v_1)) 
   (C10 (seal-C/0 C) (seal-v/0 v_0) (seal-v/0 v_1))]
  [(seal-C/0 (C11 C e (frame ...)))
   (C11 (seal-C/0 C) e (frame ... (close/0 e)))]
  [(seal-C/0 (C12 C v)) 
   (C12 (seal-C/0 C) (seal-v/0 v))]
  [(seal-C/0 (C13 C)) 
   (C13 (seal-C/0 C))]
  [(seal-C/0 (C14 C)) 
   (C14 (seal-C/0 C))]
  [(seal-C/0 (C15 C e (frame ...))) 
   (C15 (seal-C/0 C) e (frame ... (close/0 e)))]  
  [(seal-C/0 (C16 C v)) 
   (C16 (seal-C/0 C) (seal-v/0 v))]
  [(seal-C/0 (C17 C e_0 (frame_0 ...) e_1 (frame_1 ...))) 
   (C17 (seal-C/0 C) e_0 (frame_0 ... (close/0 e_0)) e_1 (frame_1 ... (close/0 e_1)))]
  [(seal-C/0 (C18 C e (frame ...))) 
   (C18 (seal-C/0 C) e (frame ... (close/0 e)))]
  [(seal-C/0 (C19 C)) 
   (C19 (seal-C/0 C))]
  [(seal-C/0 (C20 C s)) 
   (C20 (seal-C/0 C) s)]
  [(seal-C/0 (C21 C op (v ...) ((e ρ) ...))) 
   (C21 (seal-C/0 C) op ((seal-v/0 v) ...) ((seal-eρ/0 e ρ) ...))] 
  [(seal-C/0 (C22 C v)) 
   (C22 (seal-C/0 C) (seal-v/0 v))]
  [(seal-C/0 (C23 C v)) 
   (C23 (seal-C/0 C) (seal-v/0 v))]
  [(seal-C/0 (C24 C s v))
   (C24 (seal-C/0 C) s (seal-v/0 v))])
 
(define-metafunction JS
  seal-D/0 : D -> D
  [(seal-D/0 D1) D1]
  [(seal-D/0 (D2 D C e (frame ...)))
   (D2 (seal-D/0 D) (seal-C/0 C) e (frame ... (close/0 e)))]
  [(seal-D/0 (D3 D C x e (frame ...)))
   (D3 (seal-D/0 D) (seal-C/0 C) x e (frame ... (close/0 e)))]
  [(seal-D/0 (D4 D C l))
   (D4 (seal-D/0 D) (seal-C/0 C) l)])

(define-metafunction JS
  close/0 : e -> frame
  [(close/0 e) 
   ,(set-map (term (fv e)) 
             (λ (x) (list x 0)))])

(define-metafunction JS
  sto-unique : σ -> σ
  [(sto-unique σ)
   ,(remove-duplicates (term σ) 
                       (λ (x1 x2)
                         (= (first x1) (first x2))))])

(define-metafunction JS
  rec-unique : (rec (s any) ...) -> (rec (s any) ...)
  [(rec-unique (rec (s any) ...))
   (rec ,@(remove-duplicates (term ((s any) ...))
                             (λ (x1 x2)
                               (string=? (first x1) (first x2)))))])

(define (one-step? R s)
  (= 1 (length (apply-reduction-relation R s))))