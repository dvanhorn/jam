#lang racket
(require redex)
(require "js-lang.rkt")
(provide (all-defined-out))

(define-metafunction JS
  unload/ς : ς -> 𝓼
  [(unload/ς (eval σ e ρ D C)) 
   (σ (in-hole (unload/D D) (in-hole (unload/C C) (clos e ρ))))]
  [(unload/ς (cont σ D C v))   
   (σ (in-hole (unload/D D) (in-hole (unload/C C) v)))]
  [(unload/ς (appl σ D C pr))  
   (σ (in-hole (unload/D D) (in-hole (unload/C C) (unload/pr pr))))]
  [(unload/ς ans) ans])

(define-metafunction JS
  unload/pr : pr -> c
  [(unload/pr (pr-app v_0 (v_1 ...)))
   (app v_0 v_1 ...)]
  [(unload/pr (pr-rec-ref v_0 v_1))
   (rec-ref v_0 v_1)]
  [(unload/pr (pr-rec-set v_0 v_1 v_2))
   (rec-set v_0 v_1 v_2)]
  [(unload/pr (pr-rec-del v_0 v_1))
   (rec-del v_0 v_1)]
  [(unload/pr (pr-if v e_0 ρ_0 e_1 ρ_1))
   (if v (clos e_0 ρ_0) (clos e_1 ρ_1))]
  [(unload/pr (pr-op op (v ...)))
   (prim op v ...)]
  [(unload/pr (pr-set v_0 v_1))
   (set v_0 v_1)]
  [(unload/pr (pr-deref v))
   (deref v)]
  [(unload/pr (pr-throw v))
   (throw v)]
  [(unload/pr (pr-break l v))
   (break l v)])

(define-metafunction JS
  unload/C : C -> 𝓒
  [(unload/C C1) hole]
  [(unload/C (C2 C x e ρ))
   (in-hole (unload/C C) (let (x hole) (clos e ρ)))]
  [(unload/C (C3 C ((e ρ) ...)))
   (in-hole (unload/C C) (app hole (clos e ρ) ...))]
  [(unload/C (C4 C v_0 (v_1 ...) ((e ρ) ...)))
   (in-hole (unload/C C) (app v_0 v_1 ... hole (clos e ρ) ...))]
  [(unload/C (C5 C ((s_0 v) ...) s_1 ((s_2 (e ρ)) ...)))
   (in-hole (unload/C C) (rec (s_0 v) ... (s_1 hole) (s_2 (clos e ρ)) ...))]
  [(unload/C (C6 C e ρ))
   (in-hole (unload/C C) (rec-ref hole (clos e ρ)))]
  [(unload/C (C7 C v))
   (in-hole (unload/C C) (rec-ref v hole))]
  [(unload/C (C8 C e_0 e_1 ρ))
   (in-hole (unload/C C) (rec-set hole (clos e_0 ρ) (clos e_1 ρ)))]
  [(unload/C (C9 C v e ρ))
   (in-hole (unload/C C) (rec-set v hole (clos e ρ)))]
  [(unload/C (C10 C v_0 v_1))
   (in-hole (unload/C C) (rec-set v_0 v_1 hole))]
  [(unload/C (C11 C e ρ))
   (in-hole (unload/C C) (rec-del hole (clos e ρ)))]
  [(unload/C (C12 C v))
   (in-hole (unload/C C) (rec-del v hole))]
  [(unload/C (C13 C))
   (in-hole (unload/C C) (ref hole))]
  [(unload/C (C14 C))
   (in-hole (unload/C C) (deref hole))]
  [(unload/C (C15 C e ρ))
   (in-hole (unload/C C) (set hole (clos e ρ)))]
  [(unload/C (C16 C v))
   (in-hole (unload/C C) (set v hole))]
  [(unload/C (C17 C e_0 ρ_0 e_1 ρ_1))
   (in-hole (unload/C C) (if hole (clos e_0 ρ_0) (clos e_1 ρ_1)))]
  [(unload/C (C18 C e ρ))
   (in-hole (unload/C C) (begin hole (clos e ρ)))]
  [(unload/C (C19 C))
   (in-hole (unload/C C) (throw hole))]
  [(unload/C (C20 C l))
   (in-hole (unload/C C) (break l hole))]
  [(unload/C (C21 C op (v ...) ((e ρ) ...)))
   (in-hole (unload/C C) (prim op v ... hole (clos e ρ) ...))]
  [(unload/C (C22 C v))
   (in-hole (unload/C C) (begin hole v))]
  [(unload/C (C23 C v))
   (in-hole (unload/C C) (begin hole (throw v)))]
  [(unload/C (C24 C l v))
   (in-hole (unload/C C) (begin hole (break l v)))])

(define-metafunction JS
  unload/D : D -> 𝓔
  [(unload/D D1) hole]
  [(unload/D (D2 D C e ρ))
   (in-hole (unload/D D) 
            (in-hole (unload/C C) 
                     (try/finally hole (clos e ρ))))]
  [(unload/D (D3 D C x e ρ))
   (in-hole (unload/D D) 
            (in-hole (unload/C C) 
                     (try/catch hole x (clos e ρ))))]
  [(unload/D (D4 D C l))
   (in-hole (unload/D D) 
            (in-hole (unload/C C) 
                     (label l hole)))])

(redex-check JS ς (term (unload/ς ς)))

(test-equal (term (unload/ς (eval () q () D1 (C3 (C2 C1 x 1 ()) ()))))
            (term (() (let (x (app (clos q ()))) (clos 1 ())))))


  