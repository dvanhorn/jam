#lang racket
(require redex)
(provide (all-defined-out))

(define-language JS
  ;; JS
  (b true false)
  (q s n a b undefn null)
  (a (addr n))
  (s string)
  (l string)
  (n number)
  ((x y z) variable-not-otherwise-mentioned)
  (e q 
     x
     (e1 e)
     (e2 e e)
     (e3 e e e) 
     (func (x ...) e)
     (rec (s e) ...)
     (let (x e) e)
     (app e e ...)
     ;(rec-ref e e)
     ;(rec-set e e e)
     ;(rec-del e e)
     ;(set e e)    
     ;(ref e)
     ;(deref e)
     ;(if e e e)
     ;(begin e e)
     ;(while e e)
     (label l e)
     (break l e)
     (try/catch e x e)
     ;(try/finally e e)
     ;(throw e)
     (prim op e ...))
  
  (e1 ref deref throw)
  (e2 rec-ref rec-del set begin while try/finally)
  (e3 rec-set if)
  
  (f ((func (x ...) e) ρ))
  (r (rec (s v) ...))
  (v q f r)
  (ans (err v σ)
       (val v σ))
  
  (frame ((x v) ...))
  (ρ (frame ...))
  (σ ((n v) ...))
  (op + number->string)
  (pr (pr-app v (v ...))
      (pr-rec-ref v v)
      (pr-rec-set v v v)
      (pr-rec-del v v)
      (pr-if v e ρ e ρ)
      (pr-op op (v ...))
      (pr-set v v)
      (pr-deref v)
      (pr-throw v)
      (pr-break l v))
  
  ;; For syntactic reduction
  (𝓼 (σ c) ans)      
  (c q
     v
     (clos e ρ)
     (rec (s c) ...)
     (app c c ...)
     (let (x c) (clos e ρ))
     (rec-ref c c)
     (rec-set c c c)
     (rec-del c c)
     (set c c)
     (ref c)
     (deref c)
     (if c c c)
     (begin c c)
     ;(while c c)
     (label l c)
     (break l c)
     (try/catch c x (clos e ρ))
     (try/finally c c)
     (throw c)
     (prim op c ...))     
  (𝓒 hole
     (let (x 𝓒) (clos e ρ))
     ;(app 𝓒 c ...)
     (app v ... 𝓒 c ...)
     (rec (s v) ... (s 𝓒) (s c) ...)
     (rec-ref 𝓒 c)
     (rec-ref v 𝓒)
     (rec-set 𝓒 c c)
     (rec-set v 𝓒 c)
     (rec-set v v 𝓒)
     (rec-del 𝓒 c)
     (rec-del v 𝓒)
     (ref 𝓒)
     (deref 𝓒)
     (set 𝓒 c)
     (set v 𝓒)
     (if 𝓒 c c)
     (begin 𝓒 c)
     (throw 𝓒)
     (break l 𝓒)
     (prim op v ... 𝓒 c ...))
  (𝓓 hole
     (try/finally (in-hole 𝓒 𝓓) c)
     (try/catch (in-hole 𝓒 𝓓) x (clos e ρ))
     (label l (in-hole 𝓒 𝓓)))
  (𝓔 (in-hole 𝓒 𝓓))

  ;; JAM
  (C C1
     (C2 C x e ρ)
     (C3 C ((e ρ) ...))
     (C4 C v (v ...) ((e ρ) ...))
     (C5 C ((s v) ...) s ((s (e ρ)) ...))
     (C6 C e ρ)
     (C7 C v)
     (C8 C e e ρ)
     (C9 C v e ρ)
     (C10 C v v)
     (C11 C e ρ)
     (C12 C v)
     (C13 C)
     (C14 C)
     (C15 C e ρ)
     (C16 C v)
     (C17 C e ρ e ρ)
     (C18 C e ρ)
     (C19 C)
     (C20 C s)
     (C21 C op (v ...) ((e ρ) ...))
     (C22 C v)
     (C23 C v)
     (C24 C s v))
  (D D1
     (D2 D C e ρ)
     (D3 D C x e ρ)
     (D4 D C l))
  (maybe none some)  
  (ς (eval σ e ρ D C)
     (cont σ D C v)
     (appl σ D C pr)
     ans)
  
  
  ;; JAM*
  ;; This is all a boring copy/paste job in order to enforce the 
  ;; following invariant:
  (frame* ((x n) ...))  ;; <-- the imporant change
 
  ;; Other important change:
  (loc n (bind n) (cont n))
  (σ* ((loc v*) ...))
  
  (pr* (pr-app v* (v* ...))
       (pr-rec-ref v* v*)
       (pr-rec-set v* v* v*)
       (pr-rec-del v* v*)
       (pr-if v* e e ρ*)
       (pr-op op (v* ...))
       (pr-set v* v*)
       (pr-deref v*)
       (pr-throw v*)
       (pr-break l v*))
  
  ;; This needs to change from C* to n.
  (C* C1
     (C2 C* x e ρ*)
     (C3 C* ((e ρ*) ...))
     (C4 C* v* (v* ...) ((e ρ*) ...))
     (C5 C* ((s v*) ...) s ((s (e ρ*)) ...))
     (C6 C* e ρ*)
     (C7 C* v*)
     (C8 C* e e ρ*)
     (C9 C* v* e ρ*)
     (C10 C* v* v*)
     (C11 C* e ρ*)
     (C12 C* v*)
     (C13 C*)
     (C14 C*)
     (C15 C* e ρ*)
     (C16 C* v*)
     (C17 C* e e ρ*)
     (C18 C* e ρ*)
     (C19 C*)
     (C20 C* s)
     (C21 C* op (v* ...) ((e ρ*) ...))
     (C22 C* v*)
     (C23 C* v*)
     (C24 C* s v*))
  (D* D1
     (D2 D* C* e ρ*)
     (D3 D* C* x e ρ*)
     (D4 D* C* l))
  (f* ((func (x ...) e) ρ*))
  (r* (rec (s v*) ...))
  (v* q f* r*)
  (ans* (err v* σ*)
        (val v* σ*))  
  (ρ* (frame* ...))  
  (ς* (eval σ* e ρ* D* C*)
      (cont σ* D* C* v*)
      (appl σ* D* C* pr*)
      ans*)
  )
  

(define-metafunction JS
  env-extend : (x ...) (v ...) ρ -> ρ
  [(env-extend (x ...) (v ...) (frame ...))
   (((x v) ...) frame ...)])

(define-metafunction JS
  env-lookup : x ρ -> v
  [(env-lookup x (((x_0 v_0) ... (x v) (x_1 v_1) ...) frame ...)) v]
  [(env-lookup x (frame_0 frame_1 ...))
   (env-lookup x (frame_1 ...))])

(define-metafunction JS
  sto-alloc : σ -> n
  [(sto-alloc ()) 0]
  [(sto-alloc ((n v) ...))   
   ,(add1 (apply max (term (n ...))))])

(define-metafunction JS
  sto-extend : n v σ -> σ
  [(sto-extend n v ((n_0 v_0) ...))
   ((n v) (n_0 v_0) ...)])

(define-metafunction JS
  in-sto-dom? : σ n -> #t or #f
  [(in-sto-dom? ((n_0 v_0) ... (n v) (n_1 v_1) ...) n) #t]
  [(in-sto-dom? σ n) #f])

(define-metafunction JS
  sto-lookup : σ n -> v
  [(sto-lookup ((n_0 v_0) ... (n v) (n_1 v_1) ...) n) v])

(define-metafunction JS
  function? : v -> #t or #f
  [(function? ((func (x ...) e) ρ)) #t]
  [(function? v) #f])

(define-metafunction JS
  record? : v -> #t or #f
  [(record? (rec (s v) ...)) #t]
  [(record? v) #f])

(define-metafunction JS
  string? : v -> #t or #f
  [(string? s) #t]
  [(string? v) #f])

(define-metafunction JS
  boolean? : v -> #t or #f
  [(boolean? true) #t]
  [(boolean? false) #t]
  [(boolean? v) #f])

(define-metafunction JS
  address? : v -> #t or #f
  [(address? (addr n)) #t]  
  [(address? v) #f])

(define-metafunction JS
  rec-lookup : ((s v) ...) s -> v
  [(rec-lookup () s) undefn]
  [(rec-lookup ((s v) (s_0 v_0) ...) s) v]
  [(rec-lookup ((s_0 v_0) (s_1 v_1) ...) s)
   (rec-lookup ((s_1 v_1) ...) s)])

(define-metafunction JS
  rec-update : ((s v) ...) s v -> v
  [(rec-update ((s_0 v_0) ... (s v_1) (s_2 v_2) ...) s v)
   (rec (s_0 v_0) ... (s v) (s_2 v_2) ...)]
  [(rec-update ((s v) ...) s_0 v_0)
   (rec (s_0 v_0) (s v) ...)])

(define-metafunction JS
  rec-delete : ((s v) ...) s -> v
  [(rec-delete ((s_0 v_0) ... (s v_1) (s_2 v_2) ...) s)
   (rec (s_0 v_0) ... (s_2 v_2) ...)]
  [(rec-delete ((s_0 v_0) ...) s)
   (rec (s_0 v_0) ...)])

(define-metafunction JS
  δ : op v ... -> v
  [(δ + n_0 n_1) ,(+ (term n_0) (term n_1))]
  [(δ number->string n) ,(number->string (term n))])

(define-metafunction JS
  in-δ-dom? : op v ... -> #t or #f
  [(in-δ-dom? + n_0 n_1) #t]
  [(in-δ-dom? number->string n) #t]
  [(in-δ-dom? op v ...) #f])

(define-metafunction JS
  sto-update : σ n v -> σ
  [(sto-update ((n_0 v_0) ... (n v_1) (n_2 v_2) ...) n v)
   ((n_0 v_0) ... (n v) (n_2 v_2) ...)])
