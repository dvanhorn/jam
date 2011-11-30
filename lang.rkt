#lang racket
(require redex/reduction-semantics)
(provide (all-defined-out))

(define-language JS
  ;; JS
  (B true false)
  (Q S N A B undefn null)
  (A (addr N))
  (S string)
  (L string)
  (N number)
  ((X Y Z) variable-not-otherwise-mentioned)
  (E Q 
     X
     (e1 E)
     (e2 E E)
     (e3 E E E) 
     (func (X ...) E)
     (rec (S E) ...)
     (let (X E) E)
     (app E E ...)
     (label L E)
     (break L E)
     (try/catch E X E)
     (prim OP E ...))
  
  (en e1 e2 e3)
  (e1 ref deref throw)
  (e2 rec-ref rec-del set begin while try/finally)
  (e3 rec-set if)
  
  (F (clos (func (X ...) E) ρ))
  (R (rec (S V) ...))  
  (V F R (clos Q ρ))
  (ANS (err V σ)
       (val V σ))
  
  (frame ((X V) ...))
  (ρ (frame ...))
  (σ ((N V) ...))
  (OP + string-+
      % - * / === ==
      < string-<
      & \| ^ ~ << >> >>>
      to-integer to-uint-32 to-int-32
      =
      typeof surface-typeof
      prim->number prim->string prim->bool
      has-own-prop?
      print-string
      str-contains str-startswith str-length str-split-regexp str-split-strexp
      regexp-quote regexp-match
      obj-iterate-has-next? obj-iterate-next obj-iterate-key
      obj-delete obj-can-delete?
      math-sin math-cos math-log math-exp math-abs math-pow
      prim?)
      
  (PR (clos X ρ)
      (app V V ...)
      (rec-ref V V)
      (rec-set V V V)
      (rec-del V V)
      (if V c c)
      (prim OP V ...)
      (set V V)
      (deref V)
      (throw V)
      (break L V))
  
  ;; State for syntactic reduction
  (𝓼 (σ c) ANS)
  
  ;; Closures
  (c V
     (clos E ρ)
     (rec (S c) ...)
     (app c c ...)
     (let (X c) (clos E ρ))
     (rec-ref c c)
     (rec-set c c c)
     (rec-del c c)
     (set c c)
     (ref c)
     (deref c)
     (if c c c)
     (begin c c)
     ;(while c c)
     (label L c)
     (break L c)
     (try/catch c X (clos E ρ))
     (try/finally c c)
     (throw c)
     (prim OP c ...))     
  
  ;; Evaluation contexts
  (𝓒 hole
     (let (X 𝓒) (clos E ρ))    
     (app V ... 𝓒 c ...)
     (rec (S V) ... (S 𝓒) (S c) ...)
     (rec-ref 𝓒 c)
     (rec-ref V 𝓒)
     (rec-set 𝓒 c c)
     (rec-set V 𝓒 c)
     (rec-set V V 𝓒)
     (rec-del 𝓒 c)
     (rec-del V 𝓒)
     (ref 𝓒)
     (deref 𝓒)
     (set 𝓒 c)
     (set V 𝓒)
     (if 𝓒 c c)
     (begin 𝓒 c)
     (throw 𝓒)
     (break L 𝓒)
     (prim OP V ... 𝓒 c ...))
  (𝓓 hole
     (try/finally (in-hole 𝓒 𝓓) c)
     (try/catch (in-hole 𝓒 𝓓) X (clos E ρ))
     (label L (in-hole 𝓒 𝓓)))
  (𝓔 (in-hole 𝓒 𝓓))

  ;; Continuations
  (k (CONT A))
  (C mt ; Just 𝓒 with inductive occurrences replaced with k.
     (let (X k) (clos E ρ))    
     (app V ... k c ...)
     (rec (S V) ... (S k) (S c) ...)
     (rec-ref k c)
     (rec-ref V k)
     (rec-set k c c)
     (rec-set V k c)
     (rec-set V V k)
     (rec-del k c)
     (rec-del V k)
     (ref k)
     (deref k)
     (set k c)
     (set V k)
     (if k c c)
     (begin k c)
     (throw k)
     (break L k)
     (prim OP V ... k c ...))
  (D mt
     (try/finally k c)
     (try/catch k X (clos E ρ))
     (label L k))
  
  
  
  (maybe none some)  
  (ς (co σ D C V)
     (ap σ D C PR)
     ANS)
  
  
  )

(define-metafunction JS
  sto : -> σ ;; FIXME extend for convenient sto notation.  Don't write literal stores.
  [(sto) ()])

(define-metafunction JS
  env : -> ρ ;; FIXME extend for convenient env notation.  Don't write literal environments.
  [(env) ()])

(define-metafunction JS
  env-extend : (X ...) (V ...) ρ -> ρ
  [(env-extend (X ...) (V ...) (frame ...))
   (((X V) ...) frame ...)])

(define-metafunction JS
  env-lookup : X ρ -> V
  [(env-lookup X (((X_0 V_0) ... (X V) (X_1 V_1) ...) frame ...)) V]
  [(env-lookup X (frame_0 frame_1 ...))
   (env-lookup X (frame_1 ...))])

(define-metafunction JS
  sto-alloc : σ -> N
  [(sto-alloc ()) 0]
  [(sto-alloc ((N V) ...))   
   ,(add1 (apply max (term (N ...))))])

(define-metafunction JS
  sto-extend : N V σ -> σ
  [(sto-extend N V ((N_0 V_0) ...))
   ((N V) (N_0 V_0) ...)])

(define-metafunction JS
  in-sto-dom? : σ N -> #t or #f
  [(in-sto-dom? ((N_0 V_0) ... (N V) (N_1 V_1) ...) N) #t]
  [(in-sto-dom? σ N) #f])

(define-metafunction JS
  sto-lookup : σ N -> V
  [(sto-lookup ((N_0 V_0) ... (N V) (N_1 V_1) ...) N) V])

(define-metafunction JS
  function? : V -> #t or #f
  [(function? ((func (X ...) E) ρ)) #t]
  [(function? V) #f])

(define-metafunction JS
  record? : V -> #t or #f
  [(record? (rec (S V) ...)) #t]
  [(record? V) #f])

(define-metafunction JS
  string? : V -> #t or #f
  [(string? S) #t]
  [(string? V) #f])

(define-metafunction JS
  boolean? : V -> #t or #f
  [(boolean? true) #t]
  [(boolean? false) #t]
  [(boolean? V) #f])

(define-metafunction JS
  address? : V -> #t or #f
  [(address? (addr N)) #t]  
  [(address? V) #f])

(define-metafunction JS
  rec-lookup : ((S V) ...) S -> V
  [(rec-lookup () S) undefn]
  [(rec-lookup ((S V) (S_0 V_0) ...) S) V]
  [(rec-lookup ((S_0 V_0) (S_1 V_1) ...) S)
   (rec-lookup ((S_1 V_1) ...) S)])

(define-metafunction JS
  rec-update : ((S V) ...) S V -> V
  [(rec-update ((S_0 V_0) ... (S V_1) (S_2 V_2) ...) S V)
   (rec (S_0 V_0) ... (S V) (S_2 V_2) ...)]
  [(rec-update ((S V) ...) S_0 V_0)
   (rec (S_0 V_0) (S V) ...)])

(define-metafunction JS
  rec-delete : ((S V) ...) S -> V
  [(rec-delete ((S_0 V_0) ... (S V_1) (S_2 V_2) ...) S)
   (rec (S_0 V_0) ... (S_2 V_2) ...)]
  [(rec-delete ((S_0 V_0) ...) S)
   (rec (S_0 V_0) ...)])

(define-metafunction JS
  sto-update : σ N V -> σ
  [(sto-update ((N_0 V_0) ... (N V_1) (N_2 V_2) ...) N V)
   ((N_0 V_0) ... (N V) (N_2 V_2) ...)])
