(*
   This is a systematic derivation of a CESK machine for
   \lambda\rho_JS, a calculus of explicit substitutions for JavaScript
   based on \lambda_JS by Guha, et al, using the "Refocusing in
   Reduction Semantics" approach of Danvy and Nielsen.  In particular,
   we follow Danvy's "From Reduction-based to Reduction-free
   Normalization" lecture notes from AFP'08.

   David Van Horn, March 2011
   Boston, Massachusetts

   Baby, baby, baby, bitch.  
   I'm better now, please fuck off.
*)

(* FIXME: Shouldn't do splitting in step 4.  Wait for inlining down the line. *)

(* Stores *)
structure Sto = struct 

(* type loc = int *)

type 'a sto = (int * 'a) list

fun max ([], i) 
    = i
  | max ((j, x) :: s, i)
    = max (s, if i<j then j else i)

fun alloc h = 1 + max (h, 0)

fun lookup (i, [])
    = NONE
  | lookup (i, (j, x) :: h)
    = if i=j then SOME x else lookup (i, h)

exception UPDATE_FAIL

fun update (i, [], v)
    = raise UPDATE_FAIL
  | update (i, (j, v0) :: h, v)
    = if i=j 
      then (j, v) :: h 
      else (j, v0) :: update (i, h, v)
end

(* Records *)
structure Rec = struct

fun contains ([], y) 
    = false
  | contains ((x,v)::ls, y) 
    = if x=y then true else contains (ls, y)

exception LOOKUPFAIL

fun lookup ([], y)
    = raise LOOKUPFAIL
  | lookup ((x,v)::ls, y) 
    = if x=y then v else lookup (ls, y)

exception UPDATEFAIL

fun update ([], y, v1) 
    = raise UPDATEFAIL
  | update ((x,v0)::ls, y, v1) 
    = if x=y 
      then (x,v1) :: ls 
      else (x,v0) :: update (ls, y, v1)

exception REMOVEFAIL

fun remove ([], y)
    = raise REMOVEFAIL
  | remove ((x, v) :: ls, y)
    = if x=y then ls else remove (ls, y)

end

(* Environments *)
structure Env = struct 

type 'a env = (string * 'a) list list

val empty = []

exception ZIPFAIL

fun zip ([], []) = []
  | zip (x::xs, y::ys)
    = (x,y) :: zip (xs, ys)
  | zip (_, _) 
    = raise ZIPFAIL

fun extend (xs, vs, env) 
  = zip (xs, vs) :: env

fun lookup_frame (x, frame)
  = let fun search []
          = NONE
          | search ((x',v) :: frame)
            = if x = x' then SOME v else search frame
    in search frame
    end

exception UNBOUND_VARIABLE

fun lookup (x, env)
  = let fun search []
          = raise UNBOUND_VARIABLE
          | search (frame :: env)
            = (case lookup_frame (x, frame) 
                of NONE 
                   => search env
                 | SOME v
                   => v)
    in search env 
    end
end    

datatype term = VAR of string
              | STR of string
	      | NUM of int
	      | ADDR of int
              | BOOL of bool
              | UNDEFN
              | NULL
              | FUNC of string list * term
              | REC of (string * term) list
              | LET of string * term * term
              | APP of term * term list
              | REC_REF of term * term
              | REC_SET of term * term * term
              | REC_DEL of term * term
	      | SET of term * term
	      | REF of term
	      | DEREF of term
	      | IF of term * term * term
	      | SEQ of term * term
	      (* mutation *)
	      | SET of term * term
	      | REF of term
	      | DEREF of term
	      (* control *)
           (* | IF of term * term * term
	      | SEQ of term * term
	      | WHILE of term * term
	      | LAB of string * term
	      | BRK of string * term
	      | TRYC of term * string * term
	      | TRYF of term * term
	      | ERR of term  (* should be a syntactic value *)
	      | THROW of term *)

datatype closure = CLO_NUM of int
                 | CLO_STR of string
                 | CLO_BOOL of bool
                 | CLO_UNDEFN
                 | CLO_NULL
                 | CLO_GND of term * bindings
                 | CLO_APP of closure * closure list
                 | CLO_LET of string * closure * term * bindings
                 | CLO_REC of (string * closure) list
                 | CLO_REC_REF of closure * closure
                 | CLO_REC_SET of closure * closure * closure
                 | CLO_REC_DEL of closure * closure
		 (* mutation *)
		 | CLO_LOC of loc
		 | CLO_SET of closure * closure
		 | CLO_REF of closure
		 | CLO_DEREF of closure
		 (* control *)
              (* | CLO_IF of closure * closure * closure
		 | CLO_SEQ of closure * closure
		 | CLO_WHILE of closure * closure
		 | CLO_LAB of string * closure
		 | CLO_BRK of string * closure
		 | CLO_TRYC of closure * string * closure
		 | CLO_TRYF of closure * closure
		 | CLO_ERR of closure (* should be a syntactic value *)
		 | CLO_THROW of closure *)

     and value = VAL_NUM of int
               | VAL_STR of string
               | VAL_BOOL of bool
               | VAL_UNDEFN 
               | VAL_NULL
               | VAL_FUNC of string list * term * bindings
               | VAL_REC of (string * value) list
	       (* mutation *)
	       | VAL_LOC of loc

withtype bindings = value Env.env
     and loc = int
     and sto = value Sto.sto 

val initial_bindings = Env.empty

fun embed_value_in_closure ((VAL_NUM n) : value) : closure
    = CLO_NUM n
  | embed_value_in_closure (VAL_STR s)
    = CLO_STR s
  | embed_value_in_closure (VAL_BOOL b)
    = CLO_BOOL b
  | embed_value_in_closure VAL_UNDEFN
    = CLO_UNDEFN
  | embed_value_in_closure VAL_NULL
    = CLO_NULL
  | embed_value_in_closure (VAL_FUNC (xs, t, bs))
    = CLO_GND (FUNC (xs, t), bs)
  | embed_value_in_closure (VAL_REC flds)
    = CLO_REC (map (fn (s, c) => (s, embed_value_in_closure c)) flds)

  (* mutation *)
  | embed_value_in_closure (VAL_LOC i)
    = CLO_LOC i

datatype potential_redex = PR_VAR of string * bindings 
                         | PR_APP of value * (value list)
                         | PR_LET of string * value * term * bindings
                         | PR_REC_REF of value * value
                         | PR_REC_SET of value * value * value
                         | PR_REC_DEL of value * value
                         | PR_PROP_APP of term * term list * bindings
                         | PR_PROP_REC of (string * term) list * bindings
                         | PR_PROP_LET of string * term * term * bindings
                         | PR_PROP_REC_REF of term * term * bindings
                         | PR_PROP_REC_SET of term * term * term * bindings
                         | PR_PROP_REC_DEL of term * term * bindings
			 (* mutation *)
			 | PR_REF of value
			 | PR_DEREF of value
			 | PR_SET of value * value
			 | PR_PROP_SET of term * term * bindings
			 | PR_PROP_REF of term * bindings
			 | PR_PROP_DEREF of term * bindings

datatype contractum_or_error = CONTRACTUM of closure * sto 
                             | ERROR of string

fun contract ((PR_VAR (x, bs), h) : potential_redex * sto) : contractum_or_error
    = CONTRACTUM (embed_value_in_closure (Env.lookup (x, bs)), h)
  | contract (PR_APP (VAL_FUNC (xs, t, bs), vs), h)
    = if length xs = length vs 
      then CONTRACTUM (CLO_GND (t, Env.extend (xs, vs, bs)), h)
      else ERROR "Arity mismatch"
  | contract (PR_APP (v, vs), h)
    = ERROR "Stuck"
  | contract (PR_LET (x, v, t, bs), h)
    = CONTRACTUM (CLO_GND (t, Env.extend ([x], [v], bs)), h)
  | contract (PR_REC_REF (VAL_REC flds, VAL_STR s), h)
    = CONTRACTUM (if Rec.contains (flds, s) 
                  then (embed_value_in_closure (Rec.lookup (flds, s)))
                  else CLO_UNDEFN, 
		  h)
  | contract (PR_REC_REF (v0, v1), h)
    = ERROR "Stuck"
  | contract (PR_REC_SET (VAL_REC flds, VAL_STR s, v), h)
    = CONTRACTUM (embed_value_in_closure 
                      (VAL_REC (if Rec.contains (flds, s)
                                then (Rec.update (flds, s, v))
                                else ((s, v) :: flds))), 
		  h)
  | contract (PR_REC_SET (v0, v1, v2), h)
    = ERROR "Stuck"
  | contract (PR_REC_DEL (VAL_REC flds, VAL_STR s), h)
    = CONTRACTUM (embed_value_in_closure
                      (VAL_REC (if Rec.contains (flds, s)
                                then (Rec.remove (flds, s))
                                else flds)), 
		  h)
  | contract (PR_REC_DEL (v0, v1), h)
    = ERROR "Stuck"
  | contract (PR_PROP_APP (t, ts, bs), h)
    = CONTRACTUM (CLO_APP (CLO_GND (t, bs), 
                           map (fn t => CLO_GND (t, bs)) ts), 
		  h)
  | contract (PR_PROP_REC (flds, bs), h)
    = CONTRACTUM (CLO_REC (map (fn (s, t) => (s, CLO_GND (t, bs))) flds), h)
  | contract (PR_PROP_LET (x, t0, t1, bs), h)
    = CONTRACTUM (CLO_LET (x, CLO_GND (t0, bs), t1, bs), h)
  | contract (PR_PROP_REC_REF (t0, t1, bs), h)
    = CONTRACTUM (CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)), h)
  | contract (PR_PROP_REC_SET (t0, t1, t2, bs), h)
    = CONTRACTUM (CLO_REC_SET (CLO_GND (t0, bs), 
                           CLO_GND (t1, bs), 
                           CLO_GND (t2, bs)), 
		  h)
  | contract (PR_PROP_REC_DEL (t0, t1, bs), h)
    = CONTRACTUM (CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)), h)
  (* mutation *)
  | contract (PR_REF v, h) 
    = let val i = Sto.alloc h in
	  (CONTRACTUM (CLO_LOC i, ((i, v) :: h)))
      end
  | contract (PR_DEREF (VAL_LOC i), h)
    = (case Sto.lookup (i, h)
	of NONE
	   => ERROR "deref"
	 | SOME v
	   => CONTRACTUM (embed_value_in_closure v, h))
  | contract (PR_DEREF v, h)
    = ERROR "Stuck"
  | contract (PR_SET (VAL_LOC i, v), h)
    = CONTRACTUM (embed_value_in_closure v, Sto.update (i, h, v))
  | contract (PR_SET (v0, v1), h)
    = ERROR "Stuck"
  | contract (PR_PROP_SET (t0, t1, bs), h)
    = CONTRACTUM (CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), h)
  | contract (PR_PROP_REF (t, bs), h)
    = CONTRACTUM (CLO_REF (CLO_GND (t, bs)), h)
  | contract (PR_PROP_DEREF (t, bs), h)
    = CONTRACTUM (CLO_DEREF (CLO_GND (t, bs)), h)

datatype context = CTX_1
                 | CTX_2 of string * context * term * bindings
                 | CTX_3 of context * closure list
                 | CTX_4 of value * value list * context * closure list
                 | CTX_5 of (string * value) list *
                            string * context *
                            (string * closure) list
                 | CTX_6 of context * closure
                 | CTX_7 of value * context
                 | CTX_8 of context * closure * closure
                 | CTX_9 of value * context * closure
                 | CTX_10 of value * value * context
                 | CTX_11 of context * closure
                 | CTX_12 of value * context
		 (* mutation *)
		 | CTX_13 of context * closure
		 | CTX_14 of value * context
		 | CTX_15 of context
		 | CTX_16 of context

datatype value_or_decomposition = VAL of value 
                                | DEC of potential_redex * context

fun decompose_closure ((CLO_NUM n, C) : closure * context) : value_or_decomposition
    = decompose_context (C, VAL_NUM n)
  | decompose_closure (CLO_STR s, C)
    = decompose_context (C, VAL_STR s)
  | decompose_closure (CLO_BOOL b, C)
    = decompose_context (C, VAL_BOOL b)
  | decompose_closure (CLO_UNDEFN, C)
    = decompose_context (C, VAL_UNDEFN)
  | decompose_closure (CLO_NULL, C)
    = decompose_context (C, VAL_NULL)
  | decompose_closure (CLO_GND (NUM n, bs), C)
    = decompose_context (C, VAL_NUM n)
  | decompose_closure (CLO_GND (STR s, bs), C)
    = decompose_context (C, VAL_STR s)
  | decompose_closure (CLO_GND (BOOL b, bs), C)
    = decompose_context (C, VAL_BOOL b)
  | decompose_closure (CLO_GND (UNDEFN, bs), C)
    = decompose_context (C, VAL_UNDEFN)
  | decompose_closure (CLO_GND (NULL, bs), C)
    = decompose_context (C, VAL_NULL)
  | decompose_closure (CLO_GND (FUNC (xs, t), bs), C)
    = decompose_context (C, VAL_FUNC (xs, t, bs))
  | decompose_closure (CLO_GND (VAR x, bs), C)
    = DEC (PR_VAR (x, bs), C)
  | decompose_closure (CLO_GND (LET (x, t0, t1), bs), C)
    = DEC (PR_PROP_LET (x, t0, t1, bs), C)
  | decompose_closure (CLO_GND (APP (t, ts), bs), C)
    = DEC (PR_PROP_APP (t, ts, bs), C)
  | decompose_closure (CLO_GND (REC_REF (t0, t1), bs), C)
    = DEC (PR_PROP_REC_REF (t0, t1, bs), C)
  | decompose_closure (CLO_GND (REC_SET (t0, t1, t2), bs), C)
    = DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C)
  | decompose_closure (CLO_GND (REC_DEL (t0, t1), bs), C)
    = DEC (PR_PROP_REC_DEL (t0, t1, bs), C)
  | decompose_closure (CLO_GND (REC flds, bs), C)
    = DEC (PR_PROP_REC (flds, bs), C)
  | decompose_closure (CLO_APP (c, cs), C)
    = decompose_closure (c, CTX_3 (C, cs))
  | decompose_closure (CLO_LET (x, c, t, bs), C)
    = decompose_closure (c, CTX_2 (x, C, t, bs))
  | decompose_closure (CLO_REC [], C)
    = decompose_context (C, VAL_REC [])
  | decompose_closure (CLO_REC ((s, c) :: cs), C)
    = decompose_closure (c, CTX_5 ([], s, C, cs))
  | decompose_closure (CLO_REC_REF (c0, c1), C)
    = decompose_closure (c0, CTX_6 (C, c1))
  | decompose_closure (CLO_REC_SET (c0, c1, c2), C)
    = decompose_closure (c0, CTX_8 (C, c1, c2))
  | decompose_closure (CLO_REC_DEL (c0, c1), C)
    = decompose_closure (c0, CTX_11 (C, c1))      
  (* mutation *)     
  | decompose_closure (CLO_GND (SET (t0, t1), bs), C)
    = DEC (PR_PROP_SET (t0, t1, bs), C)
  | decompose_closure (CLO_GND (REF t, bs), C)
    = DEC (PR_PROP_REF (t, bs), C)
  | decompose_closure (CLO_GND (DEREF t, bs), C)
    = DEC (PR_PROP_DEREF (t, bs), C)
  | decompose_closure (CLO_LOC i, C)
    = decompose_context (C, VAL_LOC i)
  | decompose_closure (CLO_SET (c0, c1), C)
    = decompose_closure (c0, CTX_13 (C, c1))
  | decompose_closure (CLO_REF c, C)
    = decompose_closure (c, CTX_15 C)
  | decompose_closure (CLO_DEREF c, C)
    = decompose_closure (c, CTX_16 C)

and decompose_context ((CTX_1, v) : context * value) : value_or_decomposition
    = VAL v
  | decompose_context (CTX_2 (x, C, t, bs), v)
    = DEC (PR_LET (x, v, t, bs), C)
  | decompose_context (CTX_3 (C, []), v)
    = DEC (PR_APP (v, []), C)
  | decompose_context (CTX_3 (C, c :: cs), v)
    = decompose_closure (c, (CTX_4 (v, [], C, cs)))
  | decompose_context (CTX_4 (v0, vs, C, []), v)
    = DEC (PR_APP (v0, vs @ [v]), C)
  | decompose_context (CTX_4 (v0, vs, C, c :: cs), v)
    = decompose_closure (c, CTX_4 (v0, vs @ [v], C, cs))
  | decompose_context (CTX_5 (vflds, s, C, []), v)
    = decompose_context (C, VAL_REC (vflds @ [(s, v)]))
  | decompose_context (CTX_5 (vflds, s, C, (s0, c0) :: cs), v)
    = decompose_closure (c0, CTX_5 (vflds @ [(s, v)], s0, C, cs))
  | decompose_context (CTX_6 (C, c), v)
    = decompose_closure (c, CTX_7 (v, C))
  | decompose_context (CTX_7 (v0, C), v)
    = DEC (PR_REC_REF (v0, v), C)
  | decompose_context (CTX_8 (C, c0, c1), v)
    = decompose_closure (c0, CTX_9 (v, C, c1))
  | decompose_context (CTX_9 (v0, C, c), v)
    = decompose_closure (c, CTX_10 (v0, v, C))
  | decompose_context (CTX_10 (v0, v1, C), v)
    = DEC (PR_REC_SET (v0, v1, v), C)
  | decompose_context (CTX_11 (C, c), v)
    = decompose_closure (c, CTX_12 (v, C))
  | decompose_context (CTX_12 (v0, C), v)
    = DEC (PR_REC_DEL (v0, v), C)
  (* mutation *)
  | decompose_context (CTX_13 (C, c), v)
    = decompose_closure (c, CTX_14 (v, C))
  | decompose_context (CTX_14 (v0, C), v)
    = DEC (PR_SET (v0, v), C)
  | decompose_context (CTX_15 C, v)
    = DEC (PR_REF v, C)
  | decompose_context (CTX_16 C, v)
    = DEC (PR_DEREF v, C)

fun decompose (c : closure) : value_or_decomposition
    = decompose_closure (c, CTX_1)

fun recompose ((CTX_1, c) : context * closure) : closure
    = c
  | recompose (CTX_2 (x, C, t, bs), c)
    = recompose (C, CLO_LET (x, c, t, bs))
  | recompose (CTX_3 (C, cs), c)
    = recompose (C, CLO_APP (c, cs))
  | recompose (CTX_4 (v, vs, C, cs), c)
    = recompose (C, (CLO_APP ((embed_value_in_closure v), 
                              (map embed_value_in_closure vs) @ [c] @ cs)))
  | recompose (CTX_5 (svs, s, C, scs), c)
    = recompose (C, CLO_REC ((map (fn (s, v) => (s, embed_value_in_closure v))
                                  svs)
                             @ [(s, c)]
                             @ scs)) 
  | recompose (CTX_6 (C, c0), c)
    = recompose (C, CLO_REC_REF (c, c0))
  | recompose (CTX_7 (v, C), c)
    = recompose (C, CLO_REC_REF (embed_value_in_closure v, c))
  | recompose (CTX_8 (C, c0, c1), c)
    = recompose (C, CLO_REC_SET (c, c0, c1))
  | recompose (CTX_9 (v, C, c0), c)
    = recompose (C, CLO_REC_SET (embed_value_in_closure v, c, c0))
  | recompose (CTX_10 (v0, v1, C), c)
    = recompose (C, CLO_REC_SET (embed_value_in_closure v0, 
                             embed_value_in_closure v1, c))
  | recompose (CTX_11 (C, c0), c)
    = recompose (C, CLO_REC_DEL (c, c0))
  | recompose (CTX_12 (v, C), c)
    = recompose (C, CLO_REC_DEL (embed_value_in_closure v, c))
  (* mutation *)
  | recompose (CTX_13 (C, c0), c)
    = recompose (C, CLO_SET (c, c0))
  | recompose (CTX_14 (v, C), c)
    = recompose (C, CLO_SET (embed_value_in_closure v, c))
  | recompose (CTX_15 C, c)
    = recompose (C, CLO_REF c)
  | recompose (CTX_16 C, c)
    = recompose (C, CLO_DEREF c)

datatype reduct = REDUCT of closure * sto
                | STUCK of string

fun reduce ((c, h) : closure * sto) : reduct
    = (case decompose c
        of (VAL v)
           => REDUCT (embed_value_in_closure v, h)
         | (DEC (pr, C))
           => (case contract (pr, h)
                of (CONTRACTUM (c', h')) 
                   => REDUCT (recompose (C, c'), h')
                 | (ERROR s) 
                   => STUCK s))
      
datatype result = RESULT of value * sto
                | WRONG of string

fun iterate0 ((VAL v, h) : value_or_decomposition * sto) : result
    = RESULT (v, h)
  | iterate0 (DEC (pr, C), h)
    = (case contract (pr, h)
        of (CONTRACTUM (c', h')) 
           => iterate0 (decompose (recompose (C, c')), h')
         | (ERROR s) 
           => WRONG s)

fun normalize0 (t : term) : result
    = iterate0 (decompose (CLO_GND (t, initial_bindings)), [])

fun normalize0' (t : term) : result
    = iterate0 (decompose (recompose (CTX_1, (CLO_GND (t, initial_bindings)))), [])

(* ************************************************************************** *)

fun refocus ((c, C) : closure * context) : value_or_decomposition
    = decompose_closure (c, C)

fun iterate1 ((VAL v, h) : value_or_decomposition * sto) : result
    = RESULT (v, h)
  | iterate1 (DEC (pr, C), h)
    = (case contract (pr, h)
        of (CONTRACTUM (c', h'))
           => iterate1 (refocus (c', C), h') 
         | (ERROR s)
           => WRONG s)

fun normalize1 (t : term) : result
    = iterate1 (refocus (CLO_GND (t, initial_bindings), CTX_1), [])

(* ************************************************************************** *)

fun iterate2 ((VAL v, h) : value_or_decomposition * sto) : result
    = RESULT (v, h)
  | iterate2 (DEC (PR_VAR (x, bs), C), h)
    = iterate2 (refocus (embed_value_in_closure (Env.lookup (x, bs)), C), h)
  | iterate2 (DEC (PR_APP (VAL_FUNC (xs, t, bs), vs), C), h)
    = if length xs = length vs 
      then iterate2 (refocus (CLO_GND (t, Env.extend (xs, vs, bs)), C), h)
      else WRONG "Arity mismatch"
  | iterate2 (DEC (PR_APP (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate2 (DEC (PR_LET (x, v, t, bs), C), h)
    = iterate2 (refocus (CLO_GND (t, Env.extend ([x], [v], bs)), C), h)
  | iterate2 (DEC (PR_REC_REF (VAL_REC flds, VAL_STR s), C), h)
    = iterate2 (refocus ((if Rec.contains (flds, s)
                          then (embed_value_in_closure (Rec.lookup (flds, s)))
                          else CLO_UNDEFN), 
                         C), h)
  | iterate2 (DEC (PR_REC_REF (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate2 (DEC (PR_REC_SET (VAL_REC flds, VAL_STR s, v), C), h)
    = iterate2 (refocus (embed_value_in_closure
                             (VAL_REC (if Rec.contains (flds, s)
                                       then (Rec.update (flds, s, v))
                                       else ((s, v) :: flds))),
                         C), h)
  | iterate2 (DEC (PR_REC_SET (v0, v1, v2), C), h)
    = WRONG "Stuck"
  | iterate2 (DEC (PR_REC_DEL (VAL_REC flds, VAL_STR s), C), h)
    = iterate2 (refocus (embed_value_in_closure
                             (VAL_REC (if Rec.contains (flds, s)
                                       then (Rec.remove (flds, s))
                                       else flds)),
                         C), h)
  | iterate2 (DEC (PR_REC_DEL (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate2 (DEC (PR_PROP_APP (t, ts, bs), C), h)
    = iterate2 (refocus (CLO_APP (CLO_GND (t, bs),
                                 map (fn t => (CLO_GND (t, bs))) ts),
                        C), h)
  | iterate2 (DEC (PR_PROP_REC (sts, bs), C), h)
    = iterate2 (refocus (CLO_REC (map (fn (s, t) => 
                                          (s, CLO_GND (t, bs))) sts), C), h)
  | iterate2 (DEC (PR_PROP_LET (x, t0, t1, bs), C), h)
    = iterate2 (refocus (CLO_LET (x, CLO_GND (t0, bs), t1, bs), C), h)
  | iterate2 (DEC (PR_PROP_REC_REF (t0, t1, bs), C), h)
    = iterate2 (refocus (CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)), C), h)
  | iterate2 (DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C), h)
    = iterate2 (refocus (CLO_REC_SET (CLO_GND (t0, bs), 
                                  CLO_GND (t1, bs), 
                                  CLO_GND (t2, bs)), C), h)
  |iterate2 (DEC (PR_PROP_REC_DEL (t0, t1, bs), C), h)
    = iterate2 (refocus (CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)), C), h)
  (* mutation *)
  | iterate2 (DEC (PR_REF v, C), h)
    = let val i = Sto.alloc h in
	  iterate2 (refocus (CLO_LOC i, C), ((i, v) :: h))
      end
  | iterate2 (DEC (PR_DEREF (VAL_LOC i), C), h)
    = (case Sto.lookup (i, h)
	of NONE
	   => WRONG "deref"
	 | SOME v
	   => iterate2 (refocus (embed_value_in_closure v, C), h))
  | iterate2 (DEC (PR_DEREF v, C), h)
    = WRONG "Store"
  | iterate2 (DEC (PR_SET (VAL_LOC i, v), C), h)
    = iterate2 (refocus (embed_value_in_closure v, C), Sto.update (i, h, v))
  | iterate2 (DEC (PR_SET (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate2 (DEC (PR_PROP_SET (t0, t1, bs), C), h)
    = iterate2 (refocus (CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), C), h)
  | iterate2 (DEC (PR_PROP_REF (t, bs), C), h)
    = iterate2 (refocus (CLO_REF (CLO_GND (t, bs)), C), h)
  | iterate2 (DEC (PR_PROP_DEREF (t, bs), C), h)
    = iterate2 (refocus (CLO_DEREF (CLO_GND (t, bs)), C), h)

fun normalize2 (t : term) : result
    = iterate2 (refocus (CLO_GND (t, initial_bindings), CTX_1), [])

(* ************************************************************************** *)

fun refocus3_closure ((CLO_NUM n, C, h) : closure * context * sto) : result
    = refocus3_context (C, VAL_NUM n, h)
  | refocus3_closure (CLO_STR s, C, h)
    = refocus3_context (C, VAL_STR s, h)
  | refocus3_closure (CLO_BOOL b, C, h)
    = refocus3_context (C, VAL_BOOL b, h)
  | refocus3_closure (CLO_UNDEFN, C, h)
    = refocus3_context (C, VAL_UNDEFN, h)
  | refocus3_closure (CLO_NULL, C, h)
    = refocus3_context (C, VAL_NULL, h)
  | refocus3_closure (CLO_GND (NUM n, bs), C, h)
    = refocus3_context (C, VAL_NUM n, h)
  | refocus3_closure (CLO_GND (STR s, bs), C, h)
    = refocus3_context (C, VAL_STR s, h)
  | refocus3_closure (CLO_GND (BOOL b, bs), C, h)
    = refocus3_context (C, VAL_BOOL b, h)
  | refocus3_closure (CLO_GND (UNDEFN, bs), C, h)
    = refocus3_context (C, VAL_UNDEFN, h)
  | refocus3_closure (CLO_GND (NULL, bs), C, h)
    = refocus3_context (C, VAL_NULL, h)
  | refocus3_closure (CLO_GND (FUNC (xs, t), bs), C, h)
    = refocus3_context (C, VAL_FUNC (xs, t, bs), h)
  | refocus3_closure (CLO_GND (VAR x, bs), C, h)
    = iterate3 (DEC (PR_VAR (x, bs), C), h)
  | refocus3_closure (CLO_GND (LET (x, t0, t1), bs), C, h)
    = iterate3 (DEC (PR_PROP_LET (x, t0, t1, bs), C), h) 
  | refocus3_closure (CLO_GND (APP (t, ts), bs), C, h)
    = iterate3 (DEC (PR_PROP_APP (t, ts, bs), C), h)
  | refocus3_closure (CLO_GND (REC flds, bs), C, h)
    = iterate3 (DEC (PR_PROP_REC (flds, bs), C), h)
  | refocus3_closure (CLO_GND (REC_REF (t0, t1), bs), C, h)
    = iterate3 (DEC (PR_PROP_REC_REF (t0, t1, bs), C), h)
  | refocus3_closure (CLO_GND (REC_SET (t0, t1, t2), bs), C, h)
    = iterate3 (DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C), h)
  | refocus3_closure (CLO_GND (REC_DEL (t0, t1), bs), C, h)
    = iterate3 (DEC (PR_PROP_REC_DEL (t0, t1, bs), C), h)
  | refocus3_closure (CLO_APP (c, cs), C, h)
    = refocus3_closure (c, CTX_3(C, cs), h)
  | refocus3_closure (CLO_LET (x, c, t, bs), C, h)
    = refocus3_closure (c, CTX_2 (x, C, t, bs), h)
  | refocus3_closure (CLO_REC [], C, h)
    = refocus3_context (C, VAL_REC [], h)
  | refocus3_closure (CLO_REC ((s, c) :: scs), C, h)
    = refocus3_closure (c, CTX_5 ([], s, C, scs), h)
  | refocus3_closure (CLO_REC_REF (c0, c1), C, h)
    = refocus3_closure (c0, CTX_6 (C, c1), h)
  | refocus3_closure (CLO_REC_SET (c0, c1, c2), C, h)
    = refocus3_closure (c0, CTX_8 (C, c1, c2), h)
  | refocus3_closure (CLO_REC_DEL (c0, c1), C, h)
    = refocus3_closure (c0, CTX_11 (C, c1), h)
  (* mutation *)
  | refocus3_closure (CLO_LOC i, C, h)
    = refocus3_context (C, VAL_LOC i, h)
  | refocus3_closure (CLO_SET (c0, c1), C, h)
    = refocus3_closure (c0, CTX_13 (C, c1), h)
  | refocus3_closure (CLO_REF c, C, h)
    = refocus3_closure (c, CTX_15 C, h)
  | refocus3_closure (CLO_DEREF c, C, h)
    = refocus3_closure (c, CTX_16 C, h)
  | refocus3_closure (CLO_GND (SET (t0, t1), bs), C, h)
    = iterate3 (DEC (PR_PROP_SET (t0, t1, bs), C), h)
  | refocus3_closure (CLO_GND (REF t, bs), C, h)
    = iterate3 (DEC (PR_PROP_REF (t, bs), C), h)
  | refocus3_closure (CLO_GND (DEREF t, bs), C, h)
    = iterate3 (DEC (PR_PROP_DEREF (t, bs), C), h)

and refocus3_context ((CTX_1, v, h) : context * value * sto) : result
    = iterate3 (VAL v, h)
  | refocus3_context (CTX_2 (x, C, t, bs), v, h)
    = iterate3 (DEC (PR_LET (x, v, t, bs), C), h)
  | refocus3_context (CTX_3 (C, []), v, h)
    = iterate3 (DEC (PR_APP (v, []), C), h)
  | refocus3_context (CTX_3 (C, c :: cs), v, h)
    = refocus3_closure (c, (CTX_4 (v, [], C, cs)), h)
  | refocus3_context (CTX_4 (v0, vs, C, []), v, h)
    = iterate3 (DEC (PR_APP (v0, vs @ [v]), C), h)
  | refocus3_context (CTX_4 (v0, vs, C, c :: cs), v, h)
    = refocus3_closure (c, CTX_4 (v0, vs @ [v], C, cs), h)
  | refocus3_context (CTX_5 (vflds, s, C, []), v, h)
    = refocus3_context (C, VAL_REC (vflds @ [(s, v)]), h)
  | refocus3_context (CTX_5 (vflds, s, C, (s0, c0) :: cs), v, h)
    = refocus3_closure (c0, CTX_5 (vflds @ [(s, v)], s0, C, cs), h)
  | refocus3_context (CTX_6 (C, c), v, h)
    = refocus3_closure (c, CTX_7 (v, C), h)
  | refocus3_context (CTX_7 (v0, C), v, h)
    = iterate3 (DEC (PR_REC_REF (v0, v), C), h)
  | refocus3_context (CTX_8 (C, c0, c1), v, h)
    = refocus3_closure (c0, CTX_9 (v, C, c1), h)
  | refocus3_context (CTX_9 (v0, C, c), v, h)
    = refocus3_closure (c, CTX_10 (v0, v, C), h)
  | refocus3_context (CTX_10 (v0, v1, C), v, h)
    = iterate3 (DEC (PR_REC_SET (v0, v1, v), C), h)
  | refocus3_context (CTX_11 (C, c), v, h)
    = refocus3_closure (c, CTX_12 (v, C), h)
  | refocus3_context (CTX_12 (v0, C), v, h)
    = iterate3 (DEC (PR_REC_DEL (v0, v), C), h)
  (* mutation *)
  | refocus3_context (CTX_13 (C, c), v, h)
    = refocus3_closure (c, CTX_14 (v, C), h)
  | refocus3_context (CTX_14 (v0, C), v, h)
    = iterate3 (DEC (PR_SET (v0, v), C), h)
  | refocus3_context (CTX_15 C, v, h)
    = iterate3 (DEC (PR_REF v, C), h)
  | refocus3_context (CTX_16 C, v, h)
    = iterate3 (DEC (PR_DEREF v, C), h)

and iterate3 ((VAL v, h) : value_or_decomposition * sto) : result
    = RESULT (v, h)
  | iterate3 (DEC (PR_VAR (x, bs), C), h)
    = refocus3_closure (embed_value_in_closure (Env.lookup (x, bs)), C, h)
  | iterate3 (DEC (PR_APP (VAL_FUNC (xs, t, bs), vs), C), h)
    = if length xs = length vs 
      then refocus3_closure (CLO_GND (t, Env.extend (xs, vs, bs)), C, h)
      else WRONG "Arity mismatch"
  | iterate3 (DEC (PR_APP (v, vs), C), h)
    = WRONG "Stuck"        
  | iterate3 (DEC (PR_LET (x, v, t, bs), C), h)
    = refocus3_closure (CLO_GND (t, Env.extend ([x], [v], bs)), C, h)
  | iterate3 (DEC (PR_REC_REF (VAL_REC flds, VAL_STR s), C), h)
    = refocus3_closure ((if Rec.contains (flds, s)
                         then (embed_value_in_closure (Rec.lookup (flds, s)))
                         else CLO_UNDEFN), 
                        C, h)
  | iterate3 (DEC (PR_REC_REF (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate3 (DEC (PR_REC_SET (VAL_REC flds, VAL_STR s, v), C), h)
    = refocus3_closure (embed_value_in_closure
                            (VAL_REC (if Rec.contains (flds, s)
                                      then (Rec.update (flds, s, v))
                                      else ((s, v) :: flds))),
                        C, h)
  | iterate3 (DEC (PR_REC_SET (v0, v1, v2), C), h)
    = WRONG "Stuck"
  | iterate3 (DEC (PR_REC_DEL (VAL_REC flds, VAL_STR s), C), h)
    = refocus3_closure (embed_value_in_closure
                            (VAL_REC (if Rec.contains (flds, s)
                                      then (Rec.remove (flds, s))
                                      else flds)),
                        C, h)
  | iterate3 (DEC (PR_REC_DEL (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate3 (DEC (PR_PROP_APP (t, ts, bs), C), h)
    = refocus3_closure (CLO_APP (CLO_GND (t, bs),
                                 map (fn t => (CLO_GND (t, bs))) ts),
                        C, h)
  | iterate3 (DEC (PR_PROP_REC (sts, bs), C), h)
    = refocus3_closure (CLO_REC (map (fn (s, t) => 
                                         (s, CLO_GND (t, bs))) sts), C, h)
  | iterate3 (DEC (PR_PROP_LET (x, t0, t1, bs), C), h)
    = refocus3_closure (CLO_LET (x, CLO_GND (t0, bs), t1, bs), C, h)
  | iterate3 (DEC (PR_PROP_REC_REF (t0, t1, bs), C), h)
    = refocus3_closure (CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)
  | iterate3 (DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C), h)
    = refocus3_closure (CLO_REC_SET (CLO_GND (t0, bs), 
                                 CLO_GND (t1, bs), 
                                 CLO_GND (t2, bs)), C, h)
  | iterate3 (DEC (PR_PROP_REC_DEL (t0, t1, bs), C), h)
    = refocus3_closure (CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)

  (* mutation *)
  | iterate3 (DEC (PR_REF v, C), h)
    = let val i = Sto.alloc h in
	  refocus3_closure (CLO_LOC i, C, ((i, v) :: h))
      end
  | iterate3 (DEC (PR_DEREF (VAL_LOC i), C), h)
    = (case Sto.lookup (i, h)
	of NONE
	   => WRONG "deref"
	 | SOME v
	   => refocus3_closure (embed_value_in_closure v, C, h))
  | iterate3 (DEC (PR_DEREF v, C), h)
    = WRONG "Store"
  | iterate3 (DEC (PR_SET (VAL_LOC i, v), C), h)
    = refocus3_closure (embed_value_in_closure v, C, Sto.update (i, h, v))
  | iterate3 (DEC (PR_SET (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate3 (DEC (PR_PROP_SET (t0, t1, bs), C), h)
    = refocus3_closure (CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)
  | iterate3 (DEC (PR_PROP_REF (t, bs), C), h)
    = refocus3_closure (CLO_REF (CLO_GND (t, bs)), C, h)
  | iterate3 (DEC (PR_PROP_DEREF (t, bs), C), h)
    = refocus3_closure (CLO_DEREF (CLO_GND (t, bs)), C, h)

fun normalize3 (t : term) : result
  = refocus3_closure (CLO_GND (t, initial_bindings), CTX_1, [])

(* ************************************************************************** *)

(* REASONING *)

(* Compressing corridor transitions, making use of the equivalent between
   refocus4_closure (embed value in closure v, C, h) and refocus4_context (C, v, h).

  | refocus4_closure (CLO_GND (VAR x, bs), C, h)
    = iterate4 (DEC (PR_VAR (x, bs), C), h)
    = refocus4_closure (embed_value_in_closure (Env.lookup (x, bs)), C, h)
    = refocus4_context (C, (Env.lookup (x, bs)), h)

  | refocus4_closure (CLO_GND (LET (x, t0, t1), bs), C, h)
    = iterate4 (DEC (PR_PROP_LET (x, t0, t1, bs), C), h) 
    = refocus4_closure (CLO_LET (x, CLO_GND (t0, bs), t1, bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_2 (x, C, t1, bs), h)

  | refocus4_closure (CLO_GND (APP (t, ts), bs), C, h)
    = iterate4 (DEC (PR_PROP_APP (t, ts, bs), C), h)
    = refocus4_closure (CLO_APP (CLO_GND (t, bs),
                                 map (fn t => (CLO_GND (t, bs))) ts),
                        C, h)
    = refocus4_closure (CLO_GND (t, bs), 
                        CTX_3 (C, map (fn t => (CLO_GND (t, bs))) ts), h)

  | refocus4_closure (CLO_GND (REC flds, bs), C, h)
    = iterate4 (DEC (PR_PROP_REC (flds, bs), C), h)
    = refocus4_closure (CLO_REC (map (fn (s, t) => 
                                         (s, CLO_GND (t, bs))) flds), C, h)

  Case 1:
  | refocus4_closure (CLO_REC [], C, h)
    = refocus4_context (C, VAL_REC [], h)

  Case 2:
  | refocus4_closure (CLO_REC ((s, c) :: scs), C, h)
    = refocus4_closure (c, CTX_5 ([], s, C, scs), h)

  So we replace with:
  | refocus4_closure (CLO_GND (REC [], bs), C, h)
    = refocus4_context (C, VAL_REC [], h)
  | refocus4_closure (CLO_GND (REC ((s, t) :: sts), bs), C)
    = refocus4_closure (CLO_GND (t, bs), 
                        CTX_5 ([], s, C,
                               (map (fn (s, t) => 
                                        (s, CLO_GND (t, bs)))
                                    sts)), h)

  | refocus4_closure (CLO_GND (REC_REF (t0, t1), bs), C, h)
    = iterate4 (DEC (PR_PROP_REC_REF (t0, t1, bs), C), h)
    = refocus4_closure (CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_6 (C, CLO_GND (t1, bs)), h)

  | refocus4_closure (CLO_GND (REC_SET (t0, t1, t2), bs), C, h)
    = iterate4 (DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C), h)
    = refocus4_closure (CLO_REC_SET (CLO_GND (t0, bs), 
                                 CLO_GND (t1, bs), 
                                 CLO_GND (t2, bs)), C, h)
    = refocus4_closure (CLO_GND (t0, bs), 
                        CTX_8 (C, CLO_GND (t1, bs), CLO_GND (t2, bs)), h)

  | refocus4_closure (CLO_GND (REC_DEL (t0, t1), bs), C, h)
    = iterate4 (DEC (PR_PROP_REC_DEL (t0, t1, bs), C), h)
    = refocus4_closure (CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_11 (C, CLO_GND (t1, bs)), h)

  | refocus4_context (CTX_1, v, h)
    = iterate4 (VAL v, h)
    = RESULT (v, h)

  | refocus4_context (CTX_2 (x, C, t, bs), v, h)
    = iterate4 (DEC (PR_LET (x, v, t, bs), C), h)
    = refocus4_closure (CLO_GND (t, Env.extend ([x], [v], bs)), C, h)

  | iterate4 (DEC (PR_REC_REF (VAL_REC flds, VAL_STR s), C), h)
    = refocus4_closure ((if Rec.contains (flds, s)
                         then (embed_value_in_closure (Rec.lookup (flds, s)))
                         else CLO_UNDEFN), 
                        C, h)
    = refocus4_context (C, (if Rec.contains (flds, s)
                            then (Rec.lookup (flds, s))
                            else VAL_UNDEFN), h)

  | iterate4 (DEC (PR_REC_SET (VAL_REC flds, VAL_STR s, v), C), h)
    = refocus4_closure (embed_value_in_closure
                            (VAL_REC (if Rec.contains (flds, s)
                                      then (Rec.update (flds, s, v))
                                      else ((s, v) :: flds))),
                        C, h)
    = refocus4_context (C, (VAL_REC (if Rec.contains (flds, s)
                                     then (Rec.update (flds, s, v))
                                     else ((s, v) :: flds))), h)

  | iterate4 (DEC (PR_REC_DEL (VAL_REC flds, VAL_STR s), C), h)
    = refocus4_closure (embed_value_in_closure
                            (VAL_REC (if Rec.contains (flds, s)
                                      then (Rec.remove (flds, s))
                                      else flds)),
                        C, h)
    = refocus4_context (C, VAL_REC (if Rec.contains (flds, s)
                                    then (Rec.remove (flds, s))
                                    else flds), h)

  (* mutation *)

  | refocus4_closure (CLO_GND (SET (t0, t1), bs), C, h)
    = iterate4 (DEC (PR_PROP_SET (t0, t1, bs), C), h)
    = refocus4_closure (CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)

  | refocus4_closure (CLO_GND (REF t, bs), C, h)
    = iterate4 (DEC (PR_PROP_REF (t, bs), C), h)
    = refocus4_closure (CLO_REF (CLO_GND (t, bs)), C, h)

  | refocus4_closure (CLO_GND (DEREF t, bs), C, h)
    = iterate4 (DEC (PR_PROP_DEREF (t, bs), C), h)
    = refocus4_closure (CLO_DEREF (CLO_GND (t, bs)), C, h)

  | refocus4_closure (CLO_GND (SET (t0, t1), bs), C, h)
    = refocus4_closure (CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_13 (C, CLO_GND (t1, bs)), h)   

  | refocus4_closure (CLO_GND (REF t, bs), C, h)
    = refocus4_closure (CLO_REF (CLO_GND (t, bs)), C, h)
    = refocus4_closure (CLO_GND (t, bs), CTX_15 C, h)

  | refocus4_closure (CLO_GND (DEREF t, bs), C, h)
    = refocus4_closure (CLO_DEREF (CLO_GND (t, bs)), C, h)
    = refocus4_closure (CLO_GND (t, bs), CTX_16 C, h)

  | refocus4_context (CTX_15 C, v, h)
    = iterate4 (DEC (PR_REF v, C), h)
    = let val i = Sto.alloc h in
	  refocus3_closure (CLO_LOC i, C, ((i, v) :: h))
      end
    = let val i = Sto.alloc h in
	  refocus3_context (C, VAL_LOC i, ((i, v) :: h))
      end

*)

exception DEAD_CLAUSE

fun refocus4_closure ((CLO_NUM n, C, h) : closure * context * sto) : result
    = raise DEAD_CLAUSE
  | refocus4_closure (CLO_STR s, C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_BOOL b, C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_UNDEFN, C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_NULL, C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_GND (NUM n, bs), C, h)
    = refocus4_context (C, VAL_NUM n, h)
  | refocus4_closure (CLO_GND (STR s, bs), C, h)
    = refocus4_context (C, VAL_STR s, h)
  | refocus4_closure (CLO_GND (BOOL b, bs), C, h)
    = refocus4_context (C, VAL_BOOL b, h)
  | refocus4_closure (CLO_GND (UNDEFN, bs), C, h)
    = refocus4_context (C, VAL_UNDEFN, h)
  | refocus4_closure (CLO_GND (NULL, bs), C, h)
    = refocus4_context (C, VAL_NULL, h)
  | refocus4_closure (CLO_GND (FUNC (xs, t), bs), C, h)
    = refocus4_context (C, VAL_FUNC (xs, t, bs), h)
  | refocus4_closure (CLO_GND (VAR x, bs), C, h)
    = refocus4_context (C, (Env.lookup (x, bs)), h)
  | refocus4_closure (CLO_GND (LET (x, t0, t1), bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_2 (x, C, t1, bs), h)
  | refocus4_closure (CLO_GND (APP (t, ts), bs), C, h)
    = refocus4_closure (CLO_GND (t, bs), 
                        CTX_3 (C, map (fn t => (CLO_GND (t, bs))) ts), h)
  | refocus4_closure (CLO_GND (REC [], bs), C, h)
    = refocus4_context (C, VAL_REC [], h)
  | refocus4_closure (CLO_GND (REC ((s, t) :: sts), bs), C, h)
    = refocus4_closure (CLO_GND (t, bs), 
                        CTX_5 ([], s, C,
                               (map (fn (s, t) => 
                                        (s, CLO_GND (t, bs)))
                                    sts)), h)
  | refocus4_closure (CLO_GND (REC_REF (t0, t1), bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_6 (C, CLO_GND (t1, bs)), h)
  | refocus4_closure (CLO_GND (REC_SET (t0, t1, t2), bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), 
                        CTX_8 (C, CLO_GND (t1, bs), CLO_GND (t2, bs)), h)
  | refocus4_closure (CLO_GND (REC_DEL (t0, t1), bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_11 (C, CLO_GND (t1, bs)), h)
  | refocus4_closure (CLO_APP (c, cs), C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_LET (x, c, t, bs), C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_REC [], C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_REC ((s, c) :: scs), C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_REC_REF (c0, c1), C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_REC_SET (c0, c1, c2), C, h)
    = raise DEAD_CLAUSE 
  | refocus4_closure (CLO_REC_DEL (c0, c1), C, h)
    = raise DEAD_CLAUSE 
  (* mutation *)
  | refocus4_closure (CLO_LOC i, C, h)
    = raise DEAD_CLAUSE
  | refocus4_closure (CLO_SET (c0, c1), C, h)
    = raise DEAD_CLAUSE
  | refocus4_closure (CLO_REF c, C, h)
    = raise DEAD_CLAUSE
  | refocus4_closure (CLO_DEREF c, C, h)
    = raise DEAD_CLAUSE
  | refocus4_closure (CLO_GND (SET (t0, t1), bs), C, h)
    = refocus4_closure (CLO_GND (t0, bs), CTX_13 (C, CLO_GND (t1, bs)), h)   
  | refocus4_closure (CLO_GND (REF t, bs), C, h)
    = refocus4_closure (CLO_GND (t, bs), CTX_15 C, h)
  | refocus4_closure (CLO_GND (DEREF t, bs), C, h)
    = refocus4_closure (CLO_GND (t, bs), CTX_16 C, h)
      
and refocus4_context ((CTX_1, v, h) : context * value * sto) : result
    = RESULT (v, h)
  | refocus4_context (CTX_2 (x, C, t, bs), v, h)
    = refocus4_closure (CLO_GND (t, Env.extend ([x], [v], bs)), C, h)
  | refocus4_context (CTX_3 (C, []), v, h)
    = iterate4 (DEC (PR_APP (v, []), C), h)
  | refocus4_context (CTX_3 (C, c :: cs), v, h)
    = refocus4_closure (c, (CTX_4 (v, [], C, cs)), h)
  | refocus4_context (CTX_4 (v0, vs, C, []), v, h)
    = iterate4 (DEC (PR_APP (v0, vs @ [v]), C), h)
  | refocus4_context (CTX_4 (v0, vs, C, c :: cs), v, h)
    = refocus4_closure (c, CTX_4 (v0, vs @ [v], C, cs), h)
  | refocus4_context (CTX_5 (vflds, s, C, []), v, h)
    = refocus4_context (C, VAL_REC (vflds @ [(s, v)]), h)
  | refocus4_context (CTX_5 (vflds, s, C, (s0, c0) :: cs), v, h)
    = refocus4_closure (c0, CTX_5 (vflds @ [(s, v)], s0, C, cs), h)
  | refocus4_context (CTX_6 (C, c), v, h)
    = refocus4_closure (c, CTX_7 (v, C), h)
  | refocus4_context (CTX_7 (v0, C), v, h)
    = iterate4 (DEC (PR_REC_REF (v0, v), C), h)
  | refocus4_context (CTX_8 (C, c0, c1), v, h)
    = refocus4_closure (c0, CTX_9 (v, C, c1), h)
  | refocus4_context (CTX_9 (v0, C, c), v, h)
    = refocus4_closure (c, CTX_10 (v0, v, C), h)
  | refocus4_context (CTX_10 (v0, v1, C), v, h)
    = iterate4 (DEC (PR_REC_SET (v0, v1, v), C), h)
  | refocus4_context (CTX_11 (C, c), v, h)
    = refocus4_closure (c, CTX_12 (v, C), h)
  | refocus4_context (CTX_12 (v0, C), v, h)
    = iterate4 (DEC (PR_REC_DEL (v0, v), C), h)
  (* mutation *)
  | refocus4_context (CTX_13 (C, c), v, h)
    = refocus4_closure (c, CTX_14 (v, C), h)
  | refocus4_context (CTX_14 (v0, C), v, h)
    = iterate4 (DEC (PR_SET (v0, v), C), h)
  | refocus4_context (CTX_15 C, v, h)
    = let val i = Sto.alloc h in
	  refocus4_context (C, VAL_LOC i, ((i, v) :: h))
      end
  | refocus4_context (CTX_16 C, v, h)
    = iterate4 (DEC (PR_DEREF v, C), h)

and iterate4 ((VAL v, h) : value_or_decomposition * sto) : result
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_VAR (x, bs), C), h)
    = refocus4_context (C, (Env.lookup (x, bs)), h)
  | iterate4 (DEC (PR_APP (VAL_FUNC (xs, t, bs), vs), C), h)
    = if length xs = length vs 
      then refocus4_closure (CLO_GND (t, Env.extend (xs, vs, bs)), C, h)
      else WRONG "Arity mismatch"
  | iterate4 (DEC (PR_APP (v, vs), C), h)
    = WRONG "Stuck"        
  | iterate4 (DEC (PR_LET (x, v, t, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_REC_REF (VAL_REC flds, VAL_STR s), C), h)
    = refocus4_context (C, (if Rec.contains (flds, s)
                            then (Rec.lookup (flds, s))
                            else VAL_UNDEFN), 
			h)
  | iterate4 (DEC (PR_REC_REF (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate4 (DEC (PR_REC_SET (VAL_REC flds, VAL_STR s, v), C), h)
    = refocus4_context (C, (VAL_REC (if Rec.contains (flds, s)
                                     then (Rec.update (flds, s, v))
                                     else ((s, v) :: flds))),
			h)
  | iterate4 (DEC (PR_REC_SET (v0, v1, v2), C), h)
    = WRONG "Stuck"
  | iterate4 (DEC (PR_REC_DEL (VAL_REC flds, VAL_STR s), C), h)
    = refocus4_context (C, VAL_REC (if Rec.contains (flds, s)
                                    then (Rec.remove (flds, s))
                                    else flds), h)
  | iterate4 (DEC (PR_REC_DEL (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate4 (DEC (PR_PROP_APP (t, ts, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REC ([], bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REC ((s, t) :: sts, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_LET (x, t0, t1, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REC_REF (t0, t1, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REC_SET (t0, t1, t2, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REC_DEL (t0, t1, bs), C), h)
    = raise DEAD_CLAUSE
  (* mutation *)
  | iterate4 (DEC (PR_REF v, C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_DEREF (VAL_LOC i), C), h)
    = (case Sto.lookup (i, h)
	of NONE
	   => WRONG "deref"
	 | SOME v
	   => refocus4_context (C, v, h))
  | iterate4 (DEC (PR_DEREF v, C), h)
    = WRONG "Store"
  | iterate4 (DEC (PR_SET (VAL_LOC i, v), C), h)
    = refocus4_context (C, v, Sto.update (i, h, v))
  | iterate4 (DEC (PR_SET (v0, v1), C), h)
    = WRONG "Stuck"
  | iterate4 (DEC (PR_PROP_SET (t0, t1, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_REF (t, bs), C), h)
    = raise DEAD_CLAUSE
  | iterate4 (DEC (PR_PROP_DEREF (t, bs), C), h)
    = raise DEAD_CLAUSE

fun normalize4 (t : term) : result
  = refocus4_closure (CLO_GND (t, initial_bindings), CTX_1, [])


(* ************************************************************************** *)

(* A few tests -- these have to be repeated later due to the
   redefining of the data types. *)

fun test norm =    
    let val RESULT (VAL_NUM 5, [])
	  = norm (REC_REF (REC [("foo", NUM 5)], STR "foo"))                
	val RESULT (VAL_UNDEFN, [])
	  = norm (REC_REF (REC [("foo", NUM 5)], STR "bar"))
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_SET (REC [], STR "foo", NUM 5))	    
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_SET (REC [("foo", NUM 9)], STR "foo", NUM 5))	    
	val RESULT (VAL_REC [], [])
	  = norm (REC_DEL (REC [("foo", NUM 5)], STR "foo"))	    
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_DEL (REC [("foo", NUM 5)], STR "bar"))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (APP (FUNC (["x"], VAR "x"), [(NUM 5)]))	    
	val WRONG "Stuck"
	  = norm (APP (NUM 7, [NUM 5]))	    
	val WRONG "Arity mismatch"
	  = norm (APP (FUNC ([], VAR "x"), [NUM 5]))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (LET ("x", NUM 5, VAR "x"))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (APP (LET ("x", NUM 5, FUNC ([], VAR "x")), []))	    

	val RESULT (VAL_LOC 1, [(1, VAL_NUM 5)])
	  = norm (REF (NUM 5))
   
	val RESULT (VAL_NUM 5, [(1, VAL_NUM 5)])
	  = norm (DEREF (REF (NUM 5)))	    
	val RESULT (VAL_NUM 9, [(1, VAL_NUM 9)]) 
	  = norm (SET (REF (NUM 5), (NUM 9)))
    in
	"OK"
    end

val ["OK", "OK", "OK", "OK", "OK", "OK"] = 
    map test [normalize0, normalize0', normalize1, normalize2, normalize3, normalize4]

(* ************************************************************************** *)

(* Drop dead clauses.
   All calls to refocus_closure are of the form (CLO_GND (t, bs), C), so we
   flatten to t, bs, C. 
   All calls to iterate are of the form DEC (pr, C), so we flatten to pr, C.
*)

datatype value = VAL_NUM of int
               | VAL_STR of string
               | VAL_BOOL of bool
               | VAL_UNDEFN 
               | VAL_NULL
               | VAL_FUNC of string list * term * bindings
               | VAL_REC of (string * value) list
	       (* mutation *)
	       | VAL_LOC of loc
withtype bindings = value Env.env
     and loc = int
     and sto = value Sto.sto 

datatype context = CTX_1
                 | CTX_2 of string * context * term * bindings
                 | CTX_3 of context * (term * bindings) list
                 | CTX_4 of value * value list * context * (term * bindings) list
                 | CTX_5 of (string * value) list *
                            string * context *
                            (string * (term * bindings)) list
                 | CTX_6 of context * (term * bindings)
                 | CTX_7 of value * context
                 | CTX_8 of context * (term * bindings) * (term * bindings)
                 | CTX_9 of value * context * (term * bindings)
                 | CTX_10 of value * value * context
                 | CTX_11 of context * (term * bindings)
                 | CTX_12 of value * context
		 (* mutation *)
		 | CTX_13 of context * (term * bindings)
		 | CTX_14 of value * context
		 | CTX_15 of context
		 | CTX_16 of context

datatype potential_redex = PR_APP of value * (value list)
                         | PR_REC_REF of value * value
                         | PR_REC_SET of value * value * value
                         | PR_REC_DEL of value * value
			 (* mutation *)
			 | PR_DEREF of value
			 | PR_SET of value * value

val initial_bindings = Env.empty

datatype result = RESULT of value * sto
                | WRONG of string

fun refocus5_closure ((NUM n, bs, C, h) : term * bindings * context * sto) : result
    = refocus5_context (C, VAL_NUM n, h)
  | refocus5_closure (STR s, bs, C, h)
    = refocus5_context (C, VAL_STR s, h)
  | refocus5_closure (BOOL b, bs, C, h)
    = refocus5_context (C, VAL_BOOL b, h)
  | refocus5_closure (UNDEFN, bs, C, h)
    = refocus5_context (C, VAL_UNDEFN, h)
  | refocus5_closure (NULL, bs, C, h)
    = refocus5_context (C, VAL_NULL, h)
  | refocus5_closure (FUNC (xs, t), bs, C, h)
    = refocus5_context (C, VAL_FUNC (xs, t, bs), h)
  | refocus5_closure (VAR x, bs, C, h)
    = refocus5_context (C, (Env.lookup (x, bs)), h)
  | refocus5_closure (LET (x, t0, t1), bs, C, h)
    = refocus5_closure (t0, bs, CTX_2 (x, C, t1, bs), h)
  | refocus5_closure (APP (t, ts), bs, C, h)
    = refocus5_closure (t, bs, 
                        CTX_3 (C, map (fn t => (t, bs)) ts), h)
  | refocus5_closure (REC [], bs, C, h)
    = refocus5_context (C, VAL_REC [], h)
  | refocus5_closure (REC ((s, t) :: sts), bs, C, h)
    = refocus5_closure (t, bs, 
                        CTX_5 ([], s, C,
                               (map (fn (s, t) => 
                                        (s, (t, bs)))
                                    sts)), 
			h)
  | refocus5_closure (REC_REF (t0, t1), bs, C, h)
    = refocus5_closure (t0, bs, CTX_6 (C, (t1, bs)), h)
  | refocus5_closure (REC_SET (t0, t1, t2), bs, C, h)
    = refocus5_closure (t0, bs, CTX_8 (C, (t1, bs), (t2, bs)), h)
  | refocus5_closure (REC_DEL (t0, t1), bs, C, h)
    = refocus5_closure (t0, bs, CTX_11 (C, (t1, bs)), h)
  (* mutation *)
  | refocus5_closure (SET (t0, t1), bs, C, h)
    = refocus5_closure (t0, bs, CTX_13 (C, (t1, bs)), h)
  | refocus5_closure (REF t, bs, C, h)
    = refocus5_closure (t, bs, CTX_15 C, h)
  | refocus5_closure (DEREF t, bs, C, h)
    = refocus5_closure (t, bs, CTX_16 C, h)
   
and refocus5_context ((CTX_1, v, h) : context * value * sto) : result
    = RESULT (v, h)
  | refocus5_context (CTX_2 (x, C, t, bs), v, h)
    = refocus5_closure (t, Env.extend ([x], [v], bs), C, h)
  | refocus5_context (CTX_3 (C, []), v, h)
    = iterate5 (PR_APP (v, []), C, h)
  | refocus5_context (CTX_3 (C, (t, bs) :: cs), v, h)
    = refocus5_closure (t, bs, (CTX_4 (v, [], C, cs)), h)
  | refocus5_context (CTX_4 (v0, vs, C, []), v, h)
    = iterate5 (PR_APP (v0, vs @ [v]), C, h)
  | refocus5_context (CTX_4 (v0, vs, C, (t, bs) :: cs), v, h)
    = refocus5_closure (t, bs, CTX_4 (v0, vs @ [v], C, cs), h)
  | refocus5_context (CTX_5 (vflds, s, C, []), v, h)
    = refocus5_context (C, VAL_REC (vflds @ [(s, v)]), h)
  | refocus5_context (CTX_5 (vflds, s, C, (s0, (t, bs)) :: cs), v, h)
    = refocus5_closure (t, bs, CTX_5 (vflds @ [(s, v)], s0, C, cs), h)
  | refocus5_context (CTX_6 (C, (t, bs)), v, h)
    = refocus5_closure (t, bs, CTX_7 (v, C), h)
  | refocus5_context (CTX_7 (v0, C), v, h)
    = iterate5 (PR_REC_REF (v0, v), C, h)
  | refocus5_context (CTX_8 (C, (t, bs), c1), v, h)
    = refocus5_closure (t, bs, CTX_9 (v, C, c1), h)
  | refocus5_context (CTX_9 (v0, C, (t, bs)), v, h)
    = refocus5_closure (t, bs, CTX_10 (v0, v, C), h)
  | refocus5_context (CTX_10 (v0, v1, C), v, h)
    = iterate5 (PR_REC_SET (v0, v1, v), C, h)
  | refocus5_context (CTX_11 (C, (t, bs)), v, h)
    = refocus5_closure (t, bs, CTX_12 (v, C), h)
  | refocus5_context (CTX_12 (v0, C), v, h)
    = iterate5 (PR_REC_DEL (v0, v), C, h)
  (* mutation *)
  | refocus5_context (CTX_13 (C, (t, bs)), v, h)
    = refocus5_closure (t, bs, CTX_14 (v, C), h)
  | refocus5_context (CTX_14 (v0, C), v, h)
    = iterate5 (PR_SET (v0, v), C, h)
  | refocus5_context (CTX_15 C, v, h)
    = let val i = Sto.alloc h in
	  refocus5_context (C, VAL_LOC i, ((i, v) :: h))
      end
  | refocus5_context (CTX_16 C, v, h)
    = iterate5 (PR_DEREF v, C, h)

and iterate5 (PR_APP (VAL_FUNC (xs, t, bs), vs), C, h)
    = if length xs = length vs 
      then refocus5_closure (t, Env.extend (xs, vs, bs), C, h)
      else WRONG "Arity mismatch"
  | iterate5 (PR_APP (v, vs), C, h)
    = WRONG "Stuck"        
  | iterate5 (PR_REC_REF (VAL_REC flds, VAL_STR s), C, h)
    = refocus5_context (C, (if Rec.contains (flds, s)
                            then (Rec.lookup (flds, s))
                            else VAL_UNDEFN),
			h)
  | iterate5 (PR_REC_REF (v0, v1), C, h)
    = WRONG "Stuck"
  | iterate5 (PR_REC_SET (VAL_REC flds, VAL_STR s, v), C, h)
    = refocus5_context (C, (VAL_REC (if Rec.contains (flds, s)
                                     then (Rec.update (flds, s, v))
                                     else ((s, v) :: flds))),
			h)
  | iterate5 (PR_REC_SET (v0, v1, v2), C, h)
    = WRONG "Stuck"
  | iterate5 (PR_REC_DEL (VAL_REC flds, VAL_STR s), C, h)
    = refocus5_context (C, VAL_REC (if Rec.contains (flds, s)
                                    then (Rec.remove (flds, s))
                                    else flds),
			h)
  | iterate5 (PR_REC_DEL (v0, v1), C, h)
    = WRONG "Stuck"
  (* mutation *)
  | iterate5 (PR_DEREF (VAL_LOC i), C, h)
    = (case Sto.lookup (i, h)
	of NONE
	   => WRONG "deref"
	 | SOME v
	   => refocus5_context (C, v, h))
  | iterate5 (PR_DEREF v, C, h)
    = WRONG "Store"
  | iterate5 (PR_SET (VAL_LOC i, v), C, h)
    = refocus5_context (C, v, Sto.update (i, h, v))
  | iterate5 (PR_SET (v0, v1), C, h)
    = WRONG "Stuck"

fun normalize5 (t : term) : result
  = refocus5_closure (t, initial_bindings, CTX_1, [])

(* ************************************************************************** *)

(* Inline iterate6, eliminating PR_*. *)

fun eval ((NUM n, bs, C, h) : term * bindings * context * sto) : result
    = cont (C, VAL_NUM n, h)
  | eval (STR s, bs, C, h)
    = cont (C, VAL_STR s, h)
  | eval (BOOL b, bs, C, h)
    = cont (C, VAL_BOOL b, h)
  | eval (UNDEFN, bs, C, h)
    = cont (C, VAL_UNDEFN, h)
  | eval (NULL, bs, C, h)
    = cont (C, VAL_NULL, h)
  | eval (FUNC (xs, t), bs, C, h)
    = cont (C, VAL_FUNC (xs, t, bs), h)
  | eval (VAR x, bs, C, h)
    = cont (C, (Env.lookup (x, bs)), h)
  | eval (LET (x, t0, t1), bs, C, h)
    = eval (t0, bs, CTX_2 (x, C, t1, bs), h)
  | eval (APP (t, ts), bs, C, h)
    = eval (t, bs, CTX_3 (C, map (fn t => (t, bs)) ts), h)
  | eval (REC [], bs, C, h)
    = cont (C, VAL_REC [], h)
  | eval (REC ((s, t) :: sts), bs, C, h)
    = eval (t, bs, CTX_5 ([], s, C, (map (fn (s, t) => (s, (t, bs))) sts)), h)
  | eval (REC_REF (t0, t1), bs, C, h)
    = eval (t0, bs, CTX_6 (C, (t1, bs)), h)
  | eval (REC_SET (t0, t1, t2), bs, C, h)
    = eval (t0, bs, CTX_8 (C, (t1, bs), (t2, bs)), h)
  | eval (REC_DEL (t0, t1), bs, C, h)
    = eval (t0, bs, CTX_11 (C, (t1, bs)), h)
  (* mutation *)
  | eval (SET (t0, t1), bs, C, h)
    = eval (t0, bs, CTX_13 (C, (t1, bs)), h)
  | eval (REF t, bs, C, h)
    = eval (t, bs, CTX_15 C, h)
  | eval (DEREF t, bs, C, h)
    = eval (t, bs, CTX_16 C, h)
      
and cont ((CTX_1, v, h) : context * value * sto) : result
    = RESULT (v, h)
  | cont (CTX_2 (x, C, t, bs), v, h)
    = eval (t, Env.extend ([x], [v], bs), C, h)
  | cont (CTX_3 (C, []), VAL_FUNC (xs, t, bs), h)
    = if length xs = 0
      then eval (t, bs, C, h)
      else WRONG "Arity mismatch"
  | cont (CTX_3 (C, []), v, h)
    = WRONG "Stuck"
  | cont (CTX_3 (C, (t, bs) :: cs), v, h)
    = eval (t, bs, (CTX_4 (v, [], C, cs)), h)
  | cont (CTX_4 (VAL_FUNC (xs, t, bs), vs, C, []), v, h)
    = if length xs = 1 + length vs 
      then eval (t, Env.extend (xs, vs @ [v], bs), C, h)
      else WRONG "Arity mismatch"
  | cont (CTX_4 (v0, vs, C, []), v, h)
    = WRONG "Stuck"
  | cont (CTX_4 (v0, vs, C, (t, bs) :: cs), v, h)
    = eval (t, bs, CTX_4 (v0, vs @ [v], C, cs), h)
  | cont (CTX_5 (vflds, s, C, []), v, h)
    = cont (C, VAL_REC (vflds @ [(s, v)]), h)
  | cont (CTX_5 (vflds, s, C, (s0, (t, bs)) :: cs), v, h)
    = eval (t, bs, CTX_5 (vflds @ [(s, v)], s0, C, cs), h)
  | cont (CTX_6 (C, (t, bs)), v, h)
    = eval (t, bs, CTX_7 (v, C), h)
  | cont (CTX_7 (VAL_REC flds, C), VAL_STR s, h)
    = cont (C, (if Rec.contains (flds, s)
                then (Rec.lookup (flds, s))
                else VAL_UNDEFN),
	    h)    
  | cont (CTX_7 (v0, C), v, h)
    = WRONG "Stuck"
  | cont (CTX_8 (C, (t, bs), c1), v, h)
    = eval (t, bs, CTX_9 (v, C, c1), h)
  | cont (CTX_9 (v0, C, (t, bs)), v, h)
    = eval (t, bs, CTX_10 (v0, v, C), h)
  | cont (CTX_10 (VAL_REC flds, VAL_STR s, C), v, h)
    = cont (C, (VAL_REC (if Rec.contains (flds, s)
                         then (Rec.update (flds, s, v))
                         else ((s, v) :: flds))), 
	    h)
  | cont (CTX_10 (v0, v1, C), v, h)
    = WRONG "Stuck"
  | cont (CTX_11 (C, (t, bs)), v, h)
    = eval (t, bs, CTX_12 (v, C), h)      
  | cont (CTX_12 (VAL_REC flds, C), VAL_STR s, h)
    = cont (C, VAL_REC (if Rec.contains (flds, s)
                        then (Rec.remove (flds, s))
                        else flds),
	    h)
  | cont (CTX_12 (v0, C), v, h)
    = WRONG "Stuck"
  (* mutation *)
  | cont (CTX_13 (C, (t, bs)), v, h)
    = eval (t, bs, CTX_14 (v, C), h)
  | cont (CTX_14 (VAL_LOC i, C), v, h)
    = refocus5_context (C, v, Sto.update (i, h, v))
  | cont (CTX_14 (v0, C), v, h)
    = WRONG "Stuck"
  | cont (CTX_15 C, v, h)
    = let val i = Sto.alloc h in
	  cont (C, VAL_LOC i, ((i, v) :: h))
      end
  | cont (CTX_16 C, (VAL_LOC i), h)
    = (case Sto.lookup (i, h)
	of NONE
	   => WRONG "deref"
	 | SOME v
	   => refocus5_context (C, v, h))
  | cont (CTX_16 C, v, h)
    = WRONG "Store"

fun normalize6 (t : term) : result
  = eval (t, initial_bindings, CTX_1, [])

(* ************************************************************************** *)

(* A few tests *)

fun test norm =    
    let val RESULT (VAL_NUM 5, [])
	  = norm (REC_REF (REC [("foo", NUM 5)], STR "foo"))                
	val RESULT (VAL_UNDEFN, [])
	  = norm (REC_REF (REC [("foo", NUM 5)], STR "bar"))
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_SET (REC [], STR "foo", NUM 5))	    
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_SET (REC [("foo", NUM 9)], STR "foo", NUM 5))	    
	val RESULT (VAL_REC [], [])
	  = norm (REC_DEL (REC [("foo", NUM 5)], STR "foo"))	    
	val RESULT (VAL_REC [("foo", VAL_NUM 5)], [])
	  = norm (REC_DEL (REC [("foo", NUM 5)], STR "bar"))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (APP (FUNC (["x"], VAR "x"), [(NUM 5)]))	    
	val WRONG "Stuck"
	  = norm (APP (NUM 7, [NUM 5]))	    
	val WRONG "Arity mismatch"
	  = norm (APP (FUNC ([], VAR "x"), [NUM 5]))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (LET ("x", NUM 5, VAR "x"))	    
	val RESULT (VAL_NUM 5, [])
	  = norm (APP (LET ("x", NUM 5, FUNC ([], VAR "x")), []))	    
	val RESULT (VAL_LOC 1, [(1, VAL_NUM 5)])
	  = norm (REF (NUM 5))	    
	val RESULT (VAL_NUM 5, [(1, VAL_NUM 5)])
	  = norm (DEREF (REF (NUM 5)))	    
	val RESULT (VAL_NUM 9, [(1, VAL_NUM 9)]) 
	  = norm (SET (REF (NUM 5), (NUM 9)))
    in
	"OK"
    end

val ["OK","OK"] = map test [normalize5, normalize6]
