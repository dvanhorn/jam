(* This is a systematic derivation of a CK machine for Lambda_JS using
   the "Refocusing in Reduction Semantics" approach of Danvy and
   Nielsen.  In particular, we follow Danvy's "From Reduction-based to
   Reduction-free Normalization" lecture notes from AFP'08. *)

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

datatype opr
  = PLUS
  | NUM_TO_STR

datatype term 
  = VAR of string
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
  | WHILE of term * term
  | LAB of string * term
  | BREAK of string * term 
  | TRYC of term * string * term
  | TRYF of term * term
  | THROW of term
  | OP of opr * term list

datatype closure 
  = CLO_GND of term * bindings
  | CLO_STR of string
  | CLO_NUM of int
  | CLO_ADDR of int
  | CLO_BOOL of bool
  | CLO_UNDEFN 
  | CLO_NULL
  | CLO_REC of (string * closure) list
  | CLO_APP of closure * closure list
  | CLO_LET of string * closure * closure
  | CLO_REC_REF of closure * closure
  | CLO_REC_SET of closure * closure * closure
  | CLO_REC_DEL of closure * closure
  | CLO_SET of closure * closure
  | CLO_REF of closure
  | CLO_DEREF of closure
  | CLO_IF of closure * closure * closure
  | CLO_SEQ of closure * closure
  | CLO_WHILE of closure * closure
  | CLO_LAB of string * closure
  | CLO_BREAK of string * closure
  | CLO_TRYC of closure * string * closure
  | CLO_TRYF of closure * closure
  | CLO_THROW of closure
  | CLO_OP of opr * closure list
and value 
  = VAL_STR of string
  | VAL_NUM of int
  | VAL_ADDR of int
  | VAL_BOOL of bool
  | VAL_UNDEFN 
  | VAL_NULL
  | VAL_FUNC of string list * term * bindings
  | VAL_REC of (string * value) list

withtype bindings = value Env.env

val initial_bindings = Env.empty

fun embed_value_in_closure (VAL_STR s)
    = CLO_STR s
  | embed_value_in_closure (VAL_NUM n)
    = CLO_NUM n
  | embed_value_in_closure (VAL_ADDR a)
    = CLO_ADDR a
  | embed_value_in_closure (VAL_BOOL b)
    = CLO_BOOL b
  | embed_value_in_closure VAL_UNDEFN
    = CLO_UNDEFN
  | embed_value_in_closure VAL_NULL
    = CLO_NULL
  | embed_value_in_closure (VAL_FUNC (xs, t, bs))
    = CLO_GND (FUNC (xs, t), bs)
  | embed_value_in_closure (VAL_REC svs)
    = CLO_REC (map (fn (s, v) => (s, embed_value_in_closure v)) svs)

datatype potential_redex 
  = PR_PROP_REC of (string * term) list * bindings
  | PR_PROP_APP of term * term list * bindings
  | PR_PROP_LET of string * term * term * bindings
  | PR_PROP_REC_REF of term * term * bindings
  | PR_PROP_REC_SET of term * term * term * bindings
  | PR_PROP_REC_DEL of term * term * bindings
  | PR_PROP_SET of term * term * bindings
  | PR_PROP_REF of term * bindings
  | PR_PROP_DEREF of term * bindings
  | PR_PROP_IF of term * term * term * bindings		  
  | PR_PROP_SEQ of term * term * bindings
  | PR_PROP_WHILE of term * term * bindings
  | PR_PROP_LAB of string * term * bindings
  | PR_PROP_BREAK of string * term * bindings
  | PR_PROP_TRYC of term * string * term * bindings
  | PR_PROP_TRYF of term * term * bindings
  | PR_PROP_THROW of term * bindings
  | PR_PROP_OP of opr * term list * bindings
  | PR_VAR of string * bindings 
  | PR_LET of string * value * term * bindings
  | PR_APP of value * (value list)
  | PR_REC_REF of value * value
  | PR_REC_SET of value * value * value
  | PR_REC_DEL of value * value
  | PR_IF of value * closure * closure
  | PR_SEQ of value * closure
  | PR_WHILE of closure * closure
  | PR_TRYC_POP of value
  | PR_TRYF_POP of value * closure
  | PR_LAB_POP of value
  | PR_OP of opr * value list
  | PR_REF of value
  | PR_DEREF of value
  | PR_SET of value * value
  | PR_THROW of value
  | PR_BREAK of string * value

datatype C 
  = C_1
  | C_2  of C * string * closure
  | C_3  of C * closure list
  | C_4  of C * value * value list * closure list
  | C_5  of C * (string * value) list * string * (string * closure) list
  | C_6  of C * closure
  | C_7  of C * value
  | C_8  of C * closure * closure
  | C_9  of C * value * closure
  | C_10 of C * value * value
  | C_11 of C * closure
  | C_12 of C * value 
  | C_13 of C
  | C_14 of C
  | C_15 of C * closure
  | C_16 of C * value
  | C_17 of C * closure * closure
  | C_18 of C * closure
  | C_19 of C
  | C_20 of C * string
  | C_21 of C * opr * value list * closure list

  | C_22 of C * value
  | C_23 of C * value
  | C_24 of C * string * value

datatype D 
  = D_1
  | D_2 of D * C * closure
  | D_3 of D * C * string * closure
  | D_4 of D * C * string 

withtype sto = value Sto.sto 

datatype contractum 
  = CONTRACTUM of sto * D * C * closure

fun err str = CLO_THROW (CLO_GND (STR str, []))

exception DEAD_CLAUSE

fun contract (h, D, C, PR_PROP_REC (sts, bs))
    = CONTRACTUM (h, D, C, 
		  CLO_REC (map (fn (s, t) => (s, CLO_GND (t, bs))) sts))
  | contract (h, D, C, PR_PROP_APP (t, ts, bs))
    = CONTRACTUM (h, D, C, CLO_APP (CLO_GND (t, bs),
				    map (fn t => CLO_GND (t, bs)) ts))
  | contract (h, D, C, PR_PROP_LET (x, t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_LET (x, CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_REC_REF (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_REC_SET (t0, t1, t2, bs))
    = CONTRACTUM (h, D, C, CLO_REC_SET (CLO_GND (t0, bs),
					CLO_GND (t1, bs),
					CLO_GND (t2, bs)))
  | contract (h, D, C, PR_PROP_REC_DEL (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_SET (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_REF (t, bs))
    = CONTRACTUM (h, D, C, CLO_REF (CLO_GND (t, bs)))
  | contract (h, D, C, PR_PROP_DEREF (t, bs))
    = CONTRACTUM (h, D, C, CLO_DEREF (CLO_GND (t, bs)))
  | contract (h, D, C, PR_PROP_IF (t0, t1, t2, bs))
    = CONTRACTUM (h, D, C, CLO_IF (CLO_GND (t0, bs),
				   CLO_GND (t1, bs),
				   CLO_GND (t2, bs)))
  | contract (h, D, C, PR_PROP_SEQ (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_SEQ (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_WHILE (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_WHILE (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_LAB (l, t, bs))
    = CONTRACTUM (h, D, C, CLO_LAB (l, CLO_GND (t, bs)))
  | contract (h, D, C, PR_PROP_BREAK (l, t, bs))
    = CONTRACTUM (h, D, C, CLO_BREAK (l, CLO_GND (t, bs)))
  | contract (h, D, C, PR_PROP_TRYC (t0, x, t1, bs))
    = CONTRACTUM (h, D, C, CLO_TRYC (CLO_GND (t0, bs), x, CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_TRYF (t0, t1, bs))
    = CONTRACTUM (h, D, C, CLO_TRYF (CLO_GND (t0, bs), CLO_GND (t1, bs)))
  | contract (h, D, C, PR_PROP_THROW (t, bs))
    = CONTRACTUM (h, D, C, CLO_THROW (CLO_GND (t, bs)))
  | contract (h, D, C, PR_PROP_OP (opr, ts, bs))
    = CONTRACTUM (h, D, C, CLO_OP (opr, map (fn t => CLO_GND (t, bs)) ts))
  | contract (h, D, C, PR_VAR (x, bs))
    = CONTRACTUM (h, D, C, (embed_value_in_closure (Env.lookup (x, bs))))
  | contract (h, D, C, PR_LET (x, v, t, bs))
    = CONTRACTUM (h, D, C, CLO_GND (t, Env.extend ([x], [v], bs)))
  | contract (h, D, C, PR_APP (VAL_FUNC (xs, t, bs), vs))
    = CONTRACTUM (h, D, C, if length xs = length vs 
			   then CLO_GND (t, Env.extend (xs, vs, bs))
			   else err "Arity mismatch")
  | contract (h, D, C, PR_APP (v, vs))
    = CONTRACTUM (h, D, C, err "Not a function")
  | contract (h, D, C, PR_REC_REF (VAL_REC svs, VAL_STR s))
    = CONTRACTUM (h, D, C, 
		  if Rec.contains (svs, s) 
                  then (embed_value_in_closure (Rec.lookup (svs, s)))
                  else CLO_UNDEFN)
  | contract (h, D, C, PR_REC_REF (v0, v1))
    = CONTRACTUM (h, D, C, err "Bad record ref")
  | contract (h, D, C, PR_REC_SET (VAL_REC svs, VAL_STR s, v))
    = CONTRACTUM (h, D, C,
		  embed_value_in_closure 
                      (VAL_REC (if Rec.contains (svs, s)
                                then (Rec.update (svs, s, v))
                                else ((s, v) :: svs))))
  | contract (h, D, C, PR_REC_SET (v0, v1, v2))
    = CONTRACTUM (h, D, C, err "Bad record set")
  | contract (h, D, C, PR_REC_DEL (VAL_REC svs, VAL_STR s))
    = CONTRACTUM (h, D, C, 
		  embed_value_in_closure
                      (VAL_REC (if Rec.contains (svs, s)
                                then (Rec.remove (svs, s))
                                else svs)))
  | contract (h, D, C, PR_REC_DEL (v0, v1))
    = CONTRACTUM (h, D, C, err "Bad record del")
  | contract (h, D, C, PR_IF (VAL_BOOL b, c0, c1))
    = CONTRACTUM (h, D, C, if b then c0 else c1)
  | contract (h, D, C, PR_IF (v, c0, c1))
    = CONTRACTUM (h, D, C, err "Not a boolean")
  | contract (h, D, C, PR_SEQ (v, c))
    = CONTRACTUM (h, D, C, c)
  | contract (h, D, C, PR_WHILE (c0, c1))
    = CONTRACTUM (h, D, C,
		  CLO_IF (c0,
			  CLO_WHILE (c0, c1),
			  CLO_UNDEFN))
  | contract (h, D, C, PR_TRYC_POP v)
     = CONTRACTUM (h, D, C, embed_value_in_closure v)
  | contract (h, D, C, PR_TRYF_POP (v, c))
    = CONTRACTUM (h, D, C, CLO_SEQ (c, embed_value_in_closure v))
  | contract (h, D, C, PR_LAB_POP v)
    = CONTRACTUM (h, D, C, embed_value_in_closure v)
  | contract (h, D, C, PR_OP (PLUS, [VAL_NUM n0, VAL_NUM n1]))
    = CONTRACTUM (h, D, C, CLO_NUM (n0 + n1))
  | contract (h, D, C, PR_OP (NUM_TO_STR, [VAL_NUM n0]))
    = CONTRACTUM (h, D, C, CLO_STR (Int.toString n0))
  | contract (h, D, C, PR_OP (opr, vs))
    = CONTRACTUM (h, D, C, err "Bad primop")
  | contract (h, D, C, PR_REF v)
    = let val a = Sto.alloc h in
	  CONTRACTUM ((a, v) :: h, D, C, CLO_ADDR a)
      end
  | contract (h, D, C, PR_DEREF (VAL_ADDR a))
    = CONTRACTUM (h, D, C, 
		  case Sto.lookup (a, h)
		   of NONE
		      => err "Null pointer"
		    | SOME v
		      => embed_value_in_closure v)
  | contract (h, D, C, PR_DEREF v)
    = CONTRACTUM (h, D, C, err "Not an address")
  | contract (h, D, C, PR_SET (VAL_ADDR a, v))
    = CONTRACTUM (Sto.update (a, h, v), 
		  D, C,
		  embed_value_in_closure v)
  | contract (h, D, C, PR_SET (v0, v1))
    = CONTRACTUM (h, D, C, err "Not an address")
  | contract (h, D_1, C, PR_THROW v)
    = CONTRACTUM (h, D_1, C_1, CLO_THROW (embed_value_in_closure v))
  | contract (h, D_2 (D', C', c), C, PR_THROW v)
    = CONTRACTUM (h, D', C', CLO_SEQ (c, CLO_THROW (embed_value_in_closure v)))
  | contract (h, D_3 (D', C', x, (CLO_GND (t, bs))), C, PR_THROW v)
    = CONTRACTUM (h, D', C', (CLO_GND (t, Env.extend ([x], [v], bs))))
  | contract (h, D_3 (D', C', x, c), C, PR_THROW v)
    = raise DEAD_CLAUSE
  | contract (h, D_4 (D', C', l), C, PR_THROW v)
    = CONTRACTUM (h, D', C', CLO_THROW (embed_value_in_closure v))
  | contract (h, D_1, C, PR_BREAK (l, v))
    = CONTRACTUM (h, D_1, C_1, err "Unlabeled break")
  | contract (h, D_2 (D', C', c), C, PR_BREAK (l, v))
    = CONTRACTUM (h, D', C', CLO_SEQ (c, CLO_BREAK (l, embed_value_in_closure v)))
  | contract (h, D_3 (D', C', x, c), C, PR_BREAK (l, v))
    = CONTRACTUM (h, D', C', CLO_BREAK (l, embed_value_in_closure v))
  | contract (h, D_4 (D', C', l'), C, PR_BREAK (l, v))
    = CONTRACTUM (h, D', C', 
		  if (l' = l)
		  then embed_value_in_closure v
		  else CLO_BREAK (l, embed_value_in_closure v))

datatype ans_or_decomposition = VAL of value 
			      | ERR of value
                              | DEC of D * C * potential_redex

fun decompose_closure (CLO_GND (VAR x, bs), D, C) 
    = DEC (D, C, PR_VAR (x, bs))
  | decompose_closure (CLO_GND (STR s, bs), D, C)
    = decompose_context (D, C, (VAL_STR s))
  | decompose_closure (CLO_GND (NUM n, bs), D, C)
    = decompose_context (D, C, (VAL_NUM n))
  | decompose_closure (CLO_GND (ADDR a, bs), D, C)
    = decompose_context (D, C, (VAL_ADDR a))
  | decompose_closure (CLO_GND (BOOL b, bs), D, C)
    = decompose_context (D, C, (VAL_BOOL b))
  | decompose_closure (CLO_GND (UNDEFN, bs), D, C)
    = decompose_context (D, C, VAL_UNDEFN)
  | decompose_closure (CLO_GND (NULL, bs), D, C)
    = decompose_context (D, C, VAL_NULL)
  | decompose_closure (CLO_GND (FUNC (xs, t), bs), D, C)
    = decompose_context (D, C, VAL_FUNC (xs, t, bs))
  | decompose_closure (CLO_GND (REC sts, bs), D, C)
    = DEC (D, C, PR_PROP_REC (sts, bs))
  | decompose_closure (CLO_GND (LET (x, t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_LET (x, t0, t1, bs))
  | decompose_closure (CLO_GND (APP (t, ts), bs), D, C)
    = DEC (D, C, PR_PROP_APP (t, ts, bs))
  | decompose_closure (CLO_GND (REC_REF (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_REC_REF (t0, t1, bs))
  | decompose_closure (CLO_GND (REC_SET (t0, t1, t2), bs), D, C)
    = DEC (D, C, PR_PROP_REC_SET (t0, t1, t2, bs))
  | decompose_closure (CLO_GND (REC_DEL (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_REC_DEL (t0, t1, bs)) 
  | decompose_closure (CLO_GND (SET (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_SET (t0, t1, bs)) 
  | decompose_closure (CLO_GND (REF t, bs), D, C)
    = DEC (D, C, PR_PROP_REF (t, bs))
  | decompose_closure (CLO_GND (DEREF t, bs), D, C)
    = DEC (D, C, PR_PROP_DEREF (t, bs))
  | decompose_closure (CLO_GND (IF (t0, t1, t2), bs), D, C)
    = DEC (D, C, PR_PROP_IF (t0, t1, t2, bs))
  | decompose_closure (CLO_GND (SEQ (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_SEQ (t0, t1, bs))
  | decompose_closure (CLO_GND (WHILE (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_WHILE (t0, t1, bs))
  | decompose_closure (CLO_GND (LAB (l, t), bs), D, C)
    = DEC (D, C, PR_PROP_LAB (l, t, bs))
  | decompose_closure (CLO_GND (BREAK (l, t), bs), D, C)
    = DEC (D, C, PR_PROP_BREAK (l, t, bs))
  | decompose_closure (CLO_GND (TRYC (t0, x, t1), bs), D, C)
    = DEC (D, C, PR_PROP_TRYC (t0, x, t1, bs))
  | decompose_closure (CLO_GND (TRYF (t0, t1), bs), D, C)
    = DEC (D, C, PR_PROP_TRYF (t0, t1, bs))
  | decompose_closure (CLO_GND (THROW t, bs), D, C)
    = DEC (D, C, PR_PROP_THROW (t, bs))
  | decompose_closure (CLO_GND (OP (opr, ts), bs), D, C)
    = DEC (D, C, PR_PROP_OP (opr, ts, bs))
  | decompose_closure (CLO_STR s, D, C)
    = decompose_context (D, C, VAL_STR s)
  | decompose_closure (CLO_NUM n, D, C) 
    = decompose_context (D, C, VAL_NUM n)
  | decompose_closure (CLO_ADDR a, D, C)
    = decompose_context (D, C, VAL_ADDR a)
  | decompose_closure (CLO_BOOL b, D, C)
    = decompose_context (D, C, VAL_BOOL b)
  | decompose_closure (CLO_UNDEFN, D, C)
    = decompose_context (D, C, VAL_UNDEFN)
  | decompose_closure (CLO_NULL, D, C)
    = decompose_context (D, C, VAL_NULL)
  | decompose_closure (CLO_REC [], D, C)
    = decompose_context (D, C, VAL_REC [])
  | decompose_closure (CLO_REC ((s, c) :: scs), D, C)
    = decompose_closure (c, D, C_5 (C, [], s, scs))
  | decompose_closure (CLO_APP (c, cs), D, C)
    = decompose_closure (c, D, C_3 (C, cs))
  | decompose_closure (CLO_LET (x, c0, c1), D, C)
    = decompose_closure (c0, D, C_2 (C, x, c1))
  | decompose_closure (CLO_REC_REF (c0, c1), D, C)
    = decompose_closure (c0, D, C_6 (C, c1))
  | decompose_closure (CLO_REC_SET (c0, c1, c2), D, C)
    = decompose_closure (c0, D, C_8 (C, c1, c2))
  | decompose_closure (CLO_REC_DEL (c0, c1), D, C)
    = decompose_closure (c0, D, C_11 (C, c1))
  | decompose_closure (CLO_SET (c0, c1), D, C)
    = decompose_closure (c0, D, C_15 (C, c1))
  | decompose_closure (CLO_REF c, D, C)
    = decompose_closure (c, D, C_13 C)
  | decompose_closure (CLO_DEREF c, D, C)
    = decompose_closure (c, D, C_14 C)
  | decompose_closure (CLO_IF (c0, c1, c2), D, C)
    = decompose_closure (c0, D, C_17 (C, c1, c2))
  | decompose_closure (CLO_SEQ (c0, c1), D, C)
    = decompose_closure (c0, D, C_18 (C, c1))
  | decompose_closure (CLO_WHILE (c0, c1), D, C)
    = DEC (D, C, PR_WHILE (c0, c1))
  | decompose_closure (CLO_LAB (l, c), D, C)
    = decompose_closure (c, D_4 (D, C, l), C_1)
  | decompose_closure (CLO_BREAK (l, c), D, C)
    = decompose_closure (c, D, C_20 (C, l))
  | decompose_closure (CLO_TRYC (c0, x, c1), D, C)
    = decompose_closure (c0, D_3 (D, C, x, c1), C_1)
  | decompose_closure (CLO_TRYF (c0, c1), D, C)
    = decompose_closure (c0, D_2 (D, C, c1), C_1)
  | decompose_closure (CLO_THROW c, D, C)
    = decompose_closure (c, D, C_19 C)
  | decompose_closure (CLO_OP (opr, []), D, C)
    = DEC (D, C, PR_OP (opr, []))
  | decompose_closure (CLO_OP (opr, (c :: cs)), D, C)
    = decompose_closure (c, D, C_21 (C, opr, [], cs))

and decompose_context (D_1, C_1, v)
    = VAL v
  | decompose_context (D_2 (D, C, c), C_1, v)
    = DEC (D, C, PR_TRYF_POP (v, c))
  | decompose_context (D_3 (D, C, x, c), C_1, v)
    = DEC (D, C, PR_TRYC_POP v)
  | decompose_context (D_4 (D, C, l), C_1, v)
    = DEC (D, C, PR_LAB_POP v)
  | decompose_context (D, C_2 (C, x, CLO_GND (t, bs)), v)
    = DEC (D, C, PR_LET (x, v, t, bs))
  | decompose_context (D, C_2 (C, x, c), v)
    = raise DEAD_CLAUSE
  | decompose_context (D, C_3 (C, []), v)
    = DEC (D, C, PR_APP (v, []))
  | decompose_context (D, C_3 (C, c :: cs), v)
    = decompose_closure (c, D, C_4 (C, v, [], cs))
  | decompose_context (D, C_4 (C, v0, vs, []), v)
    = DEC (D, C, PR_APP (v, vs @ [v]))
  | decompose_context (D, C_4 (C, v0, vs, c :: cs), v)
    = decompose_closure (c, D, C_4 (C, v0, vs @ [v], cs))
  | decompose_context (D, C_5 (C, svs, s, []), v)
    = decompose_context (D, C, VAL_REC (svs @ [(s, v)]))
  | decompose_context (D, C_5 (C, svs, s0, (s, c) :: scs), v)
    = decompose_closure (c, D, C_5 (C, svs @ [(s0, v)], s, scs))
  | decompose_context (D, C_6 (C, c), v)
    = decompose_closure (c, D, C_7 (C, v))
  | decompose_context (D, C_7 (C, v0), v)
    = DEC (D, C, PR_REC_REF (v0, v))
  | decompose_context (D, C_8 (C, c0, c1), v)
    = decompose_closure (c0, D, C_9 (C, v, c1))
  | decompose_context (D, C_9 (C, v0, c), v)
    = decompose_closure (c, D, C_10 (C, v0, v))
  | decompose_context (D, C_10 (C, v0, v1), v)
    = DEC (D, C, PR_REC_SET (v0, v1, v))
  | decompose_context (D, C_11 (C, c), v)
    = decompose_closure (c, D, C_12 (C, v))
  | decompose_context (D, C_12 (C, v0), v)
    = DEC (D, C, PR_REC_DEL (v0, v))
  | decompose_context (D, C_13 C, v)
    = DEC (D, C, PR_REF v)
  | decompose_context (D, C_14 C, v)
    = DEC (D, C, PR_DEREF v)
  | decompose_context (D, C_15 (C, c), v)
    = decompose_closure (c, D, C_16 (C, v))
  | decompose_context (D, C_16 (C, v0), v)
    = DEC (D, C, PR_SET (v0, v))
  | decompose_context (D, C_17 (C, c0, c1), v)
    = DEC (D, C, PR_IF (v, c0, c1))
  | decompose_context (D, C_18 (C, c), v)
    = DEC (D, C, PR_SEQ (v, c))
  | decompose_context (D_1, C_19 C, v)
    = ERR v
  | decompose_context (D, C_19 C, v)
    = DEC (D, C, PR_THROW v)
  | decompose_context (D, C_20 (C, l), v)
    = DEC (D, C, PR_BREAK (l, v))
  | decompose_context (D, C_21 (C, opr, vs, []), v)
    = DEC (D, C, PR_OP (opr, vs @ [v]))
  | decompose_context (D, C_21 (C, opr, vs, c :: cs), v)
    = decompose_closure (c, D, C_21 (C, opr, vs @ [v], cs))

fun decompose c 
    = decompose_closure (c, D_1, C_1)

fun recompose (D_1, C_1, c)
    = c
  | recompose (D_2 (D, C, c1), C_1, c0)
    = recompose (D, C, CLO_TRYF (c0, c1))
  | recompose (D_3 (D, C, x, c1), C_1, c0)
    = recompose (D, C, CLO_TRYC (c0, x, c1))
  | recompose (D_4 (D, C, l), C_1, c)
    = recompose (D, C, CLO_LAB (l, c))
  | recompose (D, C_2 (C, x, c1), c0)
    = recompose (D, C, CLO_LET (x, c0, c1))
  | recompose (D, C_3 (C, cs), c)
    = recompose (D, C, CLO_APP (c, cs))
  | recompose (D, C_4 (C, v, vs, cs), c)
    = recompose (D, C, CLO_APP (embed_value_in_closure v,
				(map embed_value_in_closure vs) @ [c] @ cs))
  | recompose (D, C_5 (C, svs, s, scs), c)
    = recompose (D, C, CLO_REC ((map (fn (s, v) => (s, embed_value_in_closure v)) svs)
				@ [(s, c)]
				@ scs))
  | recompose (D, C_6 (C, c1), c0)
    = recompose (D, C, CLO_REC_REF (c0, c1))
  | recompose (D, C_7 (C, v), c)
    = recompose (D, C, CLO_REC_REF (embed_value_in_closure v, c))
  | recompose (D, C_8 (C, c1, c2), c0)
    = recompose (D, C, CLO_REC_SET (c0, c1, c2))
  | recompose (D, C_9 (C, v, c1), c0)
    = recompose (D, C, CLO_REC_SET (embed_value_in_closure v, c0, c1))
  | recompose (D, C_10 (C, v0, v1), c)
    = recompose (D, C, CLO_REC_SET (embed_value_in_closure v0,
				    embed_value_in_closure v1,
				    c))
  | recompose (D, C_11 (C, c1), c0)
    = recompose (D, C, CLO_REC_DEL (c0, c1))
  | recompose (D, C_12 (C, v), c)
    = recompose (D, C, CLO_REC_DEL (embed_value_in_closure v, c))
  | recompose (D, C_13 C, c)
    = recompose (D, C, CLO_REF c)
  | recompose (D, C_14 C, c)
    = recompose (D, C, CLO_DEREF c)
  | recompose (D, C_15 (C, c1), c0)
    = recompose (D, C, CLO_SET (c0, c1))
  | recompose (D, C_16 (C, v), c)
    = recompose (D, C, CLO_SET (embed_value_in_closure v, c))
  | recompose (D, C_17 (C, c1, c2), c0)
    = recompose (D, C, CLO_IF (c0, c1, c2))
  | recompose (D, C_18 (C, c1), c0)
    = recompose (D, C, CLO_SEQ (c0, c1))
  | recompose (D, C_19 C, c)
    = recompose (D, C, CLO_THROW c)
  | recompose (D, C_20 (C, l), c)
    = recompose (D, C, CLO_LAB (l, c))
  | recompose (D, C_21 (C, opr, vs, cs), c)
    = recompose (D, C, CLO_OP (opr, (map embed_value_in_closure vs) @ [c] @ cs))

datatype result = RESULT of value * sto
		| ERROR of value * sto

fun iterate0 (h, VAL v)
    = RESULT (v, h)
  | iterate0 (h, ERR v)
    = ERROR (v, h)
  | iterate0 (h, DEC (D, C, pr))
    = (case contract (h, D, C, pr)
        of (CONTRACTUM (h', D', C', c'))
           => iterate0 (h', decompose (recompose (D', C', c'))))

fun normalize0 t
  = iterate0 ([], decompose (CLO_GND (t, [])))
    
fun normalize0' t
  = iterate0 ([], decompose (recompose (D_1, C_1, (CLO_GND (t, [])))))

(* ************************************************************************** *)

fun refocus (D, C, c)
    = decompose_closure (c, D, C)

fun iterate1 (h, VAL v) 
    = RESULT (v, h)
  | iterate1 (h, ERR v)
    = ERROR (v, h)
  | iterate1 (h, DEC (D, C, pr))
    = (case contract (h, D, C, pr)
        of (CONTRACTUM (h', D', C', c'))
           => iterate1 (h', refocus (D', C', c')))

fun normalize1 t
    = iterate1 ([], refocus (D_1, C_1, CLO_GND (t, [])))

(* ************************************************************************** *)

(* Calls to contract are inlined in iterate. *)

fun iterate2 (h, VAL v) 
    = RESULT (v, h)
  | iterate2 (h, ERR v)
    = ERROR (v, h)
  | iterate2 (h, DEC (D, C, PR_PROP_REC (sts, bs)))
    = iterate2 (h, (refocus (D, C, CLO_REC (map (fn (s, t) => (s, CLO_GND (t, bs))) sts))))
  | iterate2 (h, DEC (D, C, PR_PROP_APP (t, ts, bs)))
    = iterate2 (h, (refocus (D, C, CLO_APP (CLO_GND (t, bs),
					    map (fn t => CLO_GND (t, bs)) ts))))
  | iterate2 (h, DEC (D, C, PR_PROP_LET (x, t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_LET (x, CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_REC_REF (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_REC_SET (t0, t1, t2, bs)))
    = iterate2 (h, (refocus (D, C, CLO_REC_SET (CLO_GND (t0, bs),
						CLO_GND (t1, bs),
						CLO_GND (t2, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_REC_DEL (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_SET (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_REF (t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_REF (CLO_GND (t, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_DEREF (t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_DEREF (CLO_GND (t, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_IF (t0, t1, t2, bs)))
    = iterate2 (h, (refocus (D, C, CLO_IF (CLO_GND (t0, bs),
					   CLO_GND (t1, bs),
					   CLO_GND (t2, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_SEQ (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_SEQ (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_WHILE (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_WHILE (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_LAB (l, t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_LAB (l, CLO_GND (t, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_BREAK (l, t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_BREAK (l, CLO_GND (t, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_TRYC (t0, x, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_TRYC (CLO_GND (t0, bs), x, CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_TRYF (t0, t1, bs)))
    = iterate2 (h, (refocus (D, C, CLO_TRYF (CLO_GND (t0, bs), CLO_GND (t1, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_THROW (t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_THROW (CLO_GND (t, bs)))))
  | iterate2 (h, DEC (D, C, PR_PROP_OP (opr, ts, bs)))
    = iterate2 (h, (refocus (D, C, CLO_OP (opr, map (fn t => CLO_GND (t, bs)) ts))))
  | iterate2 (h, DEC (D, C, PR_VAR (x, bs)))
    = iterate2 (h, (refocus (D, C, (embed_value_in_closure (Env.lookup (x, bs))))))
  | iterate2 (h, DEC (D, C, PR_LET (x, v, t, bs)))
    = iterate2 (h, (refocus (D, C, CLO_GND (t, Env.extend ([x], [v], bs)))))
  | iterate2 (h, DEC (D, C, PR_APP (VAL_FUNC (xs, t, bs), vs)))
    = iterate2 (h, (refocus (D, C, if length xs = length vs 
				   then CLO_GND (t, Env.extend (xs, vs, bs))
				   else err "Arity mismatch")))
  | iterate2 (h, DEC (D, C, PR_APP (v, vs)))
    = iterate2 (h, (refocus (D, C, err "Not a function")))
  | iterate2 (h, DEC (D, C, PR_REC_REF (VAL_REC svs, VAL_STR s)))
    = iterate2 (h, (refocus (D, C, 
			     if Rec.contains (svs, s) 
			     then (embed_value_in_closure (Rec.lookup (svs, s)))
			     else CLO_UNDEFN)))
  | iterate2 (h, DEC (D, C, PR_REC_REF (v0, v1)))
    = iterate2 (h, (refocus (D, C, err "Bad record ref")))
  | iterate2 (h, DEC (D, C, PR_REC_SET (VAL_REC svs, VAL_STR s, v)))
    = iterate2 (h, (refocus (D, C,
			     embed_value_in_closure 
				 (VAL_REC (if Rec.contains (svs, s)
					   then (Rec.update (svs, s, v))
					   else ((s, v) :: svs))))))
  | iterate2 (h, DEC (D, C, PR_REC_SET (v0, v1, v2)))
    = iterate2 (h, (refocus (D, C, err "Bad record set")))
  | iterate2 (h, DEC (D, C, PR_REC_DEL (VAL_REC svs, VAL_STR s)))
    = iterate2 (h, (refocus (D, C, 
			     embed_value_in_closure
				 (VAL_REC (if Rec.contains (svs, s)
					   then (Rec.remove (svs, s))
					   else svs)))))
  | iterate2 (h, DEC (D, C, PR_REC_DEL (v0, v1)))
    = iterate2 (h, (refocus (D, C, err "Bad record del")))
  | iterate2 (h, DEC (D, C, PR_IF (VAL_BOOL b, c0, c1)))
    = iterate2 (h, (refocus (D, C, if b then c0 else c1)))
  | iterate2 (h, DEC (D, C, PR_IF (v, c0, c1)))
    = iterate2 (h, (refocus (D, C, err "Not a boolean")))
  | iterate2 (h, DEC (D, C, PR_SEQ (v, c)))
    = iterate2 (h, (refocus (D, C, c)))
  | iterate2 (h, DEC (D, C, PR_WHILE (c0, c1)))
    = iterate2 (h, (refocus (D, C,
			     CLO_IF (c0,
				     CLO_WHILE (c0, c1),
				     CLO_UNDEFN))))
  | iterate2 (h, DEC (D, C, PR_TRYC_POP v))
    = iterate2 (h, (refocus (D, C, embed_value_in_closure v)))
  | iterate2 (h, DEC (D, C, PR_TRYF_POP (v, c)))
    = iterate2 (h, (refocus (D, C, CLO_SEQ (c, embed_value_in_closure v))))
  | iterate2 (h, DEC (D, C, PR_LAB_POP v))
    = iterate2 (h, (refocus (D, C, embed_value_in_closure v)))
  | iterate2 (h, DEC (D, C, PR_OP (PLUS, [VAL_NUM n0, VAL_NUM n1])))
    = iterate2 (h, (refocus (D, C, CLO_NUM (n0 + n1))))
  | iterate2 (h, DEC (D, C, PR_OP (NUM_TO_STR, [VAL_NUM n0])))
    = iterate2 (h, (refocus (D, C, CLO_STR (Int.toString n0))))
  | iterate2 (h, DEC (D, C, PR_OP (opr, vs)))
    = iterate2 (h, (refocus (D, C, err "Bad primop")))
  | iterate2 (h, DEC (D, C, PR_REF v))
    = let val a = Sto.alloc h in
	  iterate2 ((a, v) :: h, (refocus (D, C, CLO_ADDR a)))
      end
  | iterate2 (h, DEC (D, C, PR_DEREF (VAL_ADDR a)))
    = iterate2 (h, (refocus (D, C, 
			     case Sto.lookup (a, h)
			      of NONE
				 => err "Null pointer"
			       | SOME v
				 => embed_value_in_closure v)))
  | iterate2 (h, DEC (D, C, PR_DEREF v))
    = iterate2 (h, (refocus (D, C, err "Not an address")))
  | iterate2 (h, DEC (D, C, PR_SET (VAL_ADDR a, v)))
    = iterate2 (Sto.update (a, h, v), 
		(refocus (D, C, embed_value_in_closure v)))
  | iterate2 (h, DEC (D, C, PR_SET (v0, v1)))
    = iterate2 (h, (refocus (D, C, err "Not an address")))
  | iterate2 (h, DEC (D_1, C, PR_THROW v))
    = iterate2 (h, (refocus (D_1, C_1, CLO_THROW (embed_value_in_closure v))))
  | iterate2 (h, DEC (D_2 (D', C', c), C, PR_THROW v))
    = iterate2 (h, (refocus (D', C', CLO_SEQ (c, CLO_THROW (embed_value_in_closure v)))))
  | iterate2 (h, DEC (D_3 (D', C', x, (CLO_GND (t, bs))), C, PR_THROW v))
    = iterate2 (h, (refocus (D', C', (CLO_GND (t, Env.extend ([x], [v], bs))))))
  | iterate2 (h, DEC (D_3 (D', C', x, c), C, PR_THROW v))
    = raise DEAD_CLAUSE
  | iterate2 (h, DEC (D_4 (D', C', l), C, PR_THROW v))
    = iterate2 (h, (refocus (D', C', CLO_THROW (embed_value_in_closure v))))
  | iterate2 (h, DEC (D_1, C, PR_BREAK (l, v)))
    = iterate2 (h, (refocus (D_1, C_1, err "Unlabeled break")))
  | iterate2 (h, DEC (D_2 (D', C', c), C, PR_BREAK (l, v)))
    = iterate2 (h, (refocus (D', C', CLO_SEQ (c, CLO_BREAK (l, embed_value_in_closure v)))))
  | iterate2 (h, DEC (D_3 (D', C', x, c), C, PR_BREAK (l, v)))
    = iterate2 (h, (refocus (D', C', CLO_BREAK (l, embed_value_in_closure v))))
  | iterate2 (h, DEC (D_4 (D', C', l'), C, PR_BREAK (l, v)))
    = iterate2 (h, (refocus (D', C', if (l' = l)
				     then embed_value_in_closure v
				     else CLO_BREAK (l, embed_value_in_closure v))))

(* ************************************************************************** *)

(* Lightweight fusion. *)

(* Fuse iterate and refocus (i.e., decompose_closure and decompose_context) 
   so that the resulting iterate function is directly applied to the result
   of decompose_closure and decompose_context. *)

(* Stores are threaded through. *)

(* refocus3_closure is the composition of iterate2 and
   decompose_closure and a clone of decompose_closure. *)

(* refocus3_context is the composition of iterate2 and
   decompose_context that directly calls iterate3 over a value or a
   decomposition instead of return it to iterate2 as decompose_context
   did. *)

(* iterate3 is a clone of iterate2 taht calls the fused function
   refocus3_closure. *)

fun refocus3_closure (h, CLO_GND (VAR x, bs), D, C)
    = iterate3 (h, DEC (D, C, PR_VAR (x, bs)))
  | refocus3_closure (h, CLO_GND (STR s, bs), D, C)
    = refocus3_context (h, D, C, (VAL_STR s))
  | refocus3_closure (h, CLO_GND (NUM n, bs), D, C)
    = refocus3_context (h, D, C, (VAL_NUM n))
  | refocus3_closure (h, CLO_GND (ADDR a, bs), D, C)
    = refocus3_context (h, D, C, (VAL_ADDR a))
  | refocus3_closure (h, CLO_GND (BOOL b, bs), D, C)
    = refocus3_context (h, D, C, (VAL_BOOL b))
  | refocus3_closure (h, CLO_GND (UNDEFN, bs), D, C)
    = refocus3_context (h, D, C, VAL_UNDEFN)
  | refocus3_closure (h, CLO_GND (NULL, bs), D, C)
    = refocus3_context (h, D, C, VAL_NULL)
  | refocus3_closure (h, CLO_GND (FUNC (xs, t), bs), D, C)
    = refocus3_context (h, D, C, VAL_FUNC (xs, t, bs))
  | refocus3_closure (h, CLO_GND (REC sts, bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_REC (sts, bs)))
  | refocus3_closure (h, CLO_GND (LET (x, t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_LET (x, t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (APP (t, ts), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_APP (t, ts, bs)))
  | refocus3_closure (h, CLO_GND (REC_REF (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_REC_REF (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (REC_SET (t0, t1, t2), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_REC_SET (t0, t1, t2, bs)))
  | refocus3_closure (h, CLO_GND (REC_DEL (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_REC_DEL (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (SET (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_SET (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (REF t, bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_REF (t, bs)))
  | refocus3_closure (h, CLO_GND (DEREF t, bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_DEREF (t, bs)))
  | refocus3_closure (h, CLO_GND (IF (t0, t1, t2), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_IF (t0, t1, t2, bs)))
  | refocus3_closure (h, CLO_GND (SEQ (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_SEQ (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (WHILE (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_WHILE (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (LAB (l, t), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_LAB (l, t, bs)))
  | refocus3_closure (h, CLO_GND (BREAK (l, t), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_BREAK (l, t, bs)))
  | refocus3_closure (h, CLO_GND (TRYC (t0, x, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_TRYC (t0, x, t1, bs)))
  | refocus3_closure (h, CLO_GND (TRYF (t0, t1), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_TRYF (t0, t1, bs)))
  | refocus3_closure (h, CLO_GND (THROW t, bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_THROW (t, bs)))
  | refocus3_closure (h, CLO_GND (OP (opr, ts), bs), D, C)
    = iterate3 (h, DEC (D, C, PR_PROP_OP (opr, ts, bs)))
  | refocus3_closure (h, CLO_STR s, D, C)
    = refocus3_context (h, D, C, VAL_STR s)
  | refocus3_closure (h, CLO_NUM n, D, C) 
    = refocus3_context (h, D, C, VAL_NUM n)
  | refocus3_closure (h, CLO_ADDR a, D, C)
    = refocus3_context (h, D, C, VAL_ADDR a)
  | refocus3_closure (h, CLO_BOOL b, D, C)
    = refocus3_context (h, D, C, VAL_BOOL b)
  | refocus3_closure (h, CLO_UNDEFN, D, C)
    = refocus3_context (h, D, C, VAL_UNDEFN)
  | refocus3_closure (h, CLO_NULL, D, C)
    = refocus3_context (h, D, C, VAL_NULL)
  | refocus3_closure (h, CLO_REC [], D, C)
    = refocus3_context (h, D, C, VAL_REC [])
  | refocus3_closure (h, CLO_REC ((s, c) :: scs), D, C)
    = refocus3_closure (h, c, D, C_5 (C, [], s, scs))
  | refocus3_closure (h, CLO_APP (c, cs), D, C)
    = refocus3_closure (h, c, D, C_3 (C, cs))
  | refocus3_closure (h, CLO_LET (x, c0, c1), D, C)
    = refocus3_closure (h, c0, D, C_2 (C, x, c1))
  | refocus3_closure (h, CLO_REC_REF (c0, c1), D, C)
    = refocus3_closure (h, c0, D, C_6 (C, c1))
  | refocus3_closure (h, CLO_REC_SET (c0, c1, c2), D, C)
    = refocus3_closure (h, c0, D, C_8 (C, c1, c2))
  | refocus3_closure (h, CLO_REC_DEL (c0, c1), D, C)
    = refocus3_closure (h, c0, D, C_11 (C, c1))
  | refocus3_closure (h, CLO_SET (c0, c1), D, C)
    = refocus3_closure (h, c0, D, C_15 (C, c1))
  | refocus3_closure (h, CLO_REF c, D, C)
    = refocus3_closure (h, c, D, C_13 C)
  | refocus3_closure (h, CLO_DEREF c, D, C)
    = refocus3_closure (h, c, D, C_14 C)
  | refocus3_closure (h, CLO_IF (c0, c1, c2), D, C)
    = refocus3_closure (h, c0, D, C_17 (C, c1, c2))
  | refocus3_closure (h, CLO_SEQ (c0, c1), D, C)
    = refocus3_closure (h, c0, D, C_18 (C, c1))
  | refocus3_closure (h, CLO_WHILE (c0, c1), D, C)
    = iterate3 (h, DEC (D, C, PR_WHILE (c0, c1)))
  | refocus3_closure (h, CLO_LAB (l, c), D, C)
    = refocus3_closure (h, c, D_4 (D, C, l), C_1)
  | refocus3_closure (h, CLO_BREAK (l, c), D, C)
    = refocus3_closure (h, c, D, C_20 (C, l))
  | refocus3_closure (h, CLO_TRYC (c0, x, c1), D, C)
    = refocus3_closure (h, c0, D_3 (D, C, x, c1), C_1)
  | refocus3_closure (h, CLO_TRYF (c0, c1), D, C)
    = refocus3_closure (h, c0, D_2 (D, C, c1), C_1)
  | refocus3_closure (h, CLO_THROW c, D, C)
    = refocus3_closure (h, c, D, C_19 C)
  | refocus3_closure (h, CLO_OP (opr, []), D, C)
    = iterate3 (h, DEC (D, C, PR_OP (opr, [])))
  | refocus3_closure (h, CLO_OP (opr, (c :: cs)), D, C)
    = refocus3_closure (h, c, D, C_21 (C, opr, [], cs))

and refocus3_context (h, D_1, C_1, v)
    = iterate3 (h, VAL v)
  | refocus3_context (h, D_2 (D, C, c), C_1, v)
    = iterate3 (h, DEC (D, C, PR_TRYF_POP (v, c)))
  | refocus3_context (h, D_3 (D, C, x, c), C_1, v)
    = iterate3 (h, DEC (D, C, PR_TRYC_POP v))
  | refocus3_context (h, D_4 (D, C, l), C_1, v)
    = iterate3 (h, DEC (D, C, PR_LAB_POP v))
  | refocus3_context (h, D, C_2 (C, x, CLO_GND (t, bs)), v)
    = iterate3 (h, DEC (D, C, PR_LET (x, v, t, bs)))
  | refocus3_context (h, D, C_2 (C, x, c), v)
    = raise DEAD_CLAUSE
  | refocus3_context (h, D, C_3 (C, []), v)
    = iterate3 (h, DEC (D, C, PR_APP (v, [])))
  | refocus3_context (h, D, C_3 (C, c :: cs), v)
    = refocus3_closure (h, c, D, C_4 (C, v, [], cs))
  | refocus3_context (h, D, C_4 (C, v0, vs, []), v)
    = iterate3 (h, DEC (D, C, PR_APP (v0, vs @ [v])))
  | refocus3_context (h, D, C_4 (C, v0, vs, c :: cs), v)
    = refocus3_closure (h, c, D, C_4 (C, v0, vs @ [v], cs))
  | refocus3_context (h, D, C_5 (C, svs, s, []), v)
    = refocus3_context (h, D, C, VAL_REC (svs @ [(s, v)]))
  | refocus3_context (h, D, C_5 (C, svs, s0, (s, c) :: scs), v)
    = refocus3_closure (h, c, D, C_5 (C, svs @ [(s0, v)], s, scs))
  | refocus3_context (h, D, C_6 (C, c), v)
    = refocus3_closure (h, c, D, C_7 (C, v))
  | refocus3_context (h, D, C_7 (C, v0), v)
    = iterate3 (h, DEC (D, C, PR_REC_REF (v0, v)))
  | refocus3_context (h, D, C_8 (C, c0, c1), v)
    = refocus3_closure (h, c0, D, C_9 (C, v, c1))
  | refocus3_context (h, D, C_9 (C, v0, c), v)
    = refocus3_closure (h, c, D, C_10 (C, v0, v))
  | refocus3_context (h, D, C_10 (C, v0, v1), v)
    = iterate3 (h, DEC (D, C, PR_REC_SET (v0, v1, v)))
  | refocus3_context (h, D, C_11 (C, c), v)
    = refocus3_closure (h, c, D, C_12 (C, v))
  | refocus3_context (h, D, C_12 (C, v0), v)
    = iterate3 (h, DEC (D, C, PR_REC_DEL (v0, v)))
  | refocus3_context (h, D, C_13 C, v)
    = iterate3 (h, DEC (D, C, PR_REF v))
  | refocus3_context (h, D, C_14 C, v)
    = iterate3 (h, DEC (D, C, PR_DEREF v))
  | refocus3_context (h, D, C_15 (C, c), v)
    = refocus3_closure (h, c, D, C_16 (C, v))
  | refocus3_context (h, D, C_16 (C, v0), v)
    = iterate3 (h, DEC (D, C, PR_SET (v0, v)))
  | refocus3_context (h, D, C_17 (C, c0, c1), v)
    = iterate3 (h, DEC (D, C, PR_IF (v, c0, c1)))
  | refocus3_context (h, D, C_18 (C, c), v)
    = iterate3 (h, DEC (D, C, PR_SEQ (v, c)))
  | refocus3_context (h, D_1, C_19 C, v)
    = iterate3 (h, ERR v)
  | refocus3_context (h, D, C_19 C, v)
    = iterate3 (h, DEC (D, C, PR_THROW v))
  | refocus3_context (h, D, C_20 (C, l), v)
    = iterate3 (h, DEC (D, C, PR_BREAK (l, v)))
  | refocus3_context (h, D, C_21 (C, opr, vs, []), v)
    = iterate3 (h, DEC (D, C, PR_OP (opr, vs @ [v])))
  | refocus3_context (h, D, C_21 (C, opr, vs, c :: cs), v)
    = refocus3_closure (h, c, D, C_21 (C, opr, vs @ [v], cs))

and iterate3 (h, VAL v) 
    = RESULT (v, h)
  | iterate3 (h, ERR v)
    = ERROR (v, h)
  | iterate3 (h, DEC (D, C, PR_PROP_REC (sts, bs)))
    = refocus3_closure (h, CLO_REC (map (fn (s, t) => (s, CLO_GND (t, bs))) sts), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_APP (t, ts, bs)))
    = refocus3_closure (h, CLO_APP (CLO_GND (t, bs),
				    map (fn t => CLO_GND (t, bs)) ts), 
			D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_LET (x, t0, t1, bs)))
    = refocus3_closure (h, CLO_LET (x, CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_REC_REF (t0, t1, bs)))
    = refocus3_closure (h, CLO_REC_REF (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_REC_SET (t0, t1, t2, bs)))
    = refocus3_closure (h, CLO_REC_SET (CLO_GND (t0, bs),
						CLO_GND (t1, bs),
						CLO_GND (t2, bs)),
			D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_REC_DEL (t0, t1, bs)))
    = refocus3_closure (h, CLO_REC_DEL (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_SET (t0, t1, bs)))
    = refocus3_closure (h, CLO_SET (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_REF (t, bs)))
    = refocus3_closure (h, CLO_REF (CLO_GND (t, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_DEREF (t, bs)))
    = refocus3_closure (h, CLO_DEREF (CLO_GND (t, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_IF (t0, t1, t2, bs)))
    = refocus3_closure (h, CLO_IF (CLO_GND (t0, bs),
				   CLO_GND (t1, bs),
				   CLO_GND (t2, bs)), 
			D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_SEQ (t0, t1, bs)))
    = refocus3_closure (h, CLO_SEQ (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_WHILE (t0, t1, bs)))
    = refocus3_closure (h, CLO_WHILE (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_LAB (l, t, bs)))
    = refocus3_closure (h, CLO_LAB (l, CLO_GND (t, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_BREAK (l, t, bs)))
    = refocus3_closure (h, CLO_BREAK (l, CLO_GND (t, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_TRYC (t0, x, t1, bs)))
    = refocus3_closure (h, CLO_TRYC (CLO_GND (t0, bs), x, CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_TRYF (t0, t1, bs)))
    = refocus3_closure (h, CLO_TRYF (CLO_GND (t0, bs), CLO_GND (t1, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_THROW (t, bs)))
    = refocus3_closure (h, CLO_THROW (CLO_GND (t, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_PROP_OP (opr, ts, bs)))
    = refocus3_closure (h, CLO_OP (opr, map (fn t => CLO_GND (t, bs)) ts), D, C)
  | iterate3 (h, DEC (D, C, PR_VAR (x, bs)))
    = refocus3_closure (h, embed_value_in_closure (Env.lookup (x, bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_LET (x, v, t, bs)))
    = refocus3_closure (h, CLO_GND (t, Env.extend ([x], [v], bs)), D, C)
  | iterate3 (h, DEC (D, C, PR_APP (VAL_FUNC (xs, t, bs), vs)))
    = refocus3_closure (h, if length xs = length vs 
			   then CLO_GND (t, Env.extend (xs, vs, bs))
			   else err "Arity mismatch",
			D, C)
  | iterate3 (h, DEC (D, C, PR_APP (v, vs)))
    = refocus3_closure (h, err "Not a function", D, C)
  | iterate3 (h, DEC (D, C, PR_REC_REF (VAL_REC svs, VAL_STR s)))
    = refocus3_closure (h, if Rec.contains (svs, s) 
			   then (embed_value_in_closure (Rec.lookup (svs, s)))
			   else CLO_UNDEFN,
			D, C)
  | iterate3 (h, DEC (D, C, PR_REC_REF (v0, v1)))
    = refocus3_closure (h, err "Bad record ref", D, C)
  | iterate3 (h, DEC (D, C, PR_REC_SET (VAL_REC svs, VAL_STR s, v)))
    = refocus3_closure (h, embed_value_in_closure 
			       (VAL_REC (if Rec.contains (svs, s)
					 then (Rec.update (svs, s, v))
					 else ((s, v) :: svs))),
			D, C)
  | iterate3 (h, DEC (D, C, PR_REC_SET (v0, v1, v2)))
    = refocus3_closure (h, err "Bad record set", D, C)
  | iterate3 (h, DEC (D, C, PR_REC_DEL (VAL_REC svs, VAL_STR s)))
    = refocus3_closure (h, embed_value_in_closure
			       (VAL_REC (if Rec.contains (svs, s)
					 then (Rec.remove (svs, s))
					 else svs)),
			D, C)
  | iterate3 (h, DEC (D, C, PR_REC_DEL (v0, v1)))
    = refocus3_closure (h, err "Bad record del", D, C)
  | iterate3 (h, DEC (D, C, PR_IF (VAL_BOOL b, c0, c1)))
    = refocus3_closure (h, if b then c0 else c1, D, C)
  | iterate3 (h, DEC (D, C, PR_IF (v, c0, c1)))
    = refocus3_closure (h, err "Not a boolean", D, C)
  | iterate3 (h, DEC (D, C, PR_SEQ (v, c)))
    = refocus3_closure (h, c, D, C)
  | iterate3 (h, DEC (D, C, PR_WHILE (c0, c1)))
    = refocus3_closure (h, CLO_IF (c0,
				   CLO_WHILE (c0, c1),
				   CLO_UNDEFN),
			D, C)
  | iterate3 (h, DEC (D, C, PR_TRYC_POP v))
    = refocus3_closure (h, embed_value_in_closure v, D, C)
  | iterate3 (h, DEC (D, C, PR_TRYF_POP (v, c)))
    = refocus3_closure (h, CLO_SEQ (c, embed_value_in_closure v), D, C)
  | iterate3 (h, DEC (D, C, PR_LAB_POP v))
    = refocus3_closure (h, embed_value_in_closure v, D, C)
  | iterate3 (h, DEC (D, C, PR_OP (PLUS, [VAL_NUM n0, VAL_NUM n1])))
    = refocus3_closure (h, CLO_NUM (n0 + n1), D, C)
  | iterate3 (h, DEC (D, C, PR_OP (NUM_TO_STR, [VAL_NUM n0])))
    = refocus3_closure (h, CLO_STR (Int.toString n0), D, C)
  | iterate3 (h, DEC (D, C, PR_OP (opr, vs)))
    = refocus3_closure (h, err "Bad primop", D, C)
  | iterate3 (h, DEC (D, C, PR_REF v))
    = let val a = Sto.alloc h in
	  refocus3_closure ((a, v) :: h, CLO_ADDR a, D, C)
      end
  | iterate3 (h, DEC (D, C, PR_DEREF (VAL_ADDR a)))
    = refocus3_closure (h, case Sto.lookup (a, h)
			    of NONE
			       => err "Null pointer"
			     | SOME v
			       => embed_value_in_closure v,
			D, C)
  | iterate3 (h, DEC (D, C, PR_DEREF v))
    = refocus3_closure (h, err "Not an address", D, C)
  | iterate3 (h, DEC (D, C, PR_SET (VAL_ADDR a, v)))
    = refocus3_closure (Sto.update (a, h, v), embed_value_in_closure v, D, C)
  | iterate3 (h, DEC (D, C, PR_SET (v0, v1)))
    = refocus3_closure (h, err "Not an address", D, C)
  | iterate3 (h, DEC (D_1, C, PR_THROW v))
    = refocus3_closure (h, CLO_THROW (embed_value_in_closure v), D_1, C_1)
  | iterate3 (h, DEC (D_2 (D', C', c), C, PR_THROW v))
    = refocus3_closure (h, CLO_SEQ (c, CLO_THROW (embed_value_in_closure v)), D', C')
  | iterate3 (h, DEC (D_3 (D', C', x, (CLO_GND (t, bs))), C, PR_THROW v))
    = refocus3_closure (h, CLO_GND (t, Env.extend ([x], [v], bs)), D', C')
  | iterate3 (h, DEC (D_3 (D', C', x, c), C, PR_THROW v))
    = raise DEAD_CLAUSE
  | iterate3 (h, DEC (D_4 (D', C', l), C, PR_THROW v))
    = refocus3_closure (h, CLO_THROW (embed_value_in_closure v), D', C')
  | iterate3 (h, DEC (D_1, C, PR_BREAK (l, v)))
    = refocus3_closure (h, err "Unlabeled break", D_1, C_1)
  | iterate3 (h, DEC (D_2 (D', C', c), C, PR_BREAK (l, v)))
    = refocus3_closure (h, CLO_SEQ (c, CLO_BREAK (l, embed_value_in_closure v)), D', C')
  | iterate3 (h, DEC (D_3 (D', C', x, c), C, PR_BREAK (l, v)))
    = refocus3_closure (h, CLO_BREAK (l, embed_value_in_closure v), D', C')
  | iterate3 (h, DEC (D_4 (D', C', l'), C, PR_BREAK (l, v)))
    = refocus3_closure (h, if (l' = l)
			   then embed_value_in_closure v
			   else CLO_BREAK (l, embed_value_in_closure v),
			D', C')

fun normalize3 t
  = refocus3_closure ([], CLO_GND (t, []), D_1, C_1)

(* ************************************************************************** *)

(* Corridor transitions *)

(* | iterate4 (h, DEC (D, C, PR_REC_SET (v0, v1, v2)))
     = refocus4_closure (h, err "Bad record set", D, C)
     = refocus4_closure (h, CLO_THROW (CLO_STR "Bad record set"), D, C)
     = refocus4_closure (h, CLO_STR "Bad record set", D, C_19 C)
     = refocus4_context (h, D, C_19 C, VAL_STR "Bad record set")
     = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Bad record set")))
*)

fun refocus4_closure (h, CLO_GND (VAR x, bs), D, C)
    = refocus4_context (h, D, C, Env.lookup (x, bs))
  | refocus4_closure (h, CLO_GND (STR s, bs), D, C)
    = refocus4_context (h, D, C, (VAL_STR s))
  | refocus4_closure (h, CLO_GND (NUM n, bs), D, C)
    = refocus4_context (h, D, C, (VAL_NUM n))
  | refocus4_closure (h, CLO_GND (ADDR a, bs), D, C)
    = refocus4_context (h, D, C, (VAL_ADDR a))
  | refocus4_closure (h, CLO_GND (BOOL b, bs), D, C)
    = refocus4_context (h, D, C, (VAL_BOOL b))
  | refocus4_closure (h, CLO_GND (UNDEFN, bs), D, C)
    = refocus4_context (h, D, C, VAL_UNDEFN)
  | refocus4_closure (h, CLO_GND (NULL, bs), D, C)
    = refocus4_context (h, D, C, VAL_NULL)
  | refocus4_closure (h, CLO_GND (FUNC (xs, t), bs), D, C)
    = refocus4_context (h, D, C, VAL_FUNC (xs, t, bs))
  | refocus4_closure (h, CLO_GND (REC [], bs), D, C)
    = refocus4_context (h, D, C, VAL_REC [])
  | refocus4_closure (h, CLO_GND (REC ((s, t) :: sts), bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_5 (C, [], s, 
						    map (fn (s, t) => (s, CLO_GND (t, bs))) sts))
  | refocus4_closure (h, CLO_GND (LET (x, t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_2 (C, x, CLO_GND (t1, bs)))
  | refocus4_closure (h, CLO_GND (APP (t, ts), bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_3 (C, map (fn t => CLO_GND (t, bs)) ts))
  | refocus4_closure (h, CLO_GND (REC_REF (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_6 (C, CLO_GND (t1, bs)))
  | refocus4_closure (h, CLO_GND (REC_SET (t0, t1, t2), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_8 (C, CLO_GND (t1, bs), CLO_GND (t2, bs)))
  | refocus4_closure (h, CLO_GND (REC_DEL (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_11 (C, CLO_GND (t1, bs)))
  | refocus4_closure (h, CLO_GND (SET (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_15 (C, CLO_GND (t1, bs)))
  | refocus4_closure (h, CLO_GND (REF t, bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_13 C)
  | refocus4_closure (h, CLO_GND (DEREF t, bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_14 C)
  | refocus4_closure (h, CLO_GND (IF (t0, t1, t2), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_17 (C, CLO_GND (t1, bs), CLO_GND (t2, bs)))
  | refocus4_closure (h, CLO_GND (SEQ (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_18 (C, CLO_GND (t1, bs)))
  | refocus4_closure (h, CLO_GND (WHILE (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D, C_17 (C, CLO_GND (WHILE (t0, t1), bs), CLO_GND (UNDEFN, [])))
  | refocus4_closure (h, CLO_GND (LAB (l, t), bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D_4 (D, C, l), C_1)
  | refocus4_closure (h, CLO_GND (BREAK (l, t), bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_20 (C, l))
  | refocus4_closure (h, CLO_GND (TRYC (t0, x, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D_3 (D, C, x, CLO_GND (t1, bs)), C_1)
  | refocus4_closure (h, CLO_GND (TRYF (t0, t1), bs), D, C)
    = refocus4_closure (h, CLO_GND (t0, bs), D_2 (D, C, CLO_GND (t1, bs)), C_1)
  | refocus4_closure (h, CLO_GND (THROW t, bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_19 C)
  | refocus4_closure (h, CLO_GND (OP (opr, []), bs), D, C)
    = iterate4 (h, DEC (D, C, PR_OP (opr, [])))   
  | refocus4_closure (h, CLO_GND (OP (opr, (t :: ts)), bs), D, C)
    = refocus4_closure (h, CLO_GND (t, bs), D, C_21 (C, opr, [], (map (fn t => CLO_GND (t, bs)) ts)))
  | refocus4_closure (h, CLO_STR s, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_NUM n, D, C) 
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_ADDR a, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_BOOL b, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_UNDEFN, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_NULL, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REC [], D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REC ((s, c) :: scs), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_APP (c, cs), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_LET (x, c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REC_REF (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REC_SET (c0, c1, c2), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REC_DEL (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_SET (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_REF c, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_DEREF c, D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_IF (c0, c1, c2), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_SEQ (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_WHILE (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_LAB (l, c), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_BREAK (l, c), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_TRYC (c0, x, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_TRYF (c0, c1), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_THROW c, D, C)
    = refocus4_closure (h, c, D, C_19 C)
  | refocus4_closure (h, CLO_OP (opr, []), D, C)
    = raise DEAD_CLAUSE
  | refocus4_closure (h, CLO_OP (opr, (c :: cs)), D, C)
    = raise DEAD_CLAUSE

and refocus4_context (h, D_1, C_1, v)
    = RESULT (v, h)
  | refocus4_context (h, D_2 (D, C, c), C_1, v)
    = refocus4_closure (h, c, D, C_22 (C, v))       (* !!! *)
  | refocus4_context (h, D_3 (D, C, x, c), C_1, v)
    = refocus4_context (h, D, C, v)
  | refocus4_context (h, D_4 (D, C, l), C_1, v)
    = refocus4_context (h, D, C, v)
  | refocus4_context (h, D, C_2 (C, x, CLO_GND (t, bs)), v)
    = refocus4_closure (h, CLO_GND (t, Env.extend ([x], [v], bs)), D, C)
  | refocus4_context (h, D, C_2 (C, x, c), v)
    = raise DEAD_CLAUSE
  | refocus4_context (h, D, C_3 (C, []), v)
    = iterate4 (h, DEC (D, C, PR_APP (v, [])))
  | refocus4_context (h, D, C_3 (C, c :: cs), v)
    = refocus4_closure (h, c, D, C_4 (C, v, [], cs))
  | refocus4_context (h, D, C_4 (C, v0, vs, []), v)
    = iterate4 (h, DEC (D, C, PR_APP (v0, vs @ [v])))
  | refocus4_context (h, D, C_4 (C, v0, vs, c :: cs), v)
    = refocus4_closure (h, c, D, C_4 (C, v0, vs @ [v], cs))
  | refocus4_context (h, D, C_5 (C, svs, s, []), v)
    = refocus4_context (h, D, C, VAL_REC (svs @ [(s, v)]))
  | refocus4_context (h, D, C_5 (C, svs, s0, (s, c) :: scs), v)
    = refocus4_closure (h, c, D, C_5 (C, svs @ [(s0, v)], s, scs))
  | refocus4_context (h, D, C_6 (C, c), v)
    = refocus4_closure (h, c, D, C_7 (C, v))
  | refocus4_context (h, D, C_7 (C, v0), v)
    = iterate4 (h, DEC (D, C, PR_REC_REF (v0, v)))
  | refocus4_context (h, D, C_8 (C, c0, c1), v)
    = refocus4_closure (h, c0, D, C_9 (C, v, c1))
  | refocus4_context (h, D, C_9 (C, v0, c), v)
    = refocus4_closure (h, c, D, C_10 (C, v0, v))
  | refocus4_context (h, D, C_10 (C, v0, v1), v)
    = iterate4 (h, DEC (D, C, PR_REC_SET (v0, v1, v)))
  | refocus4_context (h, D, C_11 (C, c), v)
    = refocus4_closure (h, c, D, C_12 (C, v))
  | refocus4_context (h, D, C_12 (C, v0), v)
    = iterate4 (h, DEC (D, C, PR_REC_DEL (v0, v)))
  | refocus4_context (h, D, C_13 C, v)
    = let val a = Sto.alloc h in
	  refocus4_context ((a, v) :: h, D, C, VAL_ADDR a)
      end
  | refocus4_context (h, D, C_14 C, v)
    = iterate4 (h, DEC (D, C, PR_DEREF v))
  | refocus4_context (h, D, C_15 (C, c), v)
    = refocus4_closure (h, c, D, C_16 (C, v))
  | refocus4_context (h, D, C_16 (C, v0), v)
    = iterate4 (h, DEC (D, C, PR_SET (v0, v)))
  | refocus4_context (h, D, C_17 (C, c0, c1), v)
    = iterate4 (h, DEC (D, C, PR_IF (v, c0, c1)))
  | refocus4_context (h, D, C_18 (C, c), v)
    = refocus4_closure (h, c, D, C)
  | refocus4_context (h, D, C_22 (C, v0), v1)
    = refocus4_context (h, D, C, v0)
  | refocus4_context (h, D, C_23 (C, v0), v1)
    = iterate4 (h, DEC (D, C, PR_THROW v0))
  | refocus4_context (h, D, C_24 (C, l, v0), v1)		     
    = iterate4 (h, DEC (D, C, PR_BREAK (l, v0)))
  | refocus4_context (h, D, C_19 C, v)
    = iterate4 (h, DEC (D, C, PR_THROW v))
  | refocus4_context (h, D, C_20 (C, l), v)
    = iterate4 (h, DEC (D, C, PR_BREAK (l, v)))
  | refocus4_context (h, D, C_21 (C, opr, vs, []), v)
    = iterate4 (h, DEC (D, C, PR_OP (opr, vs @ [v])))
  | refocus4_context (h, D, C_21 (C, opr, vs, c :: cs), v)
    = refocus4_closure (h, c, D, C_21 (C, opr, vs @ [v], cs))

and iterate4 (h, VAL v) 
    = raise DEAD_CLAUSE
  | iterate4 (h, ERR v)
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_REC (sts, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_APP (t, ts, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_LET (x, t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_REC_REF (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_REC_SET (t0, t1, t2, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_REC_DEL (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_SET (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_REF (t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_DEREF (t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_IF (t0, t1, t2, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_SEQ (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_WHILE (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_LAB (l, t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_BREAK (l, t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_TRYC (t0, x, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_TRYF (t0, t1, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_THROW (t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_PROP_OP (opr, ts, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_VAR (x, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_LET (x, v, t, bs)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_APP (VAL_FUNC (xs, t, bs), vs)))
    = if length xs = length vs 
      then refocus4_closure (h, CLO_GND (t, Env.extend (xs, vs, bs)), D, C)
      else iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Arity mismatch")))
  | iterate4 (h, DEC (D, C, PR_APP (v, vs)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Not a function")))
  | iterate4 (h, DEC (D, C, PR_REC_REF (VAL_REC svs, VAL_STR s)))
    = refocus4_context (h, D, C, if Rec.contains (svs, s) 
				 then Rec.lookup (svs, s)
				 else VAL_UNDEFN)
  | iterate4 (h, DEC (D, C, PR_REC_REF (v0, v1)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Bad record ref")))
  | iterate4 (h, DEC (D, C, PR_REC_SET (VAL_REC svs, VAL_STR s, v)))
    = refocus4_context (h, D, C, VAL_REC (if Rec.contains (svs, s)
					  then (Rec.update (svs, s, v))
					  else ((s, v) :: svs)))
  | iterate4 (h, DEC (D, C, PR_REC_SET (v0, v1, v2)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Bad record set")))
  | iterate4 (h, DEC (D, C, PR_REC_DEL (VAL_REC svs, VAL_STR s)))
    = refocus4_context (h, D, C, 
			VAL_REC (if Rec.contains (svs, s)
				 then (Rec.remove (svs, s))
				 else svs))
  | iterate4 (h, DEC (D, C, PR_REC_DEL (v0, v1)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Bad record del")))
  | iterate4 (h, DEC (D, C, PR_IF (VAL_BOOL b, c0, c1)))
    = refocus4_closure (h, if b then c0 else c1, D, C)
  | iterate4 (h, DEC (D, C, PR_IF (v, c0, c1)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Not a boolean")))
  | iterate4 (h, DEC (D, C, PR_SEQ (v, c)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_WHILE (c0, c1)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_TRYC_POP v))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_TRYF_POP (v, c)))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_LAB_POP v))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_OP (PLUS, [VAL_NUM n0, VAL_NUM n1])))
    = refocus4_context (h, D, C, VAL_NUM (n0 + n1))
  | iterate4 (h, DEC (D, C, PR_OP (NUM_TO_STR, [VAL_NUM n0])))
    = refocus4_context (h, D, C, VAL_STR (Int.toString n0))
  | iterate4 (h, DEC (D, C, PR_OP (opr, vs)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Bad primop")))
  | iterate4 (h, DEC (D, C, PR_REF v))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D, C, PR_DEREF (VAL_ADDR a)))
    = (case Sto.lookup (a, h)
	of NONE => iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Null pointer")))
	 | SOME v => refocus4_context (h, D, C, v))		     
  | iterate4 (h, DEC (D, C, PR_DEREF v))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Not an address")))
  | iterate4 (h, DEC (D, C, PR_SET (VAL_ADDR a, v)))
    = refocus4_context (Sto.update (a, h, v), D, C, v)
  | iterate4 (h, DEC (D, C, PR_SET (v0, v1)))
    = iterate4 (h, DEC (D, C, PR_THROW (VAL_STR "Not an address")))
  | iterate4 (h, DEC (D_1, C, PR_THROW v))
    = ERROR (v, h)
  | iterate4 (h, DEC (D_2 (D', C', c), C, PR_THROW v))
    = refocus4_closure (h, c, D', C_23 (C', v))             (* !!! *)
  | iterate4 (h, DEC (D_3 (D', C', x, (CLO_GND (t, bs))), C, PR_THROW v))
    = refocus4_closure (h, CLO_GND (t, Env.extend ([x], [v], bs)), D', C')
  | iterate4 (h, DEC (D_3 (D', C', x, c), C, PR_THROW v))
    = raise DEAD_CLAUSE
  | iterate4 (h, DEC (D_4 (D', C', l), C, PR_THROW v))
    = iterate4 (h, DEC (D', C', PR_THROW v))
  | iterate4 (h, DEC (D_1, C, PR_BREAK (l, v)))
    = iterate4 (h, DEC (D_1, C, PR_THROW (VAL_STR "Unlabeled break")))
  | iterate4 (h, DEC (D_2 (D', C', c), C, PR_BREAK (l, v)))  (* !!! *)
    = refocus4_closure (h, c, D', C_24 (C', l, v))
  | iterate4 (h, DEC (D_3 (D', C', x, c), C, PR_BREAK (l, v)))
    = refocus4_context (h, D', C_20 (C', l), v)
  | iterate4 (h, DEC (D_4 (D', C', l'), C, PR_BREAK (l, v)))
    = if (l' = l)
      then refocus4_context (h, D', C', v)
      else refocus4_context (h, D', C_20 (C', l), v)

fun normalize4 t
  = refocus4_closure ([], CLO_GND (t, []), D_1, C_1)

(* ************************************************************************** *)

(* The remaining step is to flatten configurations.  The resulting machine is
   in jam.sml. We rename refocus_closure to eval, refocus_context to
   cont, and iterate to appl. *)
