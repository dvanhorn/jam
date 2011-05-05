(* An abstract machine for Lambda_JS. *)

(* ************************************************************************** *)
(* Stores *)
structure Sto = struct 

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

(* ************************************************************************** *)
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

(* ************************************************************************** *)
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
(* ************************************************************************** *)

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

datatype value 
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

datatype potential_redex 
  = PR_APP of value * (value list)
  | PR_REC_REF of value * value
  | PR_REC_SET of value * value * value
  | PR_REC_DEL of value * value
  | PR_IF of value * term * term * bindings
  | PR_OP of opr * value list
  | PR_SET of value * value
  | PR_DEREF of value
  | PR_THROW of value
  | PR_BREAK of string * value

datatype C 
  = C_1
  | C_2  of C * string * term * bindings
  | C_3  of C * (term * bindings) list
  | C_4  of C * value * value list * (term * bindings) list
  | C_5  of C * (string * value) list * string * (string * (term * bindings)) list
  | C_6  of C * term * bindings
  | C_7  of C * value
  | C_8  of C * term * term * bindings 
  | C_9  of C * value * term * bindings
  | C_10 of C * value * value
  | C_11 of C * term * bindings
  | C_12 of C * value 
  | C_13 of C
  | C_14 of C
  | C_15 of C * term * bindings
  | C_16 of C * value
  | C_17 of C * term * term * bindings
  | C_18 of C * term * bindings
  | C_19 of C
  | C_20 of C * string
  | C_21 of C * opr * value list * (term * bindings) list

  | C_22 of C * value
  | C_23 of C * value
  | C_24 of C * string * value

datatype D 
  = D_1
  | D_2 of D * C * term * bindings
  | D_3 of D * C * string * term * bindings
  | D_4 of D * C * string 

withtype sto = value Sto.sto 

datatype result = RESULT of value * sto
		| ERROR of value * sto

fun eval (h, VAR x, bs, D, C)
    = cont (h, D, C, Env.lookup (x, bs))
  | eval (h, STR s, bs, D, C)
    = cont (h, D, C, (VAL_STR s))
  | eval (h, NUM n, bs, D, C)
    = cont (h, D, C, (VAL_NUM n))
  | eval (h, ADDR a, bs, D, C)
    = cont (h, D, C, (VAL_ADDR a))
  | eval (h, BOOL b, bs, D, C)
    = cont (h, D, C, (VAL_BOOL b))
  | eval (h, UNDEFN, bs, D, C)
    = cont (h, D, C, VAL_UNDEFN)
  | eval (h, NULL, bs, D, C)
    = cont (h, D, C, VAL_NULL)
  | eval (h, FUNC (xs, t), bs, D, C)
    = cont (h, D, C, VAL_FUNC (xs, t, bs))
  | eval (h, REC [], bs, D, C)
    = cont (h, D, C, VAL_REC [])
  | eval (h, REC ((s, t) :: sts), bs, D, C)
    = eval (h, t, bs, D, C_5 (C, [], s, 
			      (map (fn (s, t) => (s, (t, bs))) sts)))
  | eval (h, LET (x, t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_2 (C, x, t1, bs))
  | eval (h, APP (t, ts), bs, D, C)
    = eval (h, t, bs, D, C_3 (C, map (fn t => (t, bs)) ts))
  | eval (h, REC_REF (t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_6 (C, t1, bs))
  | eval (h, REC_SET (t0, t1, t2), bs, D, C)
    = eval (h, t0, bs, D, C_8 (C, t1, t2, bs))
  | eval (h, REC_DEL (t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_11 (C, t1, bs))
  | eval (h, REF t, bs, D, C)
    = eval (h, t, bs, D, C_13 C)
  | eval (h, DEREF t, bs, D, C)
    = eval (h, t, bs, D, C_14 C)
  | eval (h, SET (t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_15 (C, t1, bs))
  | eval (h, IF (t0, t1, t2), bs, D, C)
    = eval (h, t0, bs, D, C_17 (C, t1, t2, bs))
  | eval (h, SEQ (t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_18 (C, t1, bs))
  | eval (h, WHILE (t0, t1), bs, D, C)
    = eval (h, t0, bs, D, C_17 (C, WHILE (t0, t1), UNDEFN, bs))
  | eval (h, LAB (l, t), bs, D, C)
    = eval (h, t, bs, D_4 (D, C, l), C_1)
  | eval (h, BREAK (l, t), bs, D, C)
    = eval (h, t, bs, D, C_20 (C, l))
  | eval (h, TRYC (t0, x, t1), bs, D, C)
    = eval (h, t0, bs, D_3 (D, C, x, t1, bs), C_1)
  | eval (h, TRYF (t0, t1), bs, D, C)
    = eval (h, t0, bs, D_2 (D, C, t1, bs), C_1)
  | eval (h, THROW t, bs, D, C)
    = eval (h, t, bs, D, C_19 C)
  | eval (h, OP (opr, []), bs, D, C)
    = appl (h, D, C, PR_OP (opr, []))
  | eval (h, OP (opr, (t :: ts)), bs, D, C)
    = eval (h, t, bs, D, C_21 (C, opr, [], (map (fn t => (t, bs)) ts)))

and cont (h, D_1, C_1, v)
    = RESULT (v, h)
  | cont (h, D_2 (D, C, t, bs), C_1, v)
    = eval (h, t, bs, D, C_22 (C, v))       (* !!! *)
  | cont (h, D_3 (D, C, x, t, bs), C_1, v)
    = cont (h, D, C, v)
  | cont (h, D_4 (D, C, l), C_1, v)
    = cont (h, D, C, v)
  | cont (h, D, C_2 (C, x, t, bs), v)
    = eval (h, t, Env.extend ([x], [v], bs), D, C)
  | cont (h, D, C_3 (C, []), v)
    = appl (h, D, C, PR_APP (v, []))
  | cont (h, D, C_3 (C, (t, bs) :: cs), v)
    = eval (h, t, bs, D, C_4 (C, v, [], cs))
  | cont (h, D, C_4 (C, v0, vs, []), v)
    = appl (h, D, C, PR_APP (v0, vs @ [v]))
  | cont (h, D, C_4 (C, v0, vs, (t, bs) :: cs), v)
    = eval (h, t, bs, D, C_4 (C, v0, vs @ [v], cs))
  | cont (h, D, C_5 (C, svs, s, []), v)
    = cont (h, D, C, VAL_REC (svs @ [(s, v)]))
  | cont (h, D, C_5 (C, svs, s0, (s, (t, bs)) :: scs), v)
    = eval (h, t, bs, D, C_5 (C, svs @ [(s0, v)], s, scs))
  | cont (h, D, C_6 (C, t, bs), v)
    = eval (h, t, bs, D, C_7 (C, v))
  | cont (h, D, C_7 (C, v0), v)
    = appl (h, D, C, PR_REC_REF (v0, v))
  | cont (h, D, C_8 (C, t0, t1, bs), v)
    = eval (h, t0, bs, D, C_9 (C, v, t1, bs))
  | cont (h, D, C_9 (C, v0, t, bs), v)
    = eval (h, t, bs, D, C_10 (C, v0, v))
  | cont (h, D, C_10 (C, v0, v1), v)
    = appl (h, D, C, PR_REC_SET (v0, v1, v))
  | cont (h, D, C_11 (C, t, bs), v)
    = eval (h, t, bs, D, C_12 (C, v))
  | cont (h, D, C_12 (C, v0), v)
    = appl (h, D, C, PR_REC_DEL (v0, v))
  | cont (h, D, C_13 C, v)
    = let val a = Sto.alloc h in
	  cont ((a, v) :: h, D, C, VAL_ADDR a)
      end
  | cont (h, D, C_14 C, v)
    = appl (h, D, C, PR_DEREF v)
  | cont (h, D, C_15 (C, t, bs), v)
    = eval (h, t, bs, D, C_16 (C, v))
  | cont (h, D, C_16 (C, v0), v)
    = appl (h, D, C, PR_SET (v0, v))
  | cont (h, D, C_17 (C, t0, t1, bs), v)
    = appl (h, D, C, PR_IF (v, t0, t1, bs))
  | cont (h, D, C_18 (C, t, bs), v)
    = eval (h, t, bs, D, C)
  | cont (h, D, C_19 C, v)
    = appl (h, D, C, PR_THROW v)
  | cont (h, D, C_20 (C, l), v)
    = appl (h, D, C, PR_BREAK (l, v))
  | cont (h, D, C_21 (C, opr, vs, []), v)
    = appl (h, D, C, PR_OP (opr, vs @ [v]))
  | cont (h, D, C_21 (C, opr, vs, (t, bs) :: cs), v)
    = eval (h, t, bs, D, C_21 (C, opr, vs @ [v], cs))
  | cont (h, D, C_22 (C, v0), v1)
    = cont (h, D, C, v0)
  | cont (h, D, C_23 (C, v0), v1)
    = appl (h, D, C, PR_THROW v0)
  | cont (h, D, C_24 (C, l, v0), v1)		     
    = appl (h, D, C, PR_BREAK (l, v0))

and appl (h, D, C, PR_APP (VAL_FUNC (xs, t, bs), vs))
    = if length xs = length vs 
      then eval (h, t, Env.extend (xs, vs, bs), D, C)
      else appl (h, D, C, PR_THROW (VAL_STR "Arity mismatch"))
  | appl (h, D, C, PR_APP (v, vs))
    = appl (h, D, C, PR_THROW (VAL_STR "Not a function"))
  | appl (h, D, C, PR_REC_REF (VAL_REC svs, VAL_STR s))
    = cont (h, D, C, if Rec.contains (svs, s) 
		     then Rec.lookup (svs, s)
		     else VAL_UNDEFN)
  | appl (h, D, C, PR_REC_REF (v0, v1))
    = appl (h, D, C, PR_THROW (VAL_STR "Bad record ref"))
  | appl (h, D, C, PR_REC_SET (VAL_REC svs, VAL_STR s, v))
    = cont (h, D, C, VAL_REC (if Rec.contains (svs, s)
			      then (Rec.update (svs, s, v))
			      else ((s, v) :: svs)))
  | appl (h, D, C, PR_REC_SET (v0, v1, v2))
    = appl (h, D, C, PR_THROW (VAL_STR "Bad record set"))
  | appl (h, D, C, PR_REC_DEL (VAL_REC svs, VAL_STR s))
    = cont (h, D, C, 
	    VAL_REC (if Rec.contains (svs, s)
		     then (Rec.remove (svs, s))
		     else svs))
  | appl (h, D, C, PR_REC_DEL (v0, v1))
    = appl (h, D, C, PR_THROW (VAL_STR "Bad record del"))
  | appl (h, D, C, PR_IF (VAL_BOOL b, t0, t1, bs))
    = eval (h, if b then t0 else t1, bs, D, C)
  | appl (h, D, C, PR_IF (v, t0, t1, bs))
    = appl (h, D, C, PR_THROW (VAL_STR "Not a boolean"))
  | appl (h, D, C, PR_OP (PLUS, [VAL_NUM n0, VAL_NUM n1]))
    = cont (h, D, C, VAL_NUM (n0 + n1))
  | appl (h, D, C, PR_OP (NUM_TO_STR, [VAL_NUM n0]))
    = cont (h, D, C, VAL_STR (Int.toString n0))
  | appl (h, D, C, PR_OP (opr, vs))
    = appl (h, D, C, PR_THROW (VAL_STR "Bad primop"))
  | appl (h, D, C, PR_DEREF (VAL_ADDR a))
    = (case Sto.lookup (a, h)
	of NONE => appl (h, D, C, PR_THROW (VAL_STR "Null pointer"))
	 | SOME v => cont (h, D, C, v))		     
  | appl (h, D, C, PR_DEREF v)
    = appl (h, D, C, PR_THROW (VAL_STR "Not an address"))
  | appl (h, D, C, PR_SET (VAL_ADDR a, v))
    = cont (Sto.update (a, h, v), D, C, v)
  | appl (h, D, C, PR_SET (v0, v1))
    = appl (h, D, C, PR_THROW (VAL_STR "Not an address"))
  | appl (h, D_1, C, PR_THROW v)
    = ERROR (v, h)
  | appl (h, D_2 (D', C', t, bs), C, PR_THROW v)
    = eval (h, t, bs, D', C_23 (C', v))
  | appl (h, D_3 (D', C', x, t, bs), C, PR_THROW v)
    = eval (h, t, Env.extend ([x], [v], bs), D', C')
  | appl (h, D_4 (D', C', l), C, PR_THROW v)
    = appl (h, D', C', PR_THROW v)
  | appl (h, D_1, C, PR_BREAK (l, v))
    = appl (h, D_1, C, PR_THROW (VAL_STR "Unlabeled break"))
  | appl (h, D_2 (D', C', t, bs), C, PR_BREAK (l, v))
    = eval (h, t, bs, D', C_24 (C', l, v))
  | appl (h, D_3 (D', C', x, t, bs), C, PR_BREAK (l, v))
    = appl (h, D', C', PR_BREAK (l, v))
  | appl (h, D_4 (D', C', l'), C, PR_BREAK (l, v))
    = if (l' = l)
      then cont (h, D', C', v)
      else appl (h, D', C', PR_BREAK (l, v))

fun norm t
  = eval ([], t, [], D_1, C_1)
    
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
        val ERROR (VAL_STR "Not a function", [])
          = norm (APP (NUM 7, [NUM 5]))     
        val ERROR (VAL_STR "Arity mismatch", [])
          = norm (APP (FUNC ([], VAR "x"), [NUM 5]))        
        val RESULT (VAL_NUM 5, [])
          = norm (LET ("x", NUM 5, VAR "x"))        
        val RESULT (VAL_NUM 5, [])
          = norm (APP (LET ("x", NUM 5, FUNC ([], VAR "x")), []))
        val RESULT (VAL_ADDR 1, [(1, VAL_NUM 5)])
          = norm (REF (NUM 5))      
        val RESULT (VAL_NUM 5, [(1, VAL_NUM 5)])
          = norm (DEREF (REF (NUM 5)))      
        val RESULT (VAL_NUM 9, [(1, VAL_NUM 9)]) 
          = norm (SET (REF (NUM 5), (NUM 9)))
	val ERROR (VAL_NUM 5, [])
	  = norm (THROW (NUM 5))
	val ERROR (VAL_NUM 5, [])
	  = norm (THROW (THROW (NUM 5)))
	val RESULT (VAL_NUM 5, [])
	  = norm (TRYC (THROW (NUM 5), "x", VAR "x"))
	val ERROR (VAL_STR "Null pointer", [])
	  = norm (DEREF (ADDR 0))
	val ERROR (VAL_STR "Not an address", [])
	  = norm (DEREF (NUM 0))
	val ERROR (VAL_NUM 7, [])
	  = norm (TRYF (THROW (NUM 5), THROW (NUM 7)))
	val ERROR (VAL_NUM 5, [])
	  = norm (TRYF (THROW (NUM 5), NUM 7))
    in
        "OK"
    end

val "OK" = test norm 


