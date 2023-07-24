open Logic.Variable
open Logic.Formula

type 'program nonterminal = {
  name : string;
  expansions : 'program list;
  (* When a non-terminal is not recursive, strongest should be None. *)
  strongest : ((variable * variable) list * formula) option;
}

(* To_string method *)
val to_str : 'program nonterminal -> string

(* Substitutes a hole according to a map of holes to formulas -- only substitutes top-level prog.
   TODO: Make this more elegant so the substitution can be applied to the top-level program and trickle all the way down. *)
val sub_hole_nterm :
  'program nonterminal ->
  ((string * variable list) * formula) list ->
  'program nonterminal

(* Expands a non-terminal to its productions given by a list of programs. *)
val expand : 'program nonterminal -> 'program list
