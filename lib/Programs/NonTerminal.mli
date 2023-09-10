open Logic.Variable
open Logic.Formula

exception Empty_Nonterm of string

type 'program nonterminal = {
  name : string;
  expansions : 'program list Lazy.t;
  (* When a non-terminal is not recursive, strongest should be None. *)
  strongest : ((variable * variable) list * formula) option Lazy.t;
}

(* To_string method *)
val to_str : 'program nonterminal -> string

(* To parseable string method.
   Takes the string representing the type of the nonterminal as input.
   Also takes a prog->string function as input since the nonterminal type is polymorphic. *)
val nonterminal_to_parseable_str_def :
  string -> ('program -> string) -> 'program nonterminal -> string

(* Substitutes a hole according to a map of holes to formulas -- only substitutes top-level prog.
   TODO: Make this more elegant so the substitution can be applied to the top-level program and trickle all the way down. *)
val sub_hole_nterm :
  'program nonterminal ->
  ((string * variable list) * formula) list ->
  'program nonterminal

(* Expands a non-terminal to its productions given by a list of programs. *)
val expand : 'program nonterminal -> 'program list

(* Evaluates/un-lazies a non-terminal's summary. *)
val strongest :
  'program nonterminal -> ((variable * variable) list * formula) option

(* Getter for the name of a nonterminal since I cannot access it normally somehow from the claimparser.*)
val name : 'program nonterminal -> string
