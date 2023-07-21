open Variable
open Formula

type 'program nonterminal = {
  name : string;
  expansions : 'program list;
  (* When a non-terminal is not recursive, strongest should be None. *)
  strongest : ((variable * variable) list * formula) option;
}

(* To_string method *)
val to_str : 'program nonterminal -> string

(* Expands a non-terminal to its productions given by a list of programs. *)
val expand : 'program nonterminal -> 'program list
