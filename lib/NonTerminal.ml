open Variable
open Formula

(* I think we may not need an explicit grammar depending on how mutual recursion is supported.
   I think we can get away with baking it in to the non-terminals' definitions.*)
type 'program nonterminal = {
  name : string;
  expansions : 'program list;
  strongest : ((variable * variable) list * formula) option;
}

let to_str nterm =
  match nterm.strongest with
  | None -> nterm.name
  | Some (_, form) -> Printf.sprintf "[%s MGF=%s]" nterm.name (form_tostr form)

let expand nterm = nterm.expansions
