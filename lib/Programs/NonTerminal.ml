open Logic.Variable
open Logic.Formula

exception Empty_Nonterm of string

(* I think we may not need an explicit grammar depending on how mutual recursion is supported.
   I think we can get away with baking it in to the non-terminals' definitions.*)
type 'program nonterminal = {
  name : string;
  expansions : 'program list Lazy.t;
  strongest : ((variable * variable) list * formula) option;
}

let to_str nterm =
  match nterm.strongest with
  | None -> nterm.name
  | Some (_, form) -> Printf.sprintf "[%s MGF=%s]" nterm.name (form_tostr form)

let sub_hole_nterm nterm hole_map =
  match nterm.strongest with
  | None -> nterm
  | Some (l, strong) ->
      {
        name = nterm.name;
        expansions = nterm.expansions;
        strongest = Some (l, sub_holes strong hole_map);
      }

let expand nterm =
  let exp = Lazy.force nterm.expansions in
  match exp with [] -> raise (Empty_Nonterm nterm.name) | _ -> exp

let name nterm = nterm.name
