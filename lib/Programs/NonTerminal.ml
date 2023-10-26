open Logic.Variable
open Logic.Formula

exception Empty_Nonterm of string
exception Bad_Strongest

(* I think we may not need an explicit grammar depending on how mutual recursion is supported.
   I think we can get away with baking it in to the non-terminals' definitions.*)
type 'program nonterminal = {
  name : string;
  expansions : 'program list Lazy.t;
  strongest : ((variable * variable) list * formula) option Lazy.t;
}

let to_str nterm =
  match Lazy.force nterm.strongest with
  | None -> nterm.name
  | Some (_, form) -> Printf.sprintf "[%s MGF=%s]" nterm.name (form_tostr form)

let expand nterm =
  let exp = Lazy.force nterm.expansions in
  match exp with [] -> raise (Empty_Nonterm nterm.name) | _ -> exp

let strongest nterm = Lazy.force nterm.strongest

let sub_hole_nterm nterm hole_map =
  match strongest nterm with
  | None -> nterm
  | Some (l, strong) ->
      {
        name = nterm.name;
        expansions = nterm.expansions;
        strongest = lazy (Some (l, sub_holes strong hole_map));
      }

let name nterm = nterm.name

let nonterminal_to_parseable_str_def nterm_type program_to_parseable_string
    nterm =
  let string_start = Printf.sprintf "%s %s" nterm_type nterm.name in
  let string_expansions =
    Printf.sprintf "[%s]"
      (String.concat ", " (List.map program_to_parseable_string (expand nterm)))
  in
  let string_strongest =
    match strongest nterm with
    | None -> "None"
    | Some (v_pairs_list, form) ->
        Printf.sprintf "Some ([%s] : %s)"
          (String.concat "; "
             (List.map
                (fun (v1, v2) ->
                  match (v1, v2) with
                  | TermVar _, TermVar _ ->
                      Printf.sprintf "(Int %s, Int %s)" (var_tostr v1)
                        (var_tostr v2)
                  | ATermVar _, ATermVar _ ->
                      Printf.sprintf "(AInt %s, AInt %s)" (var_tostr v1)
                        (var_tostr v2)
                  | BoolVar _, BoolVar _ ->
                      Printf.sprintf "(Bool %s, Bool %s)" (var_tostr v1)
                        (var_tostr v2)
                  | ABoolVar _, ABoolVar _ ->
                      Printf.sprintf "(ABool %s, ABool %s)" (var_tostr v1)
                        (var_tostr v2)
                  | _ -> raise Bad_Strongest)
                v_pairs_list))
          (match form with
          | BHole (name, exp_list) ->
              Printf.sprintf "(Hole: %s [%s])" name
                (String.concat ", "
                   (List.map
                      (fun exp ->
                        match exp with
                        | Term (TVar v) ->
                            Printf.sprintf "Int %s" (var_tostr (TermVar v))
                        | Boolean (BVar v) ->
                            Printf.sprintf "Bool %s" (var_tostr (BoolVar v))
                        | Term (ATVar (TUnApp v)) ->
                            Printf.sprintf "AInt %s" (var_tostr (ATermVar v))
                        | Boolean (ABVar (BUnApp v)) ->
                            Printf.sprintf "ABool %s" (var_tostr (ABoolVar v))
                        | _ -> raise Bad_Strongest)
                      exp_list))
          | _ -> form_to_parseable_str form)
  in
  Printf.sprintf "%s : %s : %s" string_start string_expansions string_strongest
