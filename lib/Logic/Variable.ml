type term_array_var = ET | T of string
type term_var = ET | T of string
(* type general_term_var = TSimple of term_var | TVectorState of term_array_var *)

type bool_array_var = BT | B of string
type bool_var = BT | B of string
(* type general_bool_var = BSimple of bool_var | BVectorState of boolean_array_var *)

type variable =
  | BoolVar of bool_var
  | TermVar of term_var
  | ABoolVar of bool_array_var
  | ATermVar of term_array_var

(* Useful set and map modules. *)
module VS = Set.Make (struct
  type t = variable

  let compare = compare
end)

module VMap_AT = Map.Make (struct
  type t = term_array_var

  let compare = compare
end)

module VMap_AB = Map.Make (struct
  type t = bool_array_var

  let compare = compare
end)

let var_tostr var =
  match var with
  | BoolVar BT -> "b_t"
  | BoolVar (B b) -> b
  | ABoolVar BT -> "b_t"
  | ABoolVar (B b) -> b
  | TermVar ET -> "e_t"
  | TermVar (T t) -> t
  | ATermVar ET -> "e_t"
  | ATermVar (T t) -> t

let subs_var current_var to_replace expression =
  let repl =
    match current_var with
    | BoolVar BT -> to_replace = "b_t"
    | BoolVar (B b) -> b = to_replace
    | ABoolVar BT -> to_replace = "b_t"
    | ABoolVar (B b) -> b = to_replace
    | TermVar ET -> to_replace = "e_t"
    | TermVar (T t) -> to_replace = t
    | ATermVar ET -> to_replace = "e_t"
    | ATermVar (T t) -> to_replace = t
  in
  if repl then expression else current_var

(* let match_var var1 name =
   match current_var with
   | BoolVar BT -> name = "b_t"
   | BoolVar (B b) -> b = name
   | ABoolVar BT -> name = "b_t"
   | ABoolVar (B b) -> b = name
   | TermVar ET -> name = "e_t"
   | TermVar (T t) -> name = t
   | ATermVar ET -> name = "e_t"
   | ATermVar (T t) -> name = t *)
