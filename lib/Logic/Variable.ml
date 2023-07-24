type term_var = ET | T of string
type bool_var = BT | B of string
type variable = BoolVar of bool_var | TermVar of term_var

(* Necessary to support set functor. *)
type t = variable

let compare = compare

let var_tostr var =
  match var with
  | BoolVar BT -> "b_t"
  | BoolVar (B b) -> b
  | TermVar ET -> "e_t"
  | TermVar (T t) -> t
