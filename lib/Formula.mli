open Variable

(* Exceptions *)
exception Subs_Type_Mismatch
exception Incorrect_Implication of string

(* For now, b_t and e_t are global constants. We may need to sub out after ITE *)

type term = Int of int | TVar of variable | Plus of term * term

type boolean_exp =
  | True
  | False
  | BVar of variable
  | And of boolean_exp * boolean_exp
  | Or of boolean_exp * boolean_exp
  | Not of boolean_exp
  | Implies of boolean_exp * boolean_exp
  | Equals of term * term
  | Less of term * term
  | Exists of variable * boolean_exp
  | Forall of variable * boolean_exp

type exp = Term of term | Boolean of boolean_exp
type formula = boolean_exp

val form_tostr : formula -> string
val subs : formula -> variable -> exp -> formula
val implies : formula -> formula -> bool Lazy.t
val fresh_var : formula -> variable
