open Variable

(* Exceptions *)
exception Subs_Type_Mismatch
exception Incorrect_Implication of string

(* For now, b_t and e_t are global constants.*)
(* Terms are integer-valued expressions. *)
type term = Int of int | TVar of term_var | Plus of term * term

(* Boolean_exps are boolean-valued expressions, also called formulas. *)
type boolean_exp =
  | True
  | False
  | BVar of bool_var
  | And of boolean_exp * boolean_exp
  | Or of boolean_exp * boolean_exp
  | Not of boolean_exp
  | Implies of boolean_exp * boolean_exp
  | Equals of term * term
  | Less of term * term
  | Iff of boolean_exp * boolean_exp (*Equals but for bools*)
  | Exists of variable * boolean_exp
  | Forall of variable * boolean_exp
  | Hole of string * exp list

(* Exps are convenient to support holes and substitution. *)
and exp = Term of term | Boolean of boolean_exp

type formula = boolean_exp

val form_tostr : formula -> string

(* Given a formula, a variable, and an expression, returns a formula where occurrences of the variable inside the input formula are replaced by the input expression. *)
val subs : formula -> variable -> exp -> formula

(* Returns a function that can be used to check implication assuming no holes are present.
   Allows separate instances for convenient memoization/maintaining state between invocations.
   This will help disambiguate holes when we synthesize MGFs/invariants. *)
val implicator : unit -> (formula -> formula -> bool Lazy.t) * (unit -> string)

(* Returns a function that can be used to check implication assuming at least one hole are present.
   Allows separate instances for convenient memoization/maintaining state between invocations.
   This will help disambiguate holes when we synthesize MGFs/invariants. *)
val implicator_synth :
  unit -> (formula -> formula -> bool Lazy.t) * (unit -> string)

(* Given a formula and a set of formula names to avoid, produces a name for a fresh variable. *)
val fresh_var_name : formula -> string list -> string

