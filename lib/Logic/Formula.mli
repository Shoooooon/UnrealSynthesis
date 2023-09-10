open Variable

(* Exceptions *)
exception Subs_Type_Mismatch
exception Incorrect_Implication of string

(* For now, b_t and e_t are global constants.*)
(* Terms are integer-valued expressions. *)
type term =
  | Int of int
  | TVar of term_var
  | ATVar of term_array_app
  | Minus of term
  | Plus of term * term

and term_array_app = App of term_array_var * term | UnApp of term_array_var

(* Boolean_exps are boolean-valued expressions, also called formulas. *)
type boolean_exp =
  | True
  | False
  | BVar of bool_var
  | ABVar of bool_array_app
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
  (* T and T' are predicate transformers.
     They should only be represented explicitly when applied to a hole.
     For T, since we are mapping program variables to fresh variables and we want this to be reversible,
     we maintain typed maps from the original vars to the new ones.*)
  | T of boolean_exp * bool_array_var * term_array_var VMap_AT.t
  | TPrime of boolean_exp

and bool_array_app = App of bool_array_var * term | UnApp of bool_array_var

(* Exps are convenient to support holes and substitution. *)
and exp = Term of term | Boolean of boolean_exp

type formula = boolean_exp

val form_tostr : formula -> string

(* Produces less readable but more pareseable output. *)
val form_to_parseable_str : formula -> string

(* Produces forall var. form if var appears in form. Else returns form. *)
val forall : variable -> formula -> formula

(* Given a formula, a variable, and an expression, returns a formula where occurrences of the variable inside the input formula are replaced by the input expression.
   Note that subs will only overwrite free variables (e.g., (subs (a && \forall a. a) a b) -> b && \forall a. a *)
val subs : formula -> variable -> exp -> formula

(* Given a formula and a list of (variable, expression) pairs, returns a formula where occurrences of the variable inside the input formula are replaced by the input expression.
   Note that subs will only overwrite free variables (e.g., (subs (a && \forall a. a) a b) -> b && \forall a. a *)
val subs_several : formula -> (variable * exp) list -> formula

(* Given a formula and a set of formula names to avoid, produces a name for a fresh variable. *)
val fresh_var_name : formula -> string list -> string

(* Given a formula and a map of holes to bodies, substitutes all holes in the original formula with the correct bodies.*)
val sub_holes : formula -> ((string * variable list) * formula) list -> formula

(* For all array vars which are indexed by a hole (UnApp's), set the index to the given exp. *)
val set_exp_index : exp -> term -> exp

val t_transform :
  formula ->
  bool_array_var (*-> bool_array_var VMap_AB.t*) ->
  term_array_var VMap_AT.t ->
  formula

(* Returns the maximum value of the indices appearing in the expression, assuming they are all ints, or 0 if none appear.   *)
val max_index : exp -> int
