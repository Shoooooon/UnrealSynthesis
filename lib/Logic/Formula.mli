open Variable

(* Exceptions *)
exception Subs_Type_Mismatch of int
exception Incorrect_Implication of string

(* For now, b_t and e_t are global constants.*)
(* Terms the bitvector-valued ones. *)
val bvconst : int

type bitv_unop = Minus
type bitv_binop = Plus | Mult | Sub | Or | And | Xor

type bitv_term =
  | Bitv of string
    (*We can cast to and from int -- easier than figuring out OCaml bitvectors as long as I never evaluate in this code. *)
  | BitvTVar of bitv_term_var
  | ABitvTVar of bitv_term_array_app
  | BitvUnarApp of bitv_unop * bitv_term
  | BitvBinarApp of bitv_binop * bitv_term * bitv_term
  | BitvTHole of string * exp list
(* | ITVar of int_term_var
   | AITVar of int_term_array_app
   | Minus of int_term
   | Plus of int_term * int_term
   | Times of int_term * int_term
   | THole of string * exp list *)

and bitv_term_array_app =
  | BitvTApp of bitv_term_array_var * int_term
  | BitvTUnApp of bitv_term_array_var

(* Terms the int-valued ones. *)
and int_term =
  | Int of int
  | ITVar of int_term_var
  | AITVar of int_term_array_app
  | Minus of int_term
  | Plus of int_term * int_term
  | Times of int_term * int_term
  | THole of string * exp list

and int_term_array_app =
  | ITApp of int_term_array_var * int_term
  | ITUnApp of int_term_array_var

and term = ITerm of int_term | BitvTerm of bitv_term

(* Boolean_exps are boolean-valued expressions, also called formulas. *)
and boolean_exp =
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
  | BHole of string * exp list
  (* T and T' are predicate transformers.
     They should only be represented explicitly when applied to a hole.
     For T, since we are mapping program variables to fresh variables and we want this to be reversible,
     we maintain typed maps from the original vars to the new ones.*)
  | T of boolean_exp * bool_array_var * vmaps
  | TPrime of boolean_exp

and bool_array_app =
  | BApp of bool_array_var * int_term
  | BUnApp of bool_array_var

(* Exps are convenient to support holes and substitution. *)
and exp = Term of term | Boolean of boolean_exp

type formula = boolean_exp

(* Converts a variable to the appropriate expression. *)
val var_to_exp : variable -> exp
val form_tostr : formula -> string
val term_tostr : term -> string

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

(* True iff the formula contains an existential quantifier. *)
val has_exists : formula -> bool
val free_vars : formula -> VS.t -> VS.t

(* Given a formula and a set of formula names to avoid, produces a name for a fresh variable. *)
val fresh_var_name : formula -> string list -> string

(* Given a formula and a map of holes to bodies, substitutes all holes in the original formula with the correct bodies.*)
val sub_holes : formula -> ((string * variable list) * formula) list -> formula

(* For all array vars which are indexed by a hole (UnApp's), set the index to the given exp. *)
val set_exp_index : exp -> int_term -> exp

val t_transform :
  formula -> bool_array_var (*-> bool_array_var VMap_AB.t*) -> vmaps -> formula

(* Returns the maximum value of the indices appearing in the expression, assuming they are all ints, or 0 if none appear.   *)
val max_index : exp -> int
val bool_finite_vs_transformer : int -> formula -> formula
