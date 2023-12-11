open Variable

exception Subs_Type_Mismatch of int
exception Unsupported_Output

(* exception Subs_Exp_In_Quant *)
exception Set_Index_Inside_Predicate
exception Applying_Transformation_On_Incomplete_Index
exception Incorrect_Implication of string

let bvconst = 32
(* Constant giving bitvector length. In the future, this could be made modular.*)

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
     we maintain typed maps from the original vars to the new ones.
     The values here are formula, b_loop, and maps for substituted vars.*)
  | T of boolean_exp * bool_array_var (* * bool_array_var VMap_AB.t *) * vmaps
  | TPrime of boolean_exp

and bool_array_app =
  | BApp of bool_array_var * int_term
  | BUnApp of bool_array_var

and exp = Term of term | Boolean of boolean_exp

module TS = Set.Make (struct
  type t = int_term

  let compare = compare
end)

type formula = boolean_exp

let var_to_exp var =
  match var with
  | BoolVar b -> Boolean (BVar b)
  | ABoolVar b -> Boolean (ABVar (BUnApp b))
  | IntTermVar t -> Term (ITerm (ITVar t))
  | AIntTermVar t -> Term (ITerm (AITVar (ITUnApp t)))
  | BitvTermVar t -> Term (BitvTerm (BitvTVar t))
  | ABitvTermVar t -> Term (BitvTerm (ABitvTVar (BitvTUnApp t)))

(* Specialty Constructors for parsing - TODO make exists and forall quantify more than 1 variable*)

(* toStr Methods *)
let rec int_term_tostr int_term =
  match int_term with
  | Int i -> Printf.sprintf "%d" i
  | ITVar v -> var_tostr (IntTermVar v)
  | AITVar (ITApp (at, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (AIntTermVar at)) (int_term_tostr i)
  | AITVar (ITUnApp at) -> Printf.sprintf "%s[?]" (var_tostr (AIntTermVar at))
  | Minus t -> Printf.sprintf "(- %s)" (int_term_tostr t)
  | Plus (t1, t2) ->
      Printf.sprintf "(%s + %s)" (int_term_tostr t1) (int_term_tostr t2)
  | Times (t1, t2) ->
      Printf.sprintf "(%s * %s)" (int_term_tostr t1) (int_term_tostr t2)
  | THole (s, arg_list) ->
      Printf.sprintf "(%s (%s))" s
        (String.concat ", " (List.map exp_tostr arg_list))

and bitv_term_tostr bitv_term =
  match bitv_term with
  | Bitv i -> i
  | BitvTVar v -> var_tostr (BitvTermVar v)
  | ABitvTVar (BitvTApp (at, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (ABitvTermVar at)) (int_term_tostr i)
  | ABitvTVar (BitvTUnApp at) ->
      Printf.sprintf "%s[?]" (var_tostr (ABitvTermVar at))
  | BitvUnarApp (Minus, btv) -> Printf.sprintf "(- %s)" (bitv_term_tostr btv)
  | BitvBinarApp (Plus, btv1, btv2) ->
      Printf.sprintf "(%s + %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvBinarApp (Mult, btv1, btv2) ->
      Printf.sprintf "(%s * %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvBinarApp (Sub, btv1, btv2) ->
      Printf.sprintf "(%s - %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvBinarApp (Or, btv1, btv2) ->
      Printf.sprintf "(%s | %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvBinarApp (Xor, btv1, btv2) ->
      Printf.sprintf "(%s ^ %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvBinarApp (And, btv1, btv2) ->
      Printf.sprintf "(%s & %s)" (bitv_term_tostr btv1) (bitv_term_tostr btv2)
  | BitvTHole (s, arg_list) ->
      Printf.sprintf "(%s (%s))" s
        (String.concat ", " (List.map exp_tostr arg_list))
(* | ITVar v -> var_tostr (IntTermVar v)
   | AITVar (ITApp (at, i)) ->
       Printf.sprintf "%s[%s]" (var_tostr (AIntTermVar at)) (term_tostr i)
   | AITVar (ITUnApp at) -> Printf.sprintf "%s[?]" (var_tostr (AIntTermVar at))
   | Minus t -> Printf.sprintf "(%s)" (term_tostr t)
   | Plus (t1, t2) -> Printf.sprintf "(%s + %s)" (term_tostr t1) (term_tostr t2)
   | Times (t1, t2) -> Printf.sprintf "(%s * %s)" (term_tostr t1) (term_tostr t2)
   | THole (s, arg_list) ->
       Printf.sprintf "(%s (%s))" s
         (String.concat ", " (List.map exp_tostr arg_list)) *)

and term_tostr term =
  match term with
  | ITerm it -> int_term_tostr it
  | BitvTerm btv -> bitv_term_tostr btv

and form_tostr form =
  match form with
  | True -> "T"
  | False -> "F"
  | And (b1, b2) -> Printf.sprintf "(%s && %s)" (form_tostr b1) (form_tostr b2)
  | Or (b1, b2) -> Printf.sprintf "(%s || %s)" (form_tostr b1) (form_tostr b2)
  | Not b -> Printf.sprintf "!%s" (form_tostr b)
  | Implies (b1, b2) ->
      Printf.sprintf "(%s => %s)" (form_tostr b1) (form_tostr b2)
  | BVar v -> var_tostr (BoolVar v)
  | ABVar (BApp (ab, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (ABoolVar ab)) (int_term_tostr i)
  | ABVar (BUnApp ab) -> Printf.sprintf "%s[?]" (var_tostr (ABoolVar ab))
  | Equals (t1, t2) ->
      Printf.sprintf "(%s == %s)" (term_tostr t1) (term_tostr t2)
  | Less (t1, t2) -> Printf.sprintf "(%s < %s)" (term_tostr t1) (term_tostr t2)
  | Iff (t1, t2) -> Printf.sprintf "(%s <-> %s)" (form_tostr t1) (form_tostr t2)
  | Exists (v, b) ->
      Printf.sprintf "((Exists %s). %s)" (var_tostr v) (form_tostr b)
  | Forall (v, b) ->
      Printf.sprintf "((Forall %s). %s)" (var_tostr v) (form_tostr b)
  | BHole (s, arg_list) ->
      Printf.sprintf "(%s (%s))" s
        (String.concat ", " (List.map exp_tostr arg_list))
  | T (f, _, _) -> Printf.sprintf "T (%s)" (form_tostr f)
  | TPrime f -> Printf.sprintf "T' (%s)" (form_tostr f)

and exp_tostr exp =
  match exp with Term t -> term_tostr t | Boolean b -> form_tostr b

(* toStr Methods in a format that can be read back in *)
let rec int_term_to_parseable_str int_term =
  match int_term with
  | Int i -> Printf.sprintf "%d" i
  | ITVar v -> var_tostr (IntTermVar v)
  | AITVar (ITApp (at, i)) ->
      Printf.sprintf "%s[%s]"
        (var_tostr (AIntTermVar at))
        (int_term_to_parseable_str i)
  | AITVar (ITUnApp at) -> Printf.sprintf "%s[?]" (var_tostr (AIntTermVar at))
  | Minus t -> Printf.sprintf "(%s)" (int_term_to_parseable_str t)
  | Plus (t1, t2) ->
      Printf.sprintf "(%s + %s)"
        (int_term_to_parseable_str t1)
        (int_term_to_parseable_str t2)
  | Times (t1, t2) ->
      Printf.sprintf "(%s * %s)"
        (int_term_to_parseable_str t1)
        (int_term_to_parseable_str t2)
  | _ -> raise Unsupported_Output

let term_to_parseable_str term =
  match term with
  | ITerm it -> int_term_to_parseable_str it
  | BitvTerm _ -> raise Unsupported_Output

let rec form_to_parseable_str form =
  match form with
  | True -> "true"
  | False -> "false"
  | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (form_to_parseable_str b1)
        (form_to_parseable_str b2)
  | Or (b1, b2) ->
      Printf.sprintf "(or %s %s)" (form_to_parseable_str b1)
        (form_to_parseable_str b2)
  | Not b -> Printf.sprintf "(not %s)" (form_to_parseable_str b)
  | Implies (b1, b2) ->
      Printf.sprintf "(=> %s %s)" (form_to_parseable_str b1)
        (form_to_parseable_str b2)
  | BVar v -> var_tostr (BoolVar v)
  | ABVar (BApp (ab, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (ABoolVar ab))
        (int_term_to_parseable_str i)
  | ABVar (BUnApp ab) -> Printf.sprintf "%s[?]" (var_tostr (ABoolVar ab))
  | Equals (t1, t2) ->
      Printf.sprintf "(= %s %s)" (term_to_parseable_str t1)
        (term_to_parseable_str t2)
  | Less (t1, t2) ->
      Printf.sprintf "(< %s %s)" (term_to_parseable_str t1)
        (term_to_parseable_str t2)
  | Iff (f1, f2) ->
      Printf.sprintf "(<-> %s %s)" (form_to_parseable_str f1)
        (form_to_parseable_str f2)
  | Exists (v, b) ->
      Printf.sprintf "((Exists %s %s). %s)" (var_tostr v)
        (match v with
        | IntTermVar _ -> "Int"
        | AIntTermVar _ -> "AInt"
        | BitvTermVar _ -> "Bitvec"
        | ABitvTermVar _ -> "ABitvec"
        | BoolVar _ -> "Bool"
        | ABoolVar _ -> "ABool")
        (form_to_parseable_str b)
  | Forall (v, b) ->
      Printf.sprintf "((Forall %s %s). %s)" (var_tostr v)
        (match v with
        | IntTermVar _ -> "Int"
        | AIntTermVar _ -> "AInt"
        | BitvTermVar _ -> "Bitvec"
        | ABitvTermVar _ -> "ABitvec"
        | BoolVar _ -> "Bool"
        | ABoolVar _ -> "ABool")
        (form_to_parseable_str b)
  | _ -> raise Unsupported_Output

(* and exp_to_parseable_str exp =
   match exp with Term t -> term_to_parseable_str t | Boolean b -> form_to_parseable_str b *)

(* Forall constructor that does not quantify over the variable if it is never used. Also, some helpers.*)
let rec is_new_var exp var_str =
  match exp with
  | Boolean True -> true
  | Boolean False -> true
  | Boolean (And (b1, b2)) ->
      is_new_var (Boolean b1) var_str && is_new_var (Boolean b2) var_str
  | Boolean (Or (b1, b2)) ->
      is_new_var (Boolean b1) var_str && is_new_var (Boolean b2) var_str
  | Boolean (Not b) -> is_new_var (Boolean b) var_str
  | Boolean (Implies (b1, b2)) ->
      is_new_var (Boolean b1) var_str && is_new_var (Boolean b2) var_str
  | Boolean (BVar v) -> var_tostr (BoolVar v) <> var_str
  | Boolean (ABVar (BUnApp v)) -> var_tostr (ABoolVar v) <> var_str
  | Boolean (ABVar (BApp (v, i))) ->
      var_tostr (ABoolVar v) <> var_str && int_term_tostr i <> var_str
  | Boolean (Equals (t1, t2)) ->
      is_new_var (Term t1) var_str && is_new_var (Term t2) var_str
  | Boolean (Less (t1, t2)) ->
      is_new_var (Term t1) var_str && is_new_var (Term t2) var_str
  | Boolean (Iff (b1, b2)) ->
      is_new_var (Boolean b1) var_str && is_new_var (Boolean b2) var_str
  | Boolean (Exists (v, b)) ->
      var_tostr v <> var_str && is_new_var (Boolean b) var_str
  | Boolean (Forall (v, b)) ->
      var_tostr v <> var_str && is_new_var (Boolean b) var_str
  | Boolean (BHole (s, arg_list)) ->
      List.for_all (fun arg -> is_new_var arg var_str) arg_list
      && s <> var_str (* Nice not to let new vars collide with hole names. *)
  | Boolean (T (f, b_loop, vmaps)) ->
      is_new_var (Boolean f) var_str
      (* && List.for_all
            (fun (b_old, b_new) ->
              var_str <> var_tostr (ABoolVar b_old)
              && var_str <> var_tostr (ABoolVar b_new))
            (VMap_AB.bindings b_map) *)
      && is_new_var (Boolean (ABVar (BUnApp b_loop))) var_str
      && List.for_all
           (fun (t_old, t_new) ->
             var_str <> var_tostr (AIntTermVar t_old)
             && var_str <> var_tostr (AIntTermVar t_new))
           (VMap_AIT.bindings vmaps.int_map)
      && List.for_all
           (fun (t_old, t_new) ->
             var_str <> var_tostr (ABitvTermVar t_old)
             && var_str <> var_tostr (ABitvTermVar t_new))
           (VMap_ABitvT.bindings vmaps.bitv_map)
  | Boolean (TPrime f) -> is_new_var (Boolean f) var_str
  | Term (ITerm (Int _)) -> true
  | Term (ITerm (ITVar v)) -> var_tostr (IntTermVar v) <> var_str
  | Term (ITerm (AITVar (ITUnApp v))) -> var_tostr (AIntTermVar v) <> var_str
  | Term (ITerm (AITVar (ITApp (v, i)))) ->
      var_tostr (AIntTermVar v) <> var_str && int_term_tostr i <> var_str
  | Term (ITerm (Minus t)) -> is_new_var (Term (ITerm t)) var_str
  | Term (ITerm (Plus (t1, t2))) ->
      is_new_var (Term (ITerm t1)) var_str
      && is_new_var (Term (ITerm t2)) var_str
  | Term (ITerm (Times (t1, t2))) ->
      is_new_var (Term (ITerm t1)) var_str
      && is_new_var (Term (ITerm t2)) var_str
  | Term (ITerm (THole (s, arg_list))) ->
      List.for_all (fun arg -> is_new_var arg var_str) arg_list
      && s <> var_str (* Nice not to let new vars collide with hole names. *)
  | Term (BitvTerm (Bitv _)) -> true
  | Term (BitvTerm (BitvTVar v)) -> var_tostr (BitvTermVar v) <> var_str
  | Term (BitvTerm (BitvUnarApp (_, btv))) ->
      is_new_var (Term (BitvTerm btv)) var_str
  | Term (BitvTerm (BitvBinarApp (_, btv1, btv2))) ->
      is_new_var (Term (BitvTerm btv1)) var_str
      && is_new_var (Term (BitvTerm btv2)) var_str
  | Term (BitvTerm (ABitvTVar (BitvTUnApp v))) ->
      var_tostr (ABitvTermVar v) <> var_str
  | Term (BitvTerm (ABitvTVar (BitvTApp (v, i)))) ->
      var_tostr (ABitvTermVar v) <> var_str && int_term_tostr i <> var_str
  | Term (BitvTerm (BitvTHole (s, arg_list))) ->
      List.for_all (fun arg -> is_new_var arg var_str) arg_list
      && s <> var_str (* Nice not to let new vars collide with hole names. *)

(* GENERAL UTILITIES *)
(* Determines if the formula has an existential quantifier. *)
let rec has_exists form =
  match form with
  | And (b1, b2) -> has_exists b1 || has_exists b2
  | Or (b1, b2) -> has_exists b1 || has_exists b2
  | Not b -> has_exists b
  | Implies (b1, b2) -> has_exists b1 || has_exists b2
  | Iff (b1, b2) -> has_exists b1 && has_exists b2
  | Exists _ -> true
  | Forall (_, b) -> has_exists b
  | BHole (_, arg_list) ->
      List.fold_left
        (fun bol arg ->
          bol && match arg with Term _ -> false | Boolean b -> has_exists b)
        false arg_list
  | T (f, _, _) -> has_exists f
  | TPrime f -> has_exists f
  | _ -> false

(* Determining which variables are free *)
let rec free_vars_int_term int_term bound_vars =
  match int_term with
  | Int _ -> VS.empty
  | ITVar v ->
      if VS.mem (IntTermVar v) bound_vars then VS.empty
      else VS.singleton (IntTermVar v)
  | AITVar (ITUnApp at) ->
      if VS.mem (AIntTermVar at) bound_vars then VS.empty
      else VS.singleton (AIntTermVar at)
  | AITVar (ITApp (at, i)) ->
      VS.union
        (if VS.mem (AIntTermVar at) bound_vars then VS.empty
         else VS.singleton (AIntTermVar at))
        (free_vars_int_term i bound_vars)
  | Minus t -> free_vars_int_term t bound_vars
  | Plus (t1, t2) ->
      VS.union
        (free_vars_int_term t1 bound_vars)
        (free_vars_int_term t2 bound_vars)
  | Times (t1, t2) ->
      VS.union
        (free_vars_int_term t1 bound_vars)
        (free_vars_int_term t2 bound_vars)
  | THole (_, arg_list) ->
      List.fold_left
        (fun set arg -> VS.union set (free_vars_exp arg bound_vars))
        VS.empty arg_list

and free_vars_bitv_term bitv bound_vars =
  match bitv with
  | Bitv _ -> VS.empty
  | BitvTVar v ->
      if VS.mem (BitvTermVar v) bound_vars then VS.empty
      else VS.singleton (BitvTermVar v)
  | BitvUnarApp (_, btv) -> free_vars_bitv_term btv bound_vars
  | BitvBinarApp (_, btv1, btv2) ->
      VS.union
        (free_vars_bitv_term btv1 bound_vars)
        (free_vars_bitv_term btv2 bound_vars)
  | ABitvTVar (BitvTUnApp at) ->
      if VS.mem (ABitvTermVar at) bound_vars then VS.empty
      else VS.singleton (ABitvTermVar at)
  | ABitvTVar (BitvTApp (at, i)) ->
      VS.union
        (if VS.mem (ABitvTermVar at) bound_vars then VS.empty
         else VS.singleton (ABitvTermVar at))
        (free_vars_int_term i bound_vars)
  | BitvTHole (_, arg_list) ->
      List.fold_left
        (fun set arg -> VS.union set (free_vars_exp arg bound_vars))
        VS.empty arg_list

and free_vars_term term =
  match term with
  | ITerm it -> free_vars_int_term it
  | BitvTerm btv -> free_vars_bitv_term btv

and free_vars form bound_vars =
  match form with
  | True -> VS.empty
  | False -> VS.empty
  | And (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Or (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Not b -> free_vars b bound_vars
  | Implies (b1, b2) ->
      VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | BVar v ->
      if VS.mem (BoolVar v) bound_vars then VS.empty
      else VS.singleton (BoolVar v)
  | ABVar (BUnApp ab) ->
      if VS.mem (ABoolVar ab) bound_vars then VS.empty
      else VS.singleton (ABoolVar ab)
  | ABVar (BApp (ab, i)) ->
      if VS.mem (ABoolVar ab) bound_vars then free_vars_int_term i bound_vars
      else VS.add (ABoolVar ab) (free_vars_int_term i bound_vars)
  | Equals (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Less (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Iff (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Exists (v, b) -> free_vars b (VS.add v bound_vars)
  | Forall (v, b) -> free_vars b (VS.add v bound_vars)
  | BHole (_, arg_list) ->
      List.fold_left
        (fun set arg -> VS.union set (free_vars_exp arg bound_vars))
        VS.empty arg_list
  | T (f, b_loop, vmaps) ->
      VS.add (ABoolVar b_loop)
        (VS.union (free_vars f bound_vars)
           (VS.union
              (VMap_AIT.bindings vmaps.int_map
              |> List.split
              |> (fun (a, b) -> List.append a b)
              |> List.map (fun v -> AIntTermVar v)
              |> VS.of_list)
              (VMap_ABitvT.bindings vmaps.bitv_map
              |> List.split
              |> (fun (a, b) -> List.append a b)
              |> List.map (fun v -> ABitvTermVar v)
              |> VS.of_list)))
  | TPrime f -> free_vars f bound_vars

and free_vars_exp exp bound_vars =
  match exp with
  | Term t -> free_vars_term t bound_vars
  | Boolean b -> free_vars b bound_vars

let fresh_var_name form exclude_set =
  let i = ref 1 in
  let frees = VS.elements (free_vars form VS.empty) in
  while
    (not (is_new_var (Boolean form) (Printf.sprintf "fresh%d" !i)))
    || List.exists
         (fun free_var ->
           String.starts_with
             ~prefix:(Printf.sprintf "fresh%d" !i)
             (var_tostr free_var))
         frees
    || List.exists
         (fun excl ->
           String.starts_with ~prefix:(Printf.sprintf "fresh%d" !i) excl)
         exclude_set
  do
    i := !i + 1
  done;
  (* Printf.printf "%s: fresh%d\n" (form_tostr form) !i; *)
  Printf.sprintf "fresh%d" !i

let forall v form =
  if is_new_var (Boolean form) (var_tostr v) then form else Forall (v, form)

(* Predicate transformers and associated helper functions.*)
(* Given a int_term, collects the set of all terms that appear as indices. *)
let rec get_index_int_terms int_term =
  match int_term with
  | AITVar (ITApp (_, i)) -> TS.add i (get_index_int_terms i)
  | Minus t -> get_index_int_terms t
  | Plus (t1, t2) -> TS.union (get_index_int_terms t1) (get_index_int_terms t2)
  | Times (t1, t2) -> TS.union (get_index_int_terms t1) (get_index_int_terms t2)
  (* TODO: Technically, we need to handle THoles here. *)
  | _ -> TS.empty

let rec get_index_bitv_terms bitv =
  match bitv with
  | Bitv _ -> TS.empty
  | BitvTVar _ -> TS.empty
  | BitvUnarApp (_, btv) -> get_index_bitv_terms btv
  | BitvBinarApp (_, btv1, btv2) ->
      TS.union (get_index_bitv_terms btv1) (get_index_bitv_terms btv2)
  | ABitvTVar (BitvTApp (_, i)) -> TS.add i (get_index_int_terms i)
  | ABitvTVar (BitvTUnApp _) -> TS.empty
  (* TODO: Technically, we need to handle THoles here. *)
  | _ -> TS.empty

let get_index_terms term =
  match term with
  | ITerm it -> get_index_int_terms it
  | BitvTerm bitv -> get_index_bitv_terms bitv

(* Given a int_term, an index int_term i and a map from vars to vars (x, y), replaces all occurrences of x[i] by y[i]. *)
let rec subs_vector_int_vars_by_index_term_helper int_term target_i
    (old_vars_to_new : int_term_array_var VMap_AIT.t) =
  match int_term with
  | AITVar (ITApp (at, i)) ->
      if i = target_i && VMap_AIT.mem at old_vars_to_new then
        AITVar (ITApp (VMap_AIT.find at old_vars_to_new, i))
      else int_term
  | Minus t ->
      Minus
        (subs_vector_int_vars_by_index_term_helper t target_i old_vars_to_new)
  | Plus (t1, t2) ->
      Plus
        ( subs_vector_int_vars_by_index_term_helper t1 target_i old_vars_to_new,
          subs_vector_int_vars_by_index_term_helper t2 target_i old_vars_to_new
        )
  | Times (t1, t2) ->
      Times
        ( subs_vector_int_vars_by_index_term_helper t1 target_i old_vars_to_new,
          subs_vector_int_vars_by_index_term_helper t2 target_i old_vars_to_new
        )
  (* TODO: Technically, we need to handle THoles here. *)
  | _ -> int_term

(* Given a int_term, a list of index terms i and a map from vars to vars (x, y), replaces all occurrences of x[i] by y[i]. *)
let subs_vector_int_vars_by_index_terms int_term targets_i
    (old_vars_to_new : int_term_array_var VMap_AIT.t) =
  List.fold_left
    (fun f i -> subs_vector_int_vars_by_index_term_helper f i old_vars_to_new)
    int_term targets_i

let rec subs_vector_bitv_vars_by_index_term_helper bitv_term target_i
    (old_vars_to_new : bitv_term_array_var VMap_ABitvT.t) =
  match bitv_term with
  | Bitv _ -> bitv_term
  | BitvTVar _ -> bitv_term
  | BitvUnarApp (op, btv) ->
      BitvUnarApp
        ( op,
          subs_vector_bitv_vars_by_index_term_helper btv target_i
            old_vars_to_new )
  | BitvBinarApp (op, btv1, btv2) ->
      BitvBinarApp
        ( op,
          subs_vector_bitv_vars_by_index_term_helper btv1 target_i
            old_vars_to_new,
          subs_vector_bitv_vars_by_index_term_helper btv2 target_i
            old_vars_to_new )
  | ABitvTVar (BitvTApp (at, i)) ->
      if i = target_i && VMap_ABitvT.mem at old_vars_to_new then
        ABitvTVar (BitvTApp (VMap_ABitvT.find at old_vars_to_new, i))
      else bitv_term
  | ABitvTVar (BitvTUnApp _) -> bitv_term
  (* TODO: Technically, we need to handle THoles here. *)
  | _ -> bitv_term

(* Given a bitv_term, a list of index terms i and a map from vars to vars (x, y), replaces all occurrences of x[i] by y[i]. *)
let subs_vector_bitv_vars_by_index_terms bitv_term targets_i
    (old_vars_to_new : bitv_term_array_var VMap_ABitvT.t) =
  List.fold_left
    (fun f i -> subs_vector_bitv_vars_by_index_term_helper f i old_vars_to_new)
    bitv_term targets_i

let subs_vector_vars_by_index_terms term targets_i (old_vars_to_new : vmaps) =
  match term with
  | ITerm it ->
      ITerm
        (subs_vector_int_vars_by_index_terms it targets_i
           old_vars_to_new.int_map)
  | BitvTerm bitv ->
      BitvTerm
        (subs_vector_bitv_vars_by_index_terms bitv targets_i
           old_vars_to_new.bitv_map)

(* Given a formula form, a bool_array_var bloop to branch on, and a map variables (x_old, y_new), applies a T transformation, substituting y_new's for x_old's in deactivated branches. *)
let rec t_transform form bloop (old_vars_to_new_term_vmaps : vmaps) =
  (* Given a int_term t, returns a list of (positive variables, formulas) for all 2^n combinations of bt[i] for the indices i appearing in t. If no indices appear, then it's just True.
     E.g., [([i, 1], bt[i] && bt[1]], ([i], bt[i] && !bt[1]), ([1], !bt[i] && bt[1]), ([], !bt[i] && !bt[1])] *)
  let t_guards_primed t start_options =
    TS.fold
      (fun int_term partial_perms_list ->
        List.append
          (List.map
             (fun (pos_list, conj) ->
               (pos_list, And (Not (ABVar (BApp (bloop, int_term))), conj)))
             partial_perms_list)
          (List.map
             (fun (pos_list, conj) ->
               ( List.cons int_term pos_list,
                 And (ABVar (BApp (bloop, int_term)), conj) ))
             partial_perms_list))
      (get_index_terms t) start_options
  in
  let t_guards t = t_guards_primed t [ ([], True) ] in
  let t_trns f = t_transform f bloop old_vars_to_new_term_vmaps in
  match form with
  (* | ABVar (App (ab, i)) ->
      Or
        ( And
            ( ABVar (App (bloop, i)),
              ABVar (App (VMap_AB.find ab old_vars_to_new_bool, i)) ),
          And (Not (ABVar (App (bloop, i))), ABVar (App (ab, i))) ) *)
  | ABVar (BUnApp _) -> raise Applying_Transformation_On_Incomplete_Index
  | And (b1, b2) -> And (t_trns b1, t_trns b2)
  | Or (b1, b2) -> Or (t_trns b1, t_trns b2)
  | Not b -> Not (t_trns b)
  | Implies (b1, b2) -> Implies (t_trns b1, t_trns b2)
  | Iff (b1, b2) -> Iff (t_trns b1, t_trns b2)
  | Equals (t1, t2) ->
      (* Get index int_term combinations in t1 and t2 (e.g., [([i, 1], bt[i] && bt[1]], ([i], bt[i] && !bt[1]), ... ])*)
      let permutations = t_guards_primed t2 (t_guards t1) in
      (* Conjunct t1=t2[y[int_term]/x[int_term]] to each index int_term combination. *)
      let make_substituted_phrases =
        List.map
          (fun (pos_indices, condition) ->
            And
              ( condition,
                Equals
                  ( subs_vector_vars_by_index_terms t1 pos_indices
                      old_vars_to_new_term_vmaps,
                    subs_vector_vars_by_index_terms t2 pos_indices
                      old_vars_to_new_term_vmaps ) ))
          permutations
      in
      (* Disjunct all possible options together. *)
      List.fold_left
        (fun running_perms new_perm -> Or (running_perms, new_perm))
        False make_substituted_phrases
  | Less (t1, t2) ->
      (* Get index int_term combinations in t1 and t2 (e.g., [([i, 1], bt[i] && bt[1]], ([i], bt[i] && !bt[1]), ... ])*)
      let permutations = t_guards_primed t2 (t_guards t1) in
      (* Conjunct t1=t2[y[int_term]/x[int_term]] to each index int_term combination. *)
      let make_substituted_phrases =
        List.map
          (fun (pos_indices, condition) ->
            And
              ( condition,
                Less
                  ( subs_vector_vars_by_index_terms t1 pos_indices
                      old_vars_to_new_term_vmaps,
                    subs_vector_vars_by_index_terms t2 pos_indices
                      old_vars_to_new_term_vmaps ) ))
          permutations
      in
      (* Disjunct all possible options together. *)
      List.fold_left
        (fun running_perms new_perm -> Or (running_perms, new_perm))
        False make_substituted_phrases
  | Exists (v, b) -> Exists (v, t_trns b)
  | Forall (v, b) -> Forall (v, t_trns b)
  | BHole _ -> T (form, bloop, old_vars_to_new_term_vmaps)
  | T (_, _, _) -> form
  | TPrime _ -> form (*TODO: Make sure this is the correct behavior*)
  | _ -> form

(* Given a formula form, applies a T' transformation. *)
let rec t_prime_transform form =
  (* Given two int_terms t1 and t2, returns a conjunction of all bt[i] for the indices i appearing in t1 or t2. If no indices appear, then it's just True.
     E.g., x[i] = x[1] goes to bt[i] && bt[1] *)
  let t_prime_guard t1 t2 =
    TS.fold
      (fun index_term form -> And (form, ABVar (BApp (BT, index_term))))
      (TS.union (get_index_terms t1) (get_index_terms t2))
      True
  in
  match form with
  | ABVar (BApp (ab, i)) -> Implies (ABVar (BApp (BT, i)), ABVar (BApp (ab, i)))
  | ABVar (BUnApp _) -> raise Applying_Transformation_On_Incomplete_Index
  | And (b1, b2) -> And (t_prime_transform b1, t_prime_transform b2)
  | Or (b1, b2) -> Or (t_prime_transform b1, t_prime_transform b2)
  | Not b -> Not (t_prime_transform b)
  | Implies (b1, b2) -> Implies (t_prime_transform b1, t_prime_transform b2)
  | Iff (b1, b2) -> Iff (t_prime_transform b1, t_prime_transform b2)
  | Equals (t1, t2) -> Implies (t_prime_guard t1 t2, form)
  | Less (t1, t2) -> Implies (t_prime_guard t1 t2, form)
  | Exists (v, b) -> Exists (v, t_prime_transform b)
  | Forall (v, b) -> Forall (v, t_prime_transform b)
  | BHole _ -> TPrime form
  | T (_, _, _) -> form (*TODO: This is not the correct behavior; fix later.*)
  | TPrime _ -> form (*TODO: Not correct behavior.*)
  | _ -> form

(* Functions to perform variable substitution in formulas and terms. *)
(* For all int_term arrays which are indexed by a hole (UnApp's), set the index to the given int_term. *)
let rec set_int_term_index holey_term index =
  match holey_term with
  | AITVar (ITUnApp var) -> AITVar (ITApp (var, index))
  | Minus t -> Minus (set_int_term_index t index)
  | Plus (t1, t2) ->
      Plus (set_int_term_index t1 index, set_int_term_index t2 index)
  | Times (t1, t2) ->
      Times (set_int_term_index t1 index, set_int_term_index t2 index)
  | THole (s, arg_list) ->
      THole (s, List.map (fun arg -> set_exp_index arg index) arg_list)
  | _ -> holey_term

and set_bitv_term_index holey_term index =
  match holey_term with
  | Bitv _ -> holey_term
  | BitvTVar _ -> holey_term
  | BitvUnarApp (op, btv) -> BitvUnarApp (op, set_bitv_term_index btv index)
  | BitvBinarApp (op, btv1, btv2) ->
      BitvBinarApp
        (op, set_bitv_term_index btv1 index, set_bitv_term_index btv2 index)
  | ABitvTVar (BitvTUnApp var) -> ABitvTVar (BitvTApp (var, index))
  | ABitvTVar (BitvTApp (_, _)) -> holey_term
  | BitvTHole (s, arg_list) ->
      BitvTHole (s, List.map (fun arg -> set_exp_index arg index) arg_list)

and set_term_index holey_term index =
  match holey_term with
  | ITerm it -> ITerm (set_int_term_index it index)
  | BitvTerm bitv -> BitvTerm (set_bitv_term_index bitv index)

and set_form_index holey_form index =
  match holey_form with
  | True -> holey_form
  | False -> holey_form
  | And (b1, b2) -> And (set_form_index b1 index, set_form_index b2 index)
  | Or (b1, b2) -> Or (set_form_index b1 index, set_form_index b2 index)
  | Not b -> Not (set_form_index b index)
  | Implies (b1, b2) ->
      Implies (set_form_index b1 index, set_form_index b2 index)
  | BVar _ -> holey_form
  | ABVar (BUnApp var) -> ABVar (BApp (var, index))
  | ABVar (BApp (ab, i)) -> ABVar (BApp (ab, set_int_term_index i index))
  | Equals (t1, t2) -> Equals (set_term_index t1 index, set_term_index t2 index)
  | Less (t1, t2) -> Less (set_term_index t1 index, set_term_index t2 index)
  | Iff (b1, b2) -> Iff (set_form_index b1 index, set_form_index b2 index)
  | Exists (v, b) -> Exists (v, set_form_index b index)
  | Forall (v, b) -> Forall (v, set_form_index b index)
  | BHole (s, arg_list) ->
      BHole (s, List.map (fun arg -> set_exp_index arg index) arg_list)
  | _ -> raise Set_Index_Inside_Predicate

and set_exp_index holey_exp index =
  match holey_exp with
  | Term t -> Term (set_term_index t index)
  | Boolean b -> Boolean (set_form_index b index)

(* Compute maximum index referenced if they are all ints. *)
let max a b = if a > b then a else b

let rec max_index_helper current_max exp =
  match exp with
  | Term (ITerm (AITVar (ITApp (_, Int i)))) -> max current_max i
  | Term (ITerm (Minus t)) -> max_index_helper current_max (Term (ITerm t))
  | Term (ITerm (Plus (t1, t2))) ->
      max_index_helper
        (max_index_helper current_max (Term (ITerm t2)))
        (Term (ITerm t1))
  | Term (ITerm (Times (t1, t2))) ->
      max_index_helper
        (max_index_helper current_max (Term (ITerm t2)))
        (Term (ITerm t1))
  | Term (ITerm (THole (_, el))) ->
      List.fold_left (fun cur exp -> max_index_helper cur exp) current_max el
  | Boolean (ABVar (BApp (_, Int i))) -> max current_max i
  | Boolean (And (f1, f2)) ->
      max_index_helper (max_index_helper current_max (Boolean f2)) (Boolean f1)
  | Boolean (Or (f1, f2)) ->
      max_index_helper (max_index_helper current_max (Boolean f2)) (Boolean f1)
  | Boolean (Not f) -> max_index_helper current_max (Boolean f)
  | Boolean (Implies (f1, f2)) ->
      max_index_helper (max_index_helper current_max (Boolean f2)) (Boolean f1)
  | Boolean (Equals (t1, t2)) ->
      max_index_helper (max_index_helper current_max (Term t2)) (Term t1)
  | Boolean (Less (t1, t2)) ->
      max_index_helper (max_index_helper current_max (Term t2)) (Term t1)
  | Boolean (Iff (f1, f2)) ->
      max_index_helper (max_index_helper current_max (Boolean f2)) (Boolean f1)
  | Boolean (Exists (_, f)) -> max_index_helper current_max (Boolean f)
  | Boolean (Forall (_, f)) -> max_index_helper current_max (Boolean f)
  | Boolean (BHole (_, el)) ->
      List.fold_left (fun cur exp -> max_index_helper cur exp) current_max el
  | Boolean (T (f, _, _)) -> max_index_helper current_max (Boolean f)
  | Boolean (TPrime f) -> max_index_helper current_max (Boolean f)
  | Term (BitvTerm (Bitv _)) -> current_max
  | Term (BitvTerm (BitvUnarApp (_, btv))) ->
      max_index_helper current_max (Term (BitvTerm btv))
  | Term (BitvTerm (BitvBinarApp (_, btv1, btv2))) ->
      max_index_helper
        (max_index_helper current_max (Term (BitvTerm btv2)))
        (Term (BitvTerm btv1))
  | Term (BitvTerm (BitvTVar _)) -> current_max
  | Term (BitvTerm (ABitvTVar (BitvTApp (_, Int i)))) -> max current_max i
  | Term (BitvTerm (ABitvTVar (BitvTUnApp _))) -> current_max
  | _ -> current_max

let max_index exp = max_index_helper 0 exp

(* Given a int_term, a int_term_var to replace, and a newt int_term to replace it with, does the replacement. *)
let rec subs_int_term_simple int_term oldv newt =
  match (int_term, newt) with
  | ITVar v, _ -> if v <> oldv then int_term else newt
  | AITVar (ITApp (at, i)), ITVar v ->
      if i = ITVar oldv then AITVar (ITApp (at, ITVar v)) else int_term
  | Minus t, _ -> Minus (subs_int_term_simple t oldv newt)
  | Plus (t1, t2), _ ->
      Plus (subs_int_term_simple t1 oldv newt, subs_int_term_simple t2 oldv newt)
  | Times (t1, t2), _ ->
      Times
        (subs_int_term_simple t1 oldv newt, subs_int_term_simple t2 oldv newt)
      (* TODO: Implement THole logic here. *)
  | _, _ -> int_term

(* Given a bitv_term, a bitv_term_var to replace, and a newt bitv_term to replace it with, does the replacement. *)
let rec subs_bitv_term_simple bitv_term oldv newt =
  match bitv_term with
  | Bitv _ -> bitv_term
  | BitvTVar v -> if v <> oldv then bitv_term else newt
  | ABitvTVar _ -> bitv_term
  | BitvUnarApp (op, btv) ->
      BitvUnarApp (op, subs_bitv_term_simple btv oldv newt)
  | BitvBinarApp (op, btv1, btv2) ->
      BitvBinarApp
        ( op,
          subs_bitv_term_simple btv1 oldv newt,
          subs_bitv_term_simple btv2 oldv newt )
      (* TODO: Implement THole logic here. *)
  | _ -> bitv_term

(* Given a bitv_term, an int_term_var to replace, and a newt int_term to replace it with, does the replacement in indices of the term. *)
let rec subs_bitv_term_index_simple bitv_term oldv newt =
  match (bitv_term, newt) with
  | Bitv _, _ -> bitv_term
  | BitvTVar _, _ -> bitv_term
  | ABitvTVar (BitvTApp (at, i)), ITVar v ->
      if i = ITVar oldv then ABitvTVar (BitvTApp (at, ITVar v)) else bitv_term
  | BitvUnarApp (op, btv), _ ->
      BitvUnarApp (op, subs_bitv_term_index_simple btv oldv newt)
  | BitvBinarApp (op, btv1, btv2), _ ->
      BitvBinarApp
        ( op,
          subs_bitv_term_index_simple btv1 oldv newt,
          subs_bitv_term_index_simple btv2 oldv newt )
      (* TODO: Implement THole logic here. *)
  | _, _ -> raise Unsupported_Output

let subs_term_simple term oldv newt =
  match (term, oldv, newt) with
  | ITerm it, IntTermVar oldintv, ITerm newintt ->
      ITerm (subs_int_term_simple it oldintv newintt)
      (* To substitute a bvec variable... *)
  | BitvTerm btv, BitvTermVar oldbitvv, BitvTerm newbitvt ->
      BitvTerm (subs_bitv_term_simple btv oldbitvv newbitvt)
      (* To substitute a bvec index variable... *)
  | BitvTerm btv, IntTermVar oldintv, ITerm newintt ->
      BitvTerm (subs_bitv_term_index_simple btv oldintv newintt)
  | _ -> raise (Subs_Type_Mismatch 1)

(*Takes int_term called int_term and swaps AIntTermVar oldv with the int_term newt*)
let rec subs_int_term_vector_state int_term oldv newt =
  match int_term with
  | AITVar (ITApp (at, i)) ->
      if at = oldv then set_int_term_index newt i else int_term
  | AITVar (ITUnApp at) -> if at = oldv then newt else int_term
  | Minus t -> Minus (subs_int_term_vector_state t oldv newt)
  | Plus (t1, t2) ->
      Plus
        ( subs_int_term_vector_state t1 oldv newt,
          subs_int_term_vector_state t2 oldv newt )
  | Times (t1, t2) ->
      Times
        ( subs_int_term_vector_state t1 oldv newt,
          subs_int_term_vector_state t2 oldv newt )
      (* TODO: Implement THole logic here. *)
  | _ -> int_term

let rec subs_bitv_term_vector_state bitv_term oldv newt =
  match bitv_term with
  | ABitvTVar (BitvTApp (at, i)) ->
      if at = oldv then set_bitv_term_index newt i else bitv_term
  | ABitvTVar (BitvTUnApp at) -> if at = oldv then newt else bitv_term
  | BitvUnarApp (op, btv) ->
      BitvUnarApp (op, subs_bitv_term_vector_state btv oldv newt)
  | BitvBinarApp (op, btv1, btv2) ->
      BitvBinarApp
        ( op,
          subs_bitv_term_vector_state btv1 oldv newt,
          subs_bitv_term_vector_state btv2 oldv newt )
  (* TODO: Implement THole logic here. *)
  | _ -> bitv_term

let subs_term_vector_state term oldv newt =
  match (term, oldv, newt) with
  | ITerm it, AIntTermVar oldaintv, ITerm newintt ->
      ITerm (subs_int_term_vector_state it oldaintv newintt)
  | BitvTerm bitvt, ABitvTermVar oldabitvv, BitvTerm newbitvt ->
      BitvTerm (subs_bitv_term_vector_state bitvt oldabitvv newbitvt)
  | _ -> raise (Subs_Type_Mismatch 2)

let rec subs form oldv newe =
  match (form, oldv, newe) with
  | _, BoolVar _, Term _ -> raise (Subs_Type_Mismatch 3)
  | _, ABoolVar _, Term _ -> raise (Subs_Type_Mismatch 4)
  | _, IntTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 5)
  | _, AIntTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 6)
  | _, BitvTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 5)
  | _, ABitvTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 6)
  | True, _, _ -> form
  | False, _, _ -> form
  | And (b1, b2), _, _ -> And (subs b1 oldv newe, subs b2 oldv newe)
  | Or (b1, b2), _, _ -> Or (subs b1 oldv newe, subs b2 oldv newe)
  | Not b, _, _ -> Not (subs b oldv newe)
  | Implies (b1, b2), _, _ -> Implies (subs b1 oldv newe, subs b2 oldv newe)
  | BVar v, BoolVar old, Boolean b -> if v <> old then form else b
  | BVar _, _, _ -> form
  | ABVar (BApp (ab, i)), ABoolVar bvs, Boolean newb ->
      if ab = bvs then set_form_index newb i else form
  | ABVar (BUnApp ab), ABoolVar bvs, Boolean newb ->
      if ab = bvs then newb else form
  | ABVar (BApp (ab, i)), IntTermVar t, Term (ITerm newt) ->
      ABVar (BApp (ab, subs_int_term_simple i t newt))
  | ABVar (BApp (ab, i)), AIntTermVar vst, Term (ITerm newt) ->
      ABVar (BApp (ab, subs_int_term_vector_state i vst newt))
  | ABVar _, _, _ -> form
  | Equals (t1, t2), IntTermVar _, Term t ->
      Equals (subs_term_simple t1 oldv t, subs_term_simple t2 oldv t)
  | Equals (t1, t2), AIntTermVar _, Term t ->
      Equals (subs_term_vector_state t1 oldv t, subs_term_vector_state t2 oldv t)
  | Equals (t1, t2), BitvTermVar _, Term t ->
      Equals (subs_term_simple t1 oldv t, subs_term_simple t2 oldv t)
  | Equals (t1, t2), ABitvTermVar _, Term t ->
      Equals (subs_term_vector_state t1 oldv t, subs_term_vector_state t2 oldv t)
  | Equals (_, _), _, _ -> form (*Small Optimization*)
  | Less (t1, t2), IntTermVar _, Term t ->
      Less (subs_term_simple t1 oldv t, subs_term_simple t2 oldv t)
  | Less (t1, t2), AIntTermVar _, Term t ->
      Less (subs_term_vector_state t1 oldv t, subs_term_vector_state t2 oldv t)
  | Less (t1, t2), BitvTermVar _, Term t ->
      Less (subs_term_simple t1 oldv t, subs_term_simple t2 oldv t)
  | Less (t1, t2), ABitvTermVar _, Term t ->
      Less (subs_term_vector_state t1 oldv t, subs_term_vector_state t2 oldv t)
  | Less (_, _), _, _ -> form
  | Iff (b1, b2), _, _ -> Iff (subs b1 oldv newe, subs b2 oldv newe)
  | Forall (v, b), _, _ ->
      if v <> oldv then Forall (v, subs b oldv newe)
      else form
        (* match newe with
           | Boolean (BVar vb) -> Forall (BoolVar vb, subs b oldv newe)
           | Boolean (ABVar (UnApp vb)) -> Forall (ABoolVar vb, subs b oldv newe)
           | Term (ITVar vt) -> Forall (IntTermVar vt, subs b oldv newe)
           | Term (AITVar (UnApp vt)) -> Forall (AIntTermVar vt, subs b oldv newe)
           | _ -> raise Subs_Exp_In_Quant) *)
  | Exists (v, b), _, _ ->
      if v <> oldv then Exists (v, subs b oldv newe)
      else form
        (* match newe with
           | Boolean (BVar vb) -> Exists (BoolVar vb, subs b oldv newe)
           | Boolean (ABVar (UnApp vb)) -> Exists (ABoolVar vb, subs b oldv newe)
           | Term (ITVar vt) -> Exists (IntTermVar vt, subs b oldv newe)
           | Term (AITVar (UnApp vt)) -> Exists (AIntTermVar vt, subs b oldv newe)
           | _ -> raise Subs_Exp_In_Quant) *)
  | BHole (s, arg_list), _, _ ->
      BHole
        ( s,
          List.map
            (fun arg ->
              match (arg, oldv, newe) with
              | _, IntTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 7)
              | _, AIntTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 8)
              | _, BitvTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 9)
              | _, ABitvTermVar _, Boolean _ -> raise (Subs_Type_Mismatch 10)
              | _, BoolVar _, Term _ -> raise (Subs_Type_Mismatch 11)
              | _, ABoolVar _, Term _ -> raise (Subs_Type_Mismatch 12)
              | Boolean b, _, _ -> Boolean (subs b oldv newe)
              | Term t, IntTermVar _, Term tterm ->
                  Term (subs_term_simple t oldv tterm)
              | Term t, BitvTermVar _, Term tterm ->
                  Term (subs_term_simple t oldv tterm)
              | Term t, AIntTermVar _, Term tterm ->
                  Term (subs_term_vector_state t oldv tterm)
              | Term t, ABitvTermVar _, Term tterm ->
                  Term (subs_term_vector_state t oldv tterm)
              | Term _, BoolVar _, _ -> arg
              | Term _, ABoolVar _, _ -> arg)
            arg_list )
  | T (f, b_map, t_map), _, _ ->
      T (subs f oldv newe, b_map, t_map) (*TODO: Must also sub map vars.*)
  | TPrime f, _, _ -> TPrime (subs f oldv newe)

let subs_several form var_exp_list =
  List.fold_left (fun f (v, exp) -> subs f v exp) form var_exp_list

let rec sub_holes (form : formula)
    (hole_map : ((string * variable list) * formula) list) =
  match form with
  | And (b1, b2) -> And (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | Or (b1, b2) -> Or (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | Not b -> Not (sub_holes b hole_map)
  | Implies (b1, b2) -> Implies (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | Iff (t1, t2) -> Iff (sub_holes t1 hole_map, sub_holes t2 hole_map)
  | Exists (v, b) -> Exists (v, sub_holes b hole_map)
  | Forall (v, b) -> Forall (v, sub_holes b hole_map)
  | BHole (s, arg_list) ->
      if List.exists (fun ((a, _), _) -> a = s) hole_map then
        let (_, old_args), body =
          List.find (fun ((a, _), _) -> a = s) hole_map
        in
        List.fold_left2
          (fun formul old_arg new_arg -> subs formul old_arg new_arg)
          body old_args arg_list
      else form
  | T (f, bloop, t_map) -> t_transform (sub_holes f hole_map) bloop t_map
  | TPrime f -> t_prime_transform (sub_holes f hole_map)
  | _ -> form

(* Functions to transform formulas over many indices to formulas over only a few indices when vector length is bounded. *)
let indexer var_name index = Printf.sprintf "%s_finitevscpy_%d" var_name index

let rec int_term_finite_vs_transformer int_term =
  match int_term with
  | AITVar (ITApp (ET, Int i)) -> ITVar (T (indexer "e_t" i))
  | AITVar (ITApp (T v, Int i)) -> ITVar (T (indexer v i))
  | Minus t -> Minus (int_term_finite_vs_transformer t)
  | Plus (t1, t2) ->
      Plus (int_term_finite_vs_transformer t1, int_term_finite_vs_transformer t2)
  | Times (t1, t2) ->
      Times
        (int_term_finite_vs_transformer t1, int_term_finite_vs_transformer t2)
  | _ -> int_term

let rec bitv_term_finite_vs_transformer bitv_term =
  match bitv_term with
  | Bitv _ -> bitv_term
  | BitvTVar _ -> bitv_term
  | ABitvTVar (BitvTUnApp _) -> raise Unsupported_Output
  | BitvUnarApp (op, btv) ->
      BitvUnarApp (op, bitv_term_finite_vs_transformer btv)
  | BitvBinarApp (op, btv1, btv2) ->
      BitvBinarApp
        ( op,
          bitv_term_finite_vs_transformer btv1,
          bitv_term_finite_vs_transformer btv2 )
  | ABitvTVar (BitvTApp (ET, Int i)) -> BitvTVar (T (indexer "e_t" i))
  | ABitvTVar (BitvTApp (T v, Int i)) -> BitvTVar (T (indexer v i))
  | _ -> bitv_term

let term_finite_vs_transformer term =
  match term with
  | ITerm it -> ITerm (int_term_finite_vs_transformer it)
  | BitvTerm bitv -> BitvTerm (bitv_term_finite_vs_transformer bitv)

let rec bool_finite_vs_transformer max_ind form =
  if max_ind = 0 then form else
  (match form with
  | ABVar (BApp (BT, Int i)) -> BVar (B (indexer "b_t" i))
  | ABVar (BApp (B v, Int i)) -> BVar (B (indexer v i))
  | And (f1, f2) ->
      And
        ( bool_finite_vs_transformer max_ind f1,
          bool_finite_vs_transformer max_ind f2 )
  | Or (f1, f2) ->
      Or
        ( bool_finite_vs_transformer max_ind f1,
          bool_finite_vs_transformer max_ind f2 )
  | Not f -> Not (bool_finite_vs_transformer max_ind f)
  | Implies (f1, f2) ->
      Implies
        ( bool_finite_vs_transformer max_ind f1,
          bool_finite_vs_transformer max_ind f2 )
  | Equals (t1, t2) ->
      Equals (term_finite_vs_transformer t1, term_finite_vs_transformer t2)
  | Less (t1, t2) ->
      Less (term_finite_vs_transformer t1, term_finite_vs_transformer t2)
  | Iff (f1, f2) ->
      Iff
        ( bool_finite_vs_transformer max_ind f1,
          bool_finite_vs_transformer max_ind f2 )
  | Exists (v, f) -> (
      match v with
      | IntTermVar _ -> Exists (v, bool_finite_vs_transformer max_ind f)
      | BitvTermVar _ -> Exists (v, bool_finite_vs_transformer max_ind f)
      | BoolVar _ -> Exists (v, bool_finite_vs_transformer max_ind f)
      | AIntTermVar (T t) ->
          List.fold_left
            (fun form i -> Exists (IntTermVar (T (indexer t i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | ABitvTermVar (T t) ->
          List.fold_left
            (fun form i -> Exists (BitvTermVar (T (indexer t i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | ABoolVar (B b) ->
          List.fold_left
            (fun form i -> Exists (BoolVar (B (indexer b i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | _ -> raise Unsupported_Output)
  | Forall (v, f) -> (
      match v with
      | IntTermVar _ -> Forall (v, bool_finite_vs_transformer max_ind f)
      | BitvTermVar _ -> Forall (v, bool_finite_vs_transformer max_ind f)
      | BoolVar _ -> Forall (v, bool_finite_vs_transformer max_ind f)
      | AIntTermVar (T t) ->
          List.fold_left
            (fun form i -> Forall (IntTermVar (T (indexer t i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | ABitvTermVar (T t) ->
          List.fold_left
            (fun form i -> Forall (BitvTermVar (T (indexer t i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | ABoolVar (B b) ->
          List.fold_left
            (fun form i -> Forall (BoolVar (B (indexer b i)), form))
            (bool_finite_vs_transformer max_ind f)
            (List.init max_ind (fun n -> n + 1))
      | _ -> raise Unsupported_Output)
  | BHole (h, arg_list) ->
      let big_args_list =
        List.concat
          (List.init max_ind (fun n ->
               List.map
                 (fun exp ->
                   exp_finite_vs_transformer max_ind
                     (set_exp_index exp (Int (n + 1))))
                 arg_list))
      in
      BHole (h, big_args_list)
  | T (f, b_loop, vmaps) ->
      (* A list of (positive variables, formulas) for all 2^n combinations of bt[i] for the indices i appearing in t. If no indices appear, then it's just True.
         E.g., [([1, 2], bloop[1] && bloop[2]], ([1], bloop[1] && !bloop[2]), ([2], !bloop[1] && bloop[2]), ([], !bloop[1] && !bloop[2])] *)
      let t_guards =
        List.fold_left
          (fun partial_perms_list index ->
            List.append
              (List.map
                 (fun (pos_list, conj) ->
                   (pos_list, And (Not (ABVar (BApp (b_loop, Int index))), conj)))
                 partial_perms_list)
              (List.map
                 (fun (pos_list, conj) ->
                   ( List.cons index pos_list,
                     And (ABVar (BApp (b_loop, Int index)), conj) ))
                 partial_perms_list))
          [ ([], True) ]
          (List.init max_ind (fun n -> n + 1))
      in
      let expanded_hole = bool_finite_vs_transformer max_ind f in
      let implied_subbed_holes =
        List.map
          (fun (off_inds, prec) ->
            Implies
              ( bool_finite_vs_transformer max_ind prec,
                List.fold_left
                  (fun hole ind ->
                    List.fold_left
                      (fun hole (oldv, newv) ->
                        subs hole
                          (IntTermVar
                             (T (indexer (var_tostr (AIntTermVar oldv)) ind)))
                          (Term
                             (ITerm
                                (ITVar
                                   (T
                                      (indexer
                                         (var_tostr (AIntTermVar newv))
                                         ind))))))
                      (List.fold_left
                         (fun hole (oldv, newv) ->
                           subs hole
                             (BitvTermVar
                                (T (indexer (var_tostr (ABitvTermVar oldv)) ind)))
                             (Term
                                (BitvTerm
                                   (BitvTVar
                                      (T
                                         (indexer
                                            (var_tostr (ABitvTermVar newv))
                                            ind))))))
                         hole
                         (VMap_ABitvT.bindings vmaps.bitv_map))
                      (VMap_AIT.bindings vmaps.int_map))
                  expanded_hole off_inds ))
          t_guards
      in
      let conjoined_holes =
        List.fold_left
          (fun form hole -> And (form, hole))
          True implied_subbed_holes
      in
      (* In the finite case, we don't reason about infinite vectors so we can expand explicitly.
         We perform an across-the-board conversion of holes over vector states to holes over the entries.
         This is a bit of a hack to use all the infinite vs machinery and change it at the very end, but let's not worry about that. *)
      conjoined_holes
  | TPrime f -> TPrime (bool_finite_vs_transformer max_ind f)
  | _ -> form)

and exp_finite_vs_transformer max_ind exp =
  match exp with
  | Term t -> Term (term_finite_vs_transformer t)
  | Boolean b -> Boolean (bool_finite_vs_transformer max_ind b)
