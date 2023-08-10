open Variable

exception Subs_Type_Mismatch
exception Subs_Exp_In_Quant
exception Incorrect_Implication of string

type term =
  | Int of int
  | TVar of term_var
  | ATVar of term_array_app
  | Minus of term
  | Plus of term * term

and term_array_app = App of term_array_var * term | UnApp of term_array_var

module TS = Set.Make (struct
  type t = term

  let compare = compare
end)

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

and bool_array_app = App of bool_array_var * term | UnApp of bool_array_var
and exp = Term of term | Boolean of boolean_exp

type formula = boolean_exp

(* Specialty Constructors for parsing - TODO make exists and forall quantify more than 1 variable*)

(* toStr Methods *)
let rec term_tostr term =
  match term with
  | Int i -> Printf.sprintf "%d" i
  | TVar v -> var_tostr (TermVar v)
  | ATVar (App (at, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (ATermVar at)) (term_tostr i)
  | ATVar (UnApp at) -> Printf.sprintf "%s[?]" (var_tostr (ATermVar at))
  | Minus t -> Printf.sprintf "(%s)" (term_tostr t)
  | Plus (t1, t2) -> Printf.sprintf "(%s + %s)" (term_tostr t1) (term_tostr t2)

let rec form_tostr form =
  match form with
  | True -> "T"
  | False -> "F"
  | And (b1, b2) -> Printf.sprintf "(%s && %s)" (form_tostr b1) (form_tostr b2)
  | Or (b1, b2) -> Printf.sprintf "(%s || %s)" (form_tostr b1) (form_tostr b2)
  | Not b -> Printf.sprintf "!%s" (form_tostr b)
  | Implies (b1, b2) ->
      Printf.sprintf "(%s => %s)" (form_tostr b1) (form_tostr b2)
  | BVar v -> var_tostr (BoolVar v)
  | ABVar (App (ab, i)) ->
      Printf.sprintf "%s[%s]" (var_tostr (ABoolVar ab)) (term_tostr i)
  | ABVar (UnApp ab) -> Printf.sprintf "%s[?]" (var_tostr (ABoolVar ab))
  | Equals (t1, t2) ->
      Printf.sprintf "(%s == %s)" (term_tostr t1) (term_tostr t2)
  | Less (t1, t2) -> Printf.sprintf "(%s < %s)" (term_tostr t1) (term_tostr t2)
  | Iff (t1, t2) -> Printf.sprintf "(%s <-> %s)" (form_tostr t1) (form_tostr t2)
  | Exists (v, b) ->
      Printf.sprintf "((Exists %s). %s)" (var_tostr v) (form_tostr b)
  | Forall (v, b) ->
      Printf.sprintf "((Forall %s). %s)" (var_tostr v) (form_tostr b)
  | Hole (s, arg_list) ->
      Printf.sprintf "(%s (%s))" s
        (String.concat ", " (List.map exp_tostr arg_list))
  
and exp_tostr exp =
  match exp with Term t -> term_tostr t | Boolean b -> form_tostr b



(* Functions to perform variable substitution in formulas and terms. *)
(* For all term arrays which are indexed by a hole (UnApp's), set the index to the given term. *)
let rec set_term_index holey_term index =
  match holey_term with
  | ATVar (UnApp var) -> ATVar (App (var, index))
  | Minus t -> Minus (set_term_index t index)
  | Plus (t1, t2) -> Plus (set_term_index t1 index, set_term_index t2 index)
  | _ -> holey_term

let rec set_form_index holey_form index =
  match holey_form with
  | True -> holey_form
  | False -> holey_form
  | And (b1, b2) -> And (set_form_index b1 index, set_form_index b2 index)
  | Or (b1, b2) -> Or (set_form_index b1 index, set_form_index b2 index)
  | Not b -> Not (set_form_index b index)
  | Implies (b1, b2) ->
      Implies (set_form_index b1 index, set_form_index b2 index)
  | BVar _ -> holey_form
  | ABVar (UnApp var) -> ABVar (App (var, index))
  | ABVar (App (ab, i)) -> ABVar (App (ab, set_term_index i index))
  | Equals (t1, t2) -> Equals (set_term_index t1 index, set_term_index t2 index)
  | Less (t1, t2) -> Less (set_term_index t1 index, set_term_index t2 index)
  | Iff (b1, b2) -> Iff (set_form_index b1 index, set_form_index b2 index)
  | Exists (v, b) -> Exists (v, set_form_index b index)
  | Forall (v, b) -> Forall (v, set_form_index b index)
  | Hole (s, arg_list) ->
      Hole (s, List.map (fun arg -> set_exp_index arg index) arg_list)

and set_exp_index holey_exp index =
  match holey_exp with
  | Term t -> Term (set_term_index t index)
  | Boolean b -> Boolean (set_form_index b index)

(* Given a term, a term_var to replace, and a newt term to replace it with, does the replacement. *)
let rec subs_term_simple term oldv newt =
  match (term, newt) with
  | TVar v, _ -> if v <> oldv then term else newt
  | ATVar (App (at, i)), TVar v ->
      if i = TVar oldv then ATVar (App (at, TVar v)) else term
  | Minus t, _ -> Minus (subs_term_simple t oldv newt)
  | Plus (t1, t2), _ ->
      Plus (subs_term_simple t1 oldv newt, subs_term_simple t2 oldv newt)
  | _, _ -> term

(*Takes term and swaps ATermVar with newt*)
let rec subs_term_vector_state term oldv newt =
  match term with
  | ATVar (App (at, i)) -> if at = oldv then set_term_index newt i else term
  | ATVar (UnApp at) -> if at = oldv then newt else term
  | Minus t -> Minus (subs_term_vector_state t oldv newt)
  | Plus (t1, t2) ->
      Plus
        ( subs_term_vector_state t1 oldv newt,
          subs_term_vector_state t2 oldv newt )
  | _ -> term

let rec subs form oldv newe =
  match (form, oldv, newe) with
  | _, BoolVar _, Term _ -> raise Subs_Type_Mismatch
  | _, ABoolVar _, Term _ -> raise Subs_Type_Mismatch
  | _, TermVar _, Boolean _ -> raise Subs_Type_Mismatch
  | _, ATermVar _, Boolean _ -> raise Subs_Type_Mismatch
  | True, _, _ -> form
  | False, _, _ -> form
  | And (b1, b2), _, _ -> And (subs b1 oldv newe, subs b2 oldv newe)
  | Or (b1, b2), _, _ -> Or (subs b1 oldv newe, subs b2 oldv newe)
  | Not b, _, _ -> Not (subs b oldv newe)
  | Implies (b1, b2), _, _ -> Implies (subs b1 oldv newe, subs b2 oldv newe)
  | BVar v, BoolVar old, Boolean b -> if v <> old then form else b
  | BVar _, _, _ -> form
  | ABVar (App (ab, i)), ABoolVar bvs, Boolean newb ->
      if ab = bvs then set_form_index newb i else form
  | ABVar (UnApp ab), ABoolVar bvs, Boolean newb ->
      if ab = bvs then newb else form
  | ABVar (App (ab, i)), TermVar t, Term newt ->
      ABVar (App (ab, subs_term_simple i t newt))
  | ABVar (App (ab, i)), ATermVar vst, Term newt ->
      ABVar (App (ab, subs_term_vector_state i vst newt))
  | ABVar _, _, _ -> form
  | Equals (t1, t2), TermVar old, Term t ->
      Equals (subs_term_simple t1 old t, subs_term_simple t2 old t)
  | Equals (t1, t2), ATermVar old, Term t ->
      Equals (subs_term_vector_state t1 old t, subs_term_vector_state t2 old t)
  | Equals (_, _), _, _ -> form (*Small Optimization*)
  | Less (t1, t2), TermVar old, Term t ->
      Less (subs_term_simple t1 old t, subs_term_simple t2 old t)
  | Less (t1, t2), ATermVar old, Term t ->
      Less (subs_term_vector_state t1 old t, subs_term_vector_state t2 old t)
  | Less (_, _), _, _ -> form
  | Iff (b1, b2), _, _ -> Iff (subs b1 oldv newe, subs b2 oldv newe)
  | Forall (v, b), _, _ -> (
      if v <> oldv then Forall (v, subs b oldv newe)
      else
        match newe with
        | Boolean (BVar vb) -> Forall (BoolVar vb, subs b oldv newe)
        | Boolean (ABVar (UnApp vb)) -> Forall (ABoolVar vb, subs b oldv newe)
        | Term (TVar vt) -> Forall (TermVar vt, subs b oldv newe)
        | Term (ATVar (UnApp vt)) -> Forall (ATermVar vt, subs b oldv newe)
        | _ -> raise Subs_Exp_In_Quant)
  | Exists (v, b), _, _ -> (
      if v <> oldv then Exists (v, subs b oldv newe)
      else
        match newe with
        | Boolean (BVar vb) -> Exists (BoolVar vb, subs b oldv newe)
        | Boolean (ABVar (UnApp vb)) -> Exists (ABoolVar vb, subs b oldv newe)
        | Term (TVar vt) -> Exists (TermVar vt, subs b oldv newe)
        | Term (ATVar (UnApp vt)) -> Exists (ATermVar vt, subs b oldv newe)
        | _ -> raise Subs_Exp_In_Quant)
  | Hole (s, arg_list), _, _ ->
      Hole
        ( s,
          List.map
            (fun arg ->
              match (arg, oldv, newe) with
              | _, TermVar _, Boolean _ -> raise Subs_Type_Mismatch
              | _, ATermVar _, Boolean _ -> raise Subs_Type_Mismatch
              | _, BoolVar _, Term _ -> raise Subs_Type_Mismatch
              | _, ABoolVar _, Term _ -> raise Subs_Type_Mismatch
              | Boolean b, _, _ -> Boolean (subs b oldv newe)
              | Term t, TermVar old, Term tterm ->
                  Term (subs_term_simple t old tterm)
              | Term t, ATermVar old, Term tterm ->
                  Term (subs_term_vector_state t old tterm)
              | Term _, BoolVar _, _ -> arg
              | Term _, ABoolVar _, _ -> arg)
            arg_list )

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
  | Boolean (ABVar (UnApp v)) -> var_tostr (ABoolVar v) <> var_str
  | Boolean (ABVar (App (v, i))) ->
      var_tostr (ABoolVar v) <> var_str && term_tostr i <> var_str
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
  | Boolean (Hole (s, arg_list)) ->
      List.for_all (fun arg -> is_new_var arg var_str) arg_list
      && s <> var_str (* Nice not to let new vars collide with hole names. *)
  | Term (Int _) -> true
  | Term (TVar v) -> var_tostr (TermVar v) <> var_str
  | Term (ATVar (UnApp v)) -> var_tostr (ATermVar v) <> var_str
  | Term (ATVar (App (v, i))) ->
      var_tostr (ATermVar v) <> var_str && term_tostr i <> var_str
  | Term (Minus t) -> is_new_var (Term t) var_str
  | Term (Plus (t1, t2)) ->
      is_new_var (Term t1) var_str && is_new_var (Term t2) var_str

let fresh_var_name form exclude_set =
  let i = ref 1 in
  while
    (not (is_new_var (Boolean form) (Printf.sprintf "fresh%d" !i)))
    || List.mem (Printf.sprintf "fresh%d" !i) exclude_set
  do
    i := !i + 1
  done;
  (* Printf.printf "%s: fresh%d\n" (form_tostr form) !i; *)
  Printf.sprintf "fresh%d" !i

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
  | Hole (s, arg_list) ->
      if List.exists (fun ((a, _), _) -> a = s) hole_map then
        let (_, old_args), body =
          List.find (fun ((a, _), _) -> a = s) hole_map
        in
        List.fold_left2
          (fun formul old_arg new_arg -> subs formul old_arg new_arg)
          body old_args arg_list
      else form
  | _ -> form
