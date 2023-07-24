open Variable

exception Subs_Type_Mismatch
exception Subs_Exp_In_Quant
exception Incorrect_Implication of string

type term =
  | Int of int
  | TVar of term_var
  | Minus of term
  | Plus of term * term

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

and exp = Term of term | Boolean of boolean_exp

type formula = boolean_exp

(* Specialty Constructors for parsing - TODO make exists and forall quantify more than 1 variable*)

(* toStr Methods *)
let rec term_tostr term =
  match term with
  | Int i -> Printf.sprintf "%d" i
  | TVar v -> var_tostr (TermVar v)
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
let rec subs_term term oldv newt =
  match term with
  | Int _ -> term
  | TVar v -> if v <> oldv then term else newt
  | Minus t -> Minus (subs_term t oldv newt)
  | Plus (t1, t2) -> Plus (subs_term t1 oldv newt, subs_term t2 oldv newt)

let rec subs form oldv newv =
  match (form, oldv, newv) with
  | _, BoolVar _, Term _ -> raise Subs_Type_Mismatch
  | _, TermVar _, Boolean _ -> raise Subs_Type_Mismatch
  | True, _, _ -> form
  | False, _, _ -> form
  | And (b1, b2), _, _ -> And (subs b1 oldv newv, subs b2 oldv newv)
  | Or (b1, b2), _, _ -> Or (subs b1 oldv newv, subs b2 oldv newv)
  | Not b, _, _ -> Not (subs b oldv newv)
  | Implies (b1, b2), _, _ -> Implies (subs b1 oldv newv, subs b2 oldv newv)
  | BVar v, BoolVar old, Boolean b -> if v <> old then form else b
  | BVar _, _, _ -> form
  | Equals (t1, t2), TermVar old, Term t ->
      Equals (subs_term t1 old t, subs_term t2 old t)
  | Equals (_, _), _, _ -> form (*Small Optimization*)
  | Less (t1, t2), TermVar old, Term t ->
      Less (subs_term t1 old t, subs_term t2 old t)
  | Less (_, _), _, _ -> form
  | Iff (b1, b2), _, _ -> Iff (subs b1 oldv newv, subs b2 oldv newv)
  | Forall (v, b), _, _ -> (
      if v <> oldv then Forall (v, subs b oldv newv)
      else
        match newv with
        | Boolean (BVar vb) -> Forall (BoolVar vb, subs b oldv newv)
        | Term (TVar vt) -> Forall (TermVar vt, subs b oldv newv)
        | _ -> raise Subs_Exp_In_Quant)
  | Exists (v, b), _, _ -> (
      if v <> oldv then Exists (v, subs b oldv newv)
      else
        match newv with
        | Boolean (BVar vb) -> Exists (BoolVar vb, subs b oldv newv)
        | Term (TVar vt) -> Exists (TermVar vt, subs b oldv newv)
        | _ -> raise Subs_Exp_In_Quant)
  | Hole (s, arg_list), _, _ ->
      Hole
        ( s,
          List.map
            (fun arg ->
              match (arg, oldv, newv) with
              | _, TermVar _, Boolean _ -> raise Subs_Type_Mismatch
              | _, BoolVar _, Term _ -> raise Subs_Type_Mismatch
              | Boolean b, _, _ -> Boolean (subs b oldv newv)
              | Term t, TermVar old, Term tterm -> Term (subs_term t old tterm)
              | Term _, BoolVar _, _ -> arg)
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
  | True -> form
  | False -> form
  | And (b1, b2) -> And (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | Or (b1, b2) -> Or (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | Not b -> Not (sub_holes b hole_map)
  | Implies (b1, b2) -> Implies (sub_holes b1 hole_map, sub_holes b2 hole_map)
  | BVar _ -> form
  | Equals (_, _) -> form
  | Less (_, _) -> form
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
