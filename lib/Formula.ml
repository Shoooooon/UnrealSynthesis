open Variable

exception Subs_Type_Mismatch
exception Subs_Exp_In_Quant
exception Incorrect_Implication of string

type term = Int of int | TVar of term_var | Plus of term * term

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

type exp = Term of term | Boolean of boolean_exp
type formula = boolean_exp

let rec term_tostr term =
  match term with
  | Int i -> Printf.sprintf "%d" i
  | TVar v -> var_tostr (TermVar v)
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

let rec subs_term term oldv newt =
  match term with
  | Int _ -> term
  | TVar v -> if v <> oldv then term else newt
  | Plus (t1, t2) -> Plus (subs_term t1 oldv newt, subs_term t2 oldv newt)

let rec subs form oldv newv =
  match (form, oldv, newv) with
  | True, _, _ -> form
  | False, _, _ -> form
  | And (b1, b2), _, _ -> And (subs b1 oldv newv, subs b2 oldv newv)
  | Or (b1, b2), _, _ -> Or (subs b1 oldv newv, subs b2 oldv newv)
  | Not b, _, _ -> Not (subs b oldv newv)
  | Implies (b1, b2), _, _ -> Implies (subs b1 oldv newv, subs b2 oldv newv)
  | BVar v, BoolVar old, Term _ -> if v <> old then form else raise Subs_Type_Mismatch
  | BVar v, BoolVar old, Boolean b -> if v <> old then form else b
  | BVar _, _, _ -> form
  | Equals (t1, t2), TermVar old, Term t -> Equals (subs_term t1 old t, subs_term t2 old t)
  | Equals (_, _), _, _ -> form (*Small Optimization*)
  | Less (t1, t2), TermVar old, Term t -> Less (subs_term t1 old t, subs_term t2 old t)
  | Less (_, _), _, _ -> form
  | Iff (b1, b2), _, _ -> Iff (subs b1 oldv newv, subs b2 oldv newv)
  | Forall (v, b), _, _ -> (
      if v <> oldv then Forall (v, subs b oldv newv)
      else
        match newv with
        | Boolean (BVar vb) -> Forall ((BoolVar vb), subs b oldv newv)
        | Term (TVar vt) -> Forall ((TermVar vt), subs b oldv newv)
        | _ -> raise Subs_Exp_In_Quant)
  | Exists (v, b), _, _ -> (
      if v <> oldv then Exists (v, subs b oldv newv)
      else
        match newv with
        | Boolean (BVar vb) -> Exists ((BoolVar vb), subs b oldv newv)
        | Term (TVar vt) -> Exists ((TermVar vt), subs b oldv newv)
        | _ -> raise Subs_Exp_In_Quant)

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
  | Boolean (BVar v) -> (var_tostr (BoolVar v)) <> var_str
  | Boolean (Equals (t1, t2)) ->
      is_new_var (Term t1) var_str && is_new_var (Term t2) var_str
  | Boolean (Less (t1, t2)) ->
      is_new_var (Term t1) var_str && is_new_var (Term t2) var_str
  | Boolean (Iff (b1, b2)) ->
      is_new_var (Boolean b1) var_str && is_new_var (Boolean b2) var_str
  | Boolean (Exists (v, b)) -> (var_tostr v) <> var_str && is_new_var (Boolean b) var_str
  | Boolean (Forall (v, b)) -> (var_tostr v) <> var_str && is_new_var (Boolean b) var_str
  | Term (Int _) -> true
  | Term (TVar v) -> (var_tostr (TermVar v)) <> var_str
  | Term (Plus (t1, t2)) -> is_new_var (Term t1) var_str && is_new_var (Term t2) var_str

let fresh_var_name form exclude_set=
  let i = ref 1 in
  while ((not (is_new_var (Boolean form) (Printf.sprintf "fresh%d" !i))) || (List.mem (Printf.sprintf "fresh%d" !i) exclude_set)) do
    i := !i + 1
  done;
  (* Printf.printf "%s: fresh%d\n" (form_tostr form) !i; *)
  Printf.sprintf "fresh%d" !i

(* Logic for discharging implications --
   The idea will be to spawn processes to invoke Z3 or whichever solver.
   We will generate a function that collects the process and makes sure it verified correctly, returning if not.
   At the end of the proof construction, we will run these functions; if none of them error, the proof is correct.
   Otherwise, an implication is incorrect (or a check did not complete).*)

let rec to_smt_helper_term term =
  match term with
  | Int i -> Printf.sprintf "%d" i
  | TVar v -> var_tostr (TermVar v)
  | Plus (t1, t2) ->
      Printf.sprintf "(+ %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)

let rec to_smt_helper form =
  match form with
  | True -> "true"
  | False -> "false"
  | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Or (b1, b2) ->
      Printf.sprintf "(or %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Not b -> Printf.sprintf "(not %s)" (to_smt_helper b)
  | Implies (b1, b2) ->
      Printf.sprintf "(=> %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | BVar v -> var_tostr (BoolVar v)
  | Equals (t1, t2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)
  | Less (t1, t2) ->
      Printf.sprintf "(< %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)
  | Iff (b1, b2) ->
    Printf.sprintf "(= %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Exists (TermVar v, b) ->
    Printf.sprintf "(exists ((%s Int) ) %s)" (var_tostr (TermVar v)) (to_smt_helper b)
  | Exists (BoolVar v, b) ->
    Printf.sprintf "(exists ((%s Bool) ) %s)" (var_tostr (BoolVar v)) (to_smt_helper b)
  | Forall (TermVar v, b) ->
    Printf.sprintf "(forall ((%s Int) ) %s)" (var_tostr (TermVar v)) (to_smt_helper b)
  | Forall (BoolVar v, b) ->
    Printf.sprintf "(forall ((%s Bool) ) %s)" (var_tostr (BoolVar v)) (to_smt_helper b)
  
module VS = Set.Make (Variable)

let rec free_vars_term term bound_vars =
  match term with
  | Int _ -> VS.empty
  | TVar v -> if VS.mem (TermVar v) bound_vars then VS.empty else VS.singleton (TermVar v)
  | Plus (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)

let rec free_vars form bound_vars =
  match form with
  | True -> VS.empty
  | False -> VS.empty
  | And (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Or (b1, b2) -> VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Not b -> free_vars b bound_vars
  | Implies (b1, b2) ->
      VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | BVar v -> if VS.mem (BoolVar v) bound_vars then VS.empty else VS.singleton (BoolVar v)
  | Equals (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Less (t1, t2) ->
      VS.union (free_vars_term t1 bound_vars) (free_vars_term t2 bound_vars)
  | Iff (b1, b2) ->
    VS.union (free_vars b1 bound_vars) (free_vars b2 bound_vars)
  | Exists (v, b) -> free_vars b (VS.add v bound_vars)
  | Forall (v, b) -> free_vars b (VS.add v bound_vars)

let to_negated_smt form name =
  Printf.sprintf
    ";%s\n\
     (set-info :status unknown)\n\
     %s(assert\n\
     (not\n\
     %s\n\
     )\n\
    \ )\n\
     (check-sat)"
    name
    (VS.fold
       (fun var str ->
          match var with
            BoolVar _ -> Printf.sprintf "%s(declare-const %s Bool)\n" str (var_tostr var)
          | TermVar _ -> Printf.sprintf "%s(declare-const %s Int)\n" str (var_tostr var))
        (free_vars form VS.empty)
       "")
    (to_smt_helper form)

(* Spawn a process to check the implication.
   Return a blocking function that confirms implication is valid. *)
type file_pair = {name_num : int; form : formula}
let file_logger = (ref []) and file_counter = (ref 0)
   let implies hyp conc =
      (* Write SMT2 File *)
      (* let filename_map character =
        match character with
        | '=' -> 'e'
        | '>' -> 'g'
        | '<' -> 'l'
        | '+' -> 'p'
        | '!' -> 'n'
        | '&' -> 'a'
        | c -> c
      in *)
      (* If the file named by our fresh counter exists, skip the number. It could be important to someone else. *)
      while ((Sys.file_exists (Printf.sprintf "Implication%d.smt" !file_counter))) do
        file_counter := !file_counter + 1;
      done;
      (* If we have not dispatched a query for this implication... *)
      if not (List.mem (Implies (hyp, conc)) (List.map (fun a -> a.form) !file_logger)) then 
        let filename_pref = Printf.sprintf "Implication%d" !file_counter
        (* String.map filename_map (form_tostr (Implies (hyp, conc))) *)
        in
          (* Set up the file and record in the structure. *)
          let oc = open_out (Printf.sprintf "%s.smt" filename_pref) in
          Printf.fprintf oc "%s" (to_negated_smt (Implies (hyp, conc)) "test");
          close_out oc;
          file_logger := (List.cons {name_num = !file_counter; form = Implies (hyp, conc)} !file_logger);  
          file_counter := !file_counter;
          (* Fork and exec a query *)
          let kid_pid = Unix.fork () in
            if kid_pid = 0 then (
              let fd =
                Unix.openfile
                  (Printf.sprintf "%s.out" filename_pref)
                  [ O_CREAT; O_WRONLY ] 0
              in
              Unix.dup2 fd Unix.stdout;
              Unix.execvp "z3"
                (Array.of_list [ "z3"; "-smt2"; Printf.sprintf "%s.smt" filename_pref ]))
            else
              (* Return function that collects SMT result *)
              lazy
                (if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then false
                else
                  let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
                  input_line f_channel = "unsat")
        (* TODO: It might be good to have the below behavior be the default in both branches, but waitpid might be better. *)
      (* If the query was already run, just read the result. *)
      else
        let name_num = (List.find (fun a -> a.form = Implies (hyp, conc)) !file_logger).name_num in let filename_pref = Printf.sprintf "Implication%d" name_num in
        lazy
          (while not (Sys.file_exists (Printf.sprintf "%s.out" filename_pref)) do
            Unix.sleep 1
          done;
          let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
          input_line f_channel = "unsat")
