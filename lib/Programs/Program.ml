open NonTerminal
open Logic.Variable
module VS = Set.Make (Logic.Variable)

type numeric_exp =
  | Zero
  | One
  | Var of string
  | Plus of numeric_exp * numeric_exp
  | ITE of boolean_exp * numeric_exp * numeric_exp
  | NNTerm of numeric_exp nonterminal

and boolean_exp =
  | True
  | False
  | Not of boolean_exp
  | And of boolean_exp * boolean_exp
  | Or of boolean_exp * boolean_exp
  | Equals of numeric_exp * numeric_exp
  | Less of numeric_exp * numeric_exp
  | BNTerm of boolean_exp nonterminal

type stmt =
  | Assign of string * numeric_exp
  | Seq of stmt * stmt
  | ITE of boolean_exp * stmt * stmt
  | While of boolean_exp * Logic.Formula.formula * stmt
  | SNTerm of stmt nonterminal

module SNTS = Set.Make (struct
  type t = stmt nonterminal

  let compare = compare
end)

type program = Numeric of numeric_exp | Boolean of boolean_exp | Stmt of stmt

let rec prog_tostr prog =
  match prog with
  | Numeric Zero -> "0"
  | Numeric One -> "1"
  | Numeric (Var x) -> x
  | Numeric (Plus (n1, n2)) ->
      Printf.sprintf "(%s + %s)" (prog_tostr (Numeric n1))
        (prog_tostr (Numeric n2))
  | Numeric (ITE (b, n1, n2)) ->
      Printf.sprintf "(if %s then %s else %s)" (prog_tostr (Boolean b))
        (prog_tostr (Numeric n1)) (prog_tostr (Numeric n2))
  | Numeric (NNTerm nterm) -> to_str nterm
  | Boolean True -> "T"
  | Boolean False -> "F"
  | Boolean (Not b) -> Printf.sprintf "!%s" (prog_tostr (Boolean b))
  | Boolean (And (b1, b2)) ->
      Printf.sprintf "(%s && %s)" (prog_tostr (Boolean b1))
        (prog_tostr (Boolean b2))
  | Boolean (Or (b1, b2)) ->
      Printf.sprintf "(%s || %s)" (prog_tostr (Boolean b1))
        (prog_tostr (Boolean b2))
  | Boolean (Equals (n1, n2)) ->
      Printf.sprintf "(%s = %s)" (prog_tostr (Numeric n1))
        (prog_tostr (Numeric n2))
  | Boolean (Less (n1, n2)) ->
      Printf.sprintf "(%s < %s)" (prog_tostr (Numeric n1))
        (prog_tostr (Numeric n2))
  | Boolean (BNTerm nterm) -> to_str nterm
  | Stmt (Assign (v, n)) ->
      Printf.sprintf "(%s := %s)"
        (prog_tostr (Numeric (Var v)))
        (prog_tostr (Numeric n))
  | Stmt (Seq (s1, s2)) ->
      Printf.sprintf "(%s; %s)" (prog_tostr (Stmt s1)) (prog_tostr (Stmt s2))
  | Stmt (ITE (b, s1, s2)) ->
      Printf.sprintf "(if %s then %s else %s)" (prog_tostr (Boolean b))
        (prog_tostr (Stmt s1)) (prog_tostr (Stmt s2))
  | Stmt (While (b, inv, s)) ->
      Printf.sprintf "(while %s do (Inv=%s) %s)" (prog_tostr (Boolean b))
        (Logic.Formula.form_tostr inv) (prog_tostr (Stmt s))
  | Stmt (SNTerm nterm) -> to_str nterm

(* Returns vars (as formula vars) whose values may be changed by any program in the set.
   This is good to have for the adapt rule. *)
let rec reassigned_vars_helper prog examined =
  match prog with
  | Numeric _ -> VS.empty
  | Boolean _ -> VS.empty
  | Stmt (Assign (v, _)) -> VS.singleton (TermVar (T v))
  (* | Stmt (Assign (_, _)) -> VS.empty *)
  | Stmt (Seq (s1, s2)) ->
      VS.union
        (reassigned_vars_helper (Stmt s1) examined)
        (reassigned_vars_helper (Stmt s2) examined)
  | Stmt (ITE (_, s1, s2)) ->
      VS.union
        (reassigned_vars_helper (Stmt s1) examined)
        (reassigned_vars_helper (Stmt s2) examined)
  | Stmt (While (_, _, s)) -> reassigned_vars_helper (Stmt s) examined
  | Stmt (SNTerm n) ->
      if SNTS.mem n examined then VS.empty
      else
        List.fold_left
          (fun a b -> VS.union a b)
          VS.empty
          (List.map
             (fun expansion ->
               reassigned_vars_helper (Stmt expansion) (SNTS.add n examined))
             n.expansions)

let reassigned_vars prog =
  VS.add (TermVar ET)
    (VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty))
