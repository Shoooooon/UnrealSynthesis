type numeric_exp =
  | Zero
  | One
  | Var of string
  | Plus of numeric_exp * numeric_exp
  | ITE of boolean_exp * numeric_exp * numeric_exp

and boolean_exp =
  | True
  | False
  | Not of boolean_exp
  | And of boolean_exp * boolean_exp
  | Or of boolean_exp * boolean_exp
  | Equals of numeric_exp * numeric_exp
  | Less of numeric_exp * numeric_exp

type stmt =
  | Assign of string * numeric_exp
  | Seq of stmt * stmt
  | ITE of boolean_exp * stmt * stmt
  | While of boolean_exp * Formula.formula * stmt

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
        (Formula.form_tostr inv) (prog_tostr (Stmt s))
