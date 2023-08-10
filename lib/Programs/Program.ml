open NonTerminal
open Logic.Variable

(* TODO: Expand support for program constants *)
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
        (Logic.Formula.form_tostr inv)
        (prog_tostr (Stmt s))
  | Stmt (SNTerm nterm) -> to_str nterm

(* Returns vars (as formula vars) whose values may be changed by any program in the set.
   This is good to have for the adapt rule. *)
let rec reassigned_vars_helper prog examined =
  match prog with
  | Numeric _ -> VS.empty
  | Boolean _ -> VS.empty
  | Stmt (Assign (v, _)) -> VS.singleton (TermVar (T v))
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
             (NonTerminal.expand n))

let reassigned_vars prog =
  VS.add (TermVar ET)
    (VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty))

(* Substitution of nonterminals according to given grammar. Useful when recursively defining grammars. *)
type grammar = {
  grammar_num : numeric_exp nonterminal list;
  grammar_bool : boolean_exp nonterminal list;
  grammar_stmt : stmt nonterminal list;
}

let rec subs_nonterms_numeric lazy_grammar num =
  let grammar = Lazy.force lazy_grammar in
  match num with
  | Plus (n1, n2) ->
      Plus
        ( subs_nonterms_numeric lazy_grammar n1,
          subs_nonterms_numeric lazy_grammar n2 )
  | ITE (b, n1, n2) ->
      ITE
        ( subs_nonterms_boolean lazy_grammar b,
          subs_nonterms_numeric lazy_grammar n1,
          subs_nonterms_numeric lazy_grammar n2 )
  | NNTerm nt ->
      if List.exists (fun n -> n.name = nt.name) grammar.grammar_num then
        NNTerm (List.find (fun n -> n.name = nt.name) grammar.grammar_num)
      else num
  | _ -> num

and subs_nonterms_boolean lazy_grammar boolean =
  let grammar = Lazy.force lazy_grammar in
  match boolean with
  | Not b -> Not (subs_nonterms_boolean lazy_grammar b)
  | And (b1, b2) ->
      And
        ( subs_nonterms_boolean lazy_grammar b1,
          subs_nonterms_boolean lazy_grammar b2 )
  | Or (b1, b2) ->
      Or
        ( subs_nonterms_boolean lazy_grammar b1,
          subs_nonterms_boolean lazy_grammar b2 )
  | Equals (n1, n2) ->
      Equals
        ( subs_nonterms_numeric lazy_grammar n1,
          subs_nonterms_numeric lazy_grammar n2 )
  | Less (n1, n2) ->
      Less
        ( subs_nonterms_numeric lazy_grammar n1,
          subs_nonterms_numeric lazy_grammar n2 )
  | BNTerm nt ->
      if List.exists (fun b -> b.name = nt.name) grammar.grammar_bool then
        BNTerm (List.find (fun b -> b.name = nt.name) grammar.grammar_bool)
      else boolean
  | _ -> boolean

and subs_nonterms_stmt lazy_grammar stmt =
  let grammar = Lazy.force lazy_grammar in
  match stmt with
  | Assign (s, n) -> Assign (s, subs_nonterms_numeric lazy_grammar n)
  | Seq (s1, s2) ->
      Seq
        (subs_nonterms_stmt lazy_grammar s1, subs_nonterms_stmt lazy_grammar s2)
  | ITE (b, s1, s2) ->
      ITE
        ( subs_nonterms_boolean lazy_grammar b,
          subs_nonterms_stmt lazy_grammar s1,
          subs_nonterms_stmt lazy_grammar s2 )
  | While (b, form, s) ->
      While
        ( subs_nonterms_boolean lazy_grammar b,
          form,
          subs_nonterms_stmt lazy_grammar s )
  | SNTerm nt ->
      if List.exists (fun s -> s.name = nt.name) grammar.grammar_stmt then
        SNTerm (List.find (fun s -> s.name = nt.name) grammar.grammar_stmt)
      else stmt

let subs_nonterms lazy_grammar program =
  match program with
  | Numeric n -> Numeric (subs_nonterms_numeric lazy_grammar n)
  | Boolean b -> Boolean (subs_nonterms_boolean lazy_grammar b)
  | Stmt s -> Stmt (subs_nonterms_stmt lazy_grammar s)
