open NonTerminal
open Logic.Variable

(* TODO: Expand support for program constants *)
type numeric_exp =
  | Int of int
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
  | Numeric (Int i) -> Printf.sprintf "%d" i
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

(* Prints program in the same form as input is expected. *)
let rec prog_to_parseable_str prog =
  match prog with
  | Numeric (Int i) -> Printf.sprintf "%d" i
  | Numeric (Var v) -> v
  | Numeric (Plus (n1, n2)) ->
      Printf.sprintf "(+ %s %s)"
        (prog_to_parseable_str (Numeric n1))
        (prog_to_parseable_str (Numeric n2))
  | Numeric (ITE (b, n1, n2)) ->
      Printf.sprintf "(if %s then %s else %s)"
        (prog_to_parseable_str (Boolean b))
        (prog_to_parseable_str (Numeric n1))
        (prog_to_parseable_str (Numeric n2))
  | Numeric (NNTerm nterm) -> Printf.sprintf "Nonterm %s" nterm.name
  | Boolean True -> "true"
  | Boolean False -> "false"
  | Boolean (Not b) ->
      Printf.sprintf "(not %s)" (prog_to_parseable_str (Boolean b))
  | Boolean (And (b1, b2)) ->
      Printf.sprintf "(and %s %s)"
        (prog_to_parseable_str (Boolean b1))
        (prog_to_parseable_str (Boolean b2))
  | Boolean (Or (b1, b2)) ->
      Printf.sprintf "(or %s %s)"
        (prog_to_parseable_str (Boolean b1))
        (prog_to_parseable_str (Boolean b2))
  | Boolean (Equals (n1, n2)) ->
      Printf.sprintf "(= %s %s)"
        (prog_to_parseable_str (Numeric n1))
        (prog_to_parseable_str (Numeric n2))
  | Boolean (Less (n1, n2)) ->
      Printf.sprintf "(< %s %s)"
        (prog_to_parseable_str (Numeric n1))
        (prog_to_parseable_str (Numeric n2))
  | Boolean (BNTerm nterm) -> Printf.sprintf "Nonterm %s" nterm.name
  | Stmt (Assign (v, n)) ->
      Printf.sprintf "(:= %s %s)"
        (prog_to_parseable_str (Numeric (Var v)))
        (prog_to_parseable_str (Numeric n))
  | Stmt (Seq (s1, s2)) ->
      Printf.sprintf "(; %s %s)"
        (prog_to_parseable_str (Stmt s1))
        (prog_to_parseable_str (Stmt s2))
  | Stmt (ITE (b, s1, s2)) ->
      Printf.sprintf "(if %s then %s else %s)"
        (prog_to_parseable_str (Boolean b))
        (prog_to_parseable_str (Stmt s1))
        (prog_to_parseable_str (Stmt s2))
  | Stmt (While (b, inv, s)) ->
      Printf.sprintf "(while %s do {|%s|} %s)"
        (prog_to_parseable_str (Boolean b))
        (Logic.Formula.form_tostr inv)
        (prog_to_parseable_str (Stmt s))
  | Stmt (SNTerm nterm) -> Printf.sprintf "Nonterm %s" nterm.name

(* Returns all vars mentioned in the program, including e_t or b_t only if the program is a numeric or bool. *)
let rec get_program_vars_helper prog examined =
  match prog with
  | Numeric (Int _) -> (VS.empty, examined)
  | Numeric (Var v) ->
      (VS.singleton (IntTermVar (match v with "e_t" -> ET | _ -> T v)), examined)
  | Numeric (Plus (n1, n2)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Numeric n1) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Numeric n2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Numeric (ITE (b, n1, n2)) ->
      let guard_set, guard_examined =
        get_program_vars_helper (Boolean b) examined
      in
      let then_set, then_examined =
        get_program_vars_helper (Numeric n1) guard_examined
      in
      let else_set, else_examined =
        get_program_vars_helper (Numeric n2) then_examined
      in
      (VS.union guard_set (VS.union then_set else_set), else_examined)
  | Numeric (NNTerm nterm) ->
      if List.mem prog examined then (VS.empty, examined)
      else
        List.fold_left
          (fun (vars, examined_already) expansion ->
            let found_vars, examined_stuff =
              get_program_vars_helper (Numeric expansion) examined_already
            in
            (VS.union vars found_vars, examined_stuff))
          (VS.empty, List.cons prog examined)
          (NonTerminal.expand nterm)
  | Boolean True -> (VS.empty, examined)
  | Boolean False -> (VS.empty, examined)
  | Boolean (Not b) -> get_program_vars_helper (Boolean b) examined
  | Boolean (And (b1, b2)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Boolean b1) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Boolean b2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Boolean (Or (b1, b2)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Boolean b1) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Boolean b2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Boolean (Equals (n1, n2)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Numeric n1) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Numeric n2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Boolean (Less (n1, n2)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Numeric n1) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Numeric n2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Boolean (BNTerm nterm) ->
      if List.mem prog examined then (VS.empty, examined)
      else
        List.fold_left
          (fun (vars, examined_already) expansion ->
            let found_vars, examined_stuff =
              get_program_vars_helper (Boolean expansion) examined_already
            in
            (VS.union vars found_vars, examined_stuff))
          (VS.empty, List.cons prog examined)
          (NonTerminal.expand nterm)
  | Stmt (Assign (v, n)) ->
      let rhs_set, rhs_examined =
        get_program_vars_helper (Numeric n) examined
      in
      (VS.add (IntTermVar (T v)) rhs_set, rhs_examined)
  | Stmt (Seq (s1, s2)) ->
      let lhs_set, lhs_examined = get_program_vars_helper (Stmt s1) examined in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Stmt s2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Stmt (ITE (b, s1, s2)) ->
      let guard_set, guard_examined =
        get_program_vars_helper (Boolean b) examined
      in
      let then_set, then_examined =
        get_program_vars_helper (Stmt s1) guard_examined
      in
      let else_set, else_examined =
        get_program_vars_helper (Stmt s2) then_examined
      in
      (VS.union guard_set (VS.union then_set else_set), else_examined)
  | Stmt (While (b, _, s)) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Boolean b) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Stmt s) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Stmt (SNTerm nterm) ->
      if List.mem prog examined then (VS.empty, examined)
      else
        List.fold_left
          (fun (vars, examined_already) expansion ->
            let found_vars, examined_stuff =
              get_program_vars_helper (Stmt expansion) examined_already
            in
            (VS.union vars found_vars, examined_stuff))
          (VS.empty, List.cons prog examined)
          (NonTerminal.expand nterm)

let get_program_vars prog =
  match prog with
  | Numeric _ -> VS.add (IntTermVar ET) (fst (get_program_vars_helper prog []))
  | Boolean _ -> VS.add (BoolVar BT) (fst (get_program_vars_helper prog []))
  | Stmt _ -> fst (get_program_vars_helper prog [])

(* Returns vars (as formula vars) whose values may be changed by any program in the set.
   This is good to have for the adapt rule. *)
let rec reassigned_vars_helper prog examined =
  match prog with
  | Numeric _ -> VS.empty
  | Boolean _ -> VS.empty
  | Stmt (Assign (v, _)) -> VS.singleton (IntTermVar (T v))
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
  VS.add (IntTermVar ET)
    (VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty))

(* Returns set of reassigned vars excluding ET and BT, unless the program is a bool or int *)
let reassigned_vars_clean prog =
  match prog with
  | Numeric _ -> VS.add (IntTermVar ET) (reassigned_vars_helper prog SNTS.empty)
  | Boolean _ -> VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty)
  | Stmt _ -> reassigned_vars_helper prog SNTS.empty

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

let rec get_nonterms_helper prog grm =
  match prog with
  | Numeric (Int _) -> grm
  | Numeric (Var _) -> grm
  | Numeric (Plus (n1, n2)) ->
      get_nonterms_helper (Numeric n2) (get_nonterms_helper (Numeric n1) grm)
  | Numeric (ITE (b, n1, n2)) ->
      get_nonterms_helper (Boolean b)
        (get_nonterms_helper (Numeric n1)
           (get_nonterms_helper (Numeric n2) grm))
  | Numeric (NNTerm nterm) ->
      if List.mem nterm grm.grammar_num then grm
      else
        List.fold_left
          (fun gram num -> get_nonterms_helper (Numeric num) gram)
          {
            grammar_num = List.cons nterm grm.grammar_num;
            grammar_bool = grm.grammar_bool;
            grammar_stmt = grm.grammar_stmt;
          }
          (expand nterm)
  | Boolean True -> grm
  | Boolean False -> grm
  | Boolean (Not b) -> get_nonterms_helper (Boolean b) grm
  | Boolean (And (b1, b2)) ->
      get_nonterms_helper (Boolean b1) (get_nonterms_helper (Boolean b2) grm)
  | Boolean (Or (b1, b2)) ->
      get_nonterms_helper (Boolean b1) (get_nonterms_helper (Boolean b2) grm)
  | Boolean (Equals (n1, n2)) ->
      get_nonterms_helper (Numeric n1) (get_nonterms_helper (Numeric n2) grm)
  | Boolean (Less (n1, n2)) ->
      get_nonterms_helper (Numeric n1) (get_nonterms_helper (Numeric n2) grm)
  | Boolean (BNTerm nterm) ->
      if List.mem nterm grm.grammar_bool then grm
      else
        List.fold_left
          (fun gram bol -> get_nonterms_helper (Boolean bol) gram)
          {
            grammar_num = grm.grammar_num;
            grammar_bool = List.cons nterm grm.grammar_bool;
            grammar_stmt = grm.grammar_stmt;
          }
          (expand nterm)
  | Stmt (Assign (_, n)) -> get_nonterms_helper (Numeric n) grm
  | Stmt (Seq (s1, s2)) ->
      get_nonterms_helper (Stmt s1) (get_nonterms_helper (Stmt s2) grm)
  | Stmt (ITE (b, s1, s2)) ->
      get_nonterms_helper (Boolean b)
        (get_nonterms_helper (Stmt s1) (get_nonterms_helper (Stmt s2) grm))
  | Stmt (While (b, _, s)) ->
      get_nonterms_helper (Boolean b) (get_nonterms_helper (Stmt s) grm)
  | Stmt (SNTerm nterm) ->
      if List.mem nterm grm.grammar_stmt then grm
      else
        List.fold_left
          (fun gram stmt -> get_nonterms_helper (Stmt stmt) gram)
          {
            grammar_num = grm.grammar_num;
            grammar_bool = grm.grammar_bool;
            grammar_stmt = List.cons nterm grm.grammar_stmt;
          }
          (expand nterm)

let get_nonterms prog =
  get_nonterms_helper prog
    { grammar_num = []; grammar_bool = []; grammar_stmt = [] }

(* Given a grammar, converts it to a pareseable string *)
let grammar_to_parseable_str gram =
  let ns =
    List.map
      (nonterminal_to_parseable_str_def "Int" (fun num ->
           prog_to_parseable_str (Numeric num)))
      gram.grammar_num
  and bs =
    List.map
      (nonterminal_to_parseable_str_def "Bool" (fun bol ->
           prog_to_parseable_str (Boolean bol)))
      gram.grammar_bool
  and ss =
    List.map
      (nonterminal_to_parseable_str_def "Stmt" (fun stmt ->
           prog_to_parseable_str (Stmt stmt)))
      gram.grammar_stmt
  in
  let alls = List.append ns (List.append bs ss) in
  Printf.sprintf "[%s]" (String.concat "; " alls)
