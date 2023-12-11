open NonTerminal
open Logic.Variable

exception Unimplemented

(* TODO: Expand support for program constants *)
type bitv_unop = Minus
type bitv_binop = Plus | Mult | Sub | Or | And | Xor

type bitv_exp =
  | Bitv of string
  | BitvVar of string
  | BitvUnApp of bitv_unop * bitv_exp
  | BinApp of bitv_binop * bitv_exp * bitv_exp
  | BitvITE of boolean_exp * bitv_exp * bitv_exp
  | BitvNTerm of bitv_exp nonterminal

and numeric_exp =
  | Int of int
  | Var of string
  | Plus of numeric_exp * numeric_exp
  | Minus of numeric_exp
  | ITE of boolean_exp * numeric_exp * numeric_exp
  | NNTerm of numeric_exp nonterminal

and term_exp = Numeric of numeric_exp | Bitvec of bitv_exp

and boolean_exp =
  | True
  | False
  | Not of boolean_exp
  | And of boolean_exp * boolean_exp
  | Or of boolean_exp * boolean_exp
  | Equals of term_exp * term_exp
  | Less of term_exp * term_exp
  | BNTerm of boolean_exp nonterminal

type stmt =
  | Skip
  | Assign of string * term_exp
  | Seq of stmt * stmt
  | ITE of boolean_exp * stmt * stmt
  | While of boolean_exp * Logic.Formula.formula * stmt
  | SNTerm of stmt nonterminal

module SNTS = Set.Make (struct
  type t = stmt nonterminal

  let compare = compare
end)

type program = Term of term_exp | Boolean of boolean_exp | Stmt of stmt

let rec numeric_to_str num_exp =
  match num_exp with
  | Int i -> Printf.sprintf "%d" i
  | Var x -> x
  | Plus (n1, n2) ->
      Printf.sprintf "(%s + %s)" (numeric_to_str n1) (numeric_to_str n2)
  | Minus n -> Printf.sprintf "(- %s)" (numeric_to_str n)
  | ITE (b, n1, n2) ->
      Printf.sprintf "(if %s then %s else %s)" (prog_tostr (Boolean b))
        (numeric_to_str n1) (numeric_to_str n2)
  | NNTerm nterm -> to_str nterm

and bitvec_to_str bitv_exp =
  match bitv_exp with
  | Bitv s -> s
  | BitvVar v -> v
  | BitvUnApp (Minus, btv) -> Printf.sprintf "(- %s)" (bitvec_to_str btv)
  | BinApp (op, btv1, btv2) -> (
      match op with
      | Plus ->
          Printf.sprintf "(%s + %s)" (bitvec_to_str btv1) (bitvec_to_str btv2)
      | Mult ->
          Printf.sprintf "(%s * %s)" (bitvec_to_str btv1) (bitvec_to_str btv2)
      | Sub ->
          Printf.sprintf "(%s - %s)" (bitvec_to_str btv1) (bitvec_to_str btv2)
      | Or ->
          Printf.sprintf "(%s | %s)" (bitvec_to_str btv1) (bitvec_to_str btv2)
      | Xor ->
          Printf.sprintf "(%s ^ %s)" (bitvec_to_str btv1) (bitvec_to_str btv2)
      | And ->
          Printf.sprintf "(%s & %s)" (bitvec_to_str btv1) (bitvec_to_str btv2))
  | BitvITE (guard, btv1, btv2) ->
      Printf.sprintf "(if %s then %s else %s)"
        (prog_tostr (Boolean guard))
        (bitvec_to_str btv1) (bitvec_to_str btv2)
  | BitvNTerm nterm -> to_str nterm

and term_to_str t =
  match t with Numeric n -> numeric_to_str n | Bitvec btv -> bitvec_to_str btv

and prog_tostr prog =
  match prog with
  | Term (Numeric n) -> numeric_to_str n
  | Term (Bitvec btv) -> bitvec_to_str btv
  | Boolean True -> "T"
  | Boolean False -> "F"
  | Boolean (Not b) -> Printf.sprintf "!%s" (prog_tostr (Boolean b))
  | Boolean (And (b1, b2)) ->
      Printf.sprintf "(%s && %s)" (prog_tostr (Boolean b1))
        (prog_tostr (Boolean b2))
  | Boolean (Or (b1, b2)) ->
      Printf.sprintf "(%s || %s)" (prog_tostr (Boolean b1))
        (prog_tostr (Boolean b2))
  | Boolean (Equals (t1, t2)) ->
      Printf.sprintf "(%s = %s)" (term_to_str t1) (term_to_str t2)
  | Boolean (Less (t1, t2)) ->
      Printf.sprintf "(%s < %s)" (term_to_str t1) (term_to_str t2)
  | Boolean (BNTerm nterm) -> to_str nterm
  | Stmt Skip -> "skip"
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n ->
          Printf.sprintf "(%s := %s)" (numeric_to_str (Var v))
            (numeric_to_str n)
      | Bitvec btv ->
          Printf.sprintf "(%s := %s)"
            (bitvec_to_str (BitvVar v))
            (bitvec_to_str btv))
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
  | Term (Numeric (Int i)) -> Printf.sprintf "%d" i
  | Term (Numeric (Var v)) -> v
  | Term (Numeric (Plus (n1, n2))) ->
      Printf.sprintf "(+ %s %s)"
        (prog_to_parseable_str (Term (Numeric n1)))
        (prog_to_parseable_str (Term (Numeric n2)))
  | Term (Numeric (Minus n)) ->
      Printf.sprintf "(- %s)" (prog_to_parseable_str (Term (Numeric n)))
  | Term (Numeric (ITE (b, n1, n2))) ->
      Printf.sprintf "(if %s then %s else %s)"
        (prog_to_parseable_str (Boolean b))
        (prog_to_parseable_str (Term (Numeric n1)))
        (prog_to_parseable_str (Term (Numeric n2)))
  | Term (Numeric (NNTerm nterm)) -> Printf.sprintf "Nonterm %s" nterm.name
  | Term (Bitvec _) -> raise Unimplemented
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
  | Boolean (Equals (Numeric n1, Numeric n2)) ->
      Printf.sprintf "(= %s %s)"
        (prog_to_parseable_str (Term (Numeric n1)))
        (prog_to_parseable_str (Term (Numeric n2)))
  | Boolean (Equals (Bitvec btv1, Bitvec btv2)) ->
      Printf.sprintf "(= %s %s)"
        (prog_to_parseable_str (Term (Bitvec btv1)))
        (prog_to_parseable_str (Term (Bitvec btv2)))
  | Boolean (Equals (_, _)) -> raise Unimplemented
  | Boolean (Less (Numeric n1, Numeric n2)) ->
      Printf.sprintf "(< %s %s)"
        (prog_to_parseable_str (Term (Numeric n1)))
        (prog_to_parseable_str (Term (Numeric n2)))
  | Boolean (Less (Bitvec btv1, Bitvec btv2)) ->
      Printf.sprintf "(< %s %s)"
        (prog_to_parseable_str (Term (Bitvec btv1)))
        (prog_to_parseable_str (Term (Bitvec btv2)))
  | Boolean (Less (_, _)) -> raise Unimplemented
  | Boolean (BNTerm nterm) -> Printf.sprintf "Nonterm %s" nterm.name
  | Stmt Skip -> "skip"
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n ->
          Printf.sprintf "(:= %s %s)"
            (prog_to_parseable_str (Term (Numeric (Var v))))
            (prog_to_parseable_str (Term (Numeric n)))
      | Bitvec btv ->
          Printf.sprintf "(:= %s %s)"
            (prog_to_parseable_str (Term (Bitvec (BitvVar v))))
            (prog_to_parseable_str (Term (Bitvec btv))))
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
  | Term (Numeric (Int _)) -> (VS.empty, examined)
  | Term (Numeric (Var v)) ->
      ( VS.singleton (IntTermVar (match v with "e_t" -> ET | _ -> T v)),
        examined )
  | Term (Numeric (Plus (n1, n2))) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Term (Numeric n1)) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Term (Numeric n2)) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Term (Numeric (Minus n)) ->
      get_program_vars_helper (Term (Numeric n)) examined
  | Term (Numeric (ITE (b, n1, n2))) ->
      let guard_set, guard_examined =
        get_program_vars_helper (Boolean b) examined
      in
      let then_set, then_examined =
        get_program_vars_helper (Term (Numeric n1)) guard_examined
      in
      let else_set, else_examined =
        get_program_vars_helper (Term (Numeric n2)) then_examined
      in
      (VS.union guard_set (VS.union then_set else_set), else_examined)
  | Term (Numeric (NNTerm nterm)) ->
      if List.mem prog examined then (VS.empty, examined)
      else
        List.fold_left
          (fun (vars, examined_already) expansion ->
            let found_vars, examined_stuff =
              get_program_vars_helper (Term (Numeric expansion))
                examined_already
            in
            (VS.union vars found_vars, examined_stuff))
          (VS.empty, List.cons prog examined)
          (NonTerminal.expand nterm)
  | Term (Bitvec (Bitv _)) -> (VS.empty, examined)
  | Term (Bitvec (BitvVar v)) ->
      ( VS.singleton (BitvTermVar (match v with "e_t" -> ET | _ -> T v)),
        examined )
  | Term (Bitvec (BitvUnApp (_, btv))) ->
      get_program_vars_helper (Term (Bitvec btv)) examined
  | Term (Bitvec (BinApp (_, btv1, btv2))) ->
      let lhs_set, lhs_examined =
        get_program_vars_helper (Term (Bitvec btv1)) examined
      in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Term (Bitvec btv2)) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Term (Bitvec (BitvITE (b, btv1, btv2))) ->
      let guard_set, guard_examined =
        get_program_vars_helper (Boolean b) examined
      in
      let then_set, then_examined =
        get_program_vars_helper (Term (Bitvec btv1)) guard_examined
      in
      let else_set, else_examined =
        get_program_vars_helper (Term (Bitvec btv2)) then_examined
      in
      (VS.union guard_set (VS.union then_set else_set), else_examined)
  | Term (Bitvec (BitvNTerm nterm)) ->
      if List.mem prog examined then (VS.empty, examined)
      else
        List.fold_left
          (fun (vars, examined_already) expansion ->
            let found_vars, examined_stuff =
              get_program_vars_helper (Term (Bitvec expansion)) examined_already
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
      let lhs_set, lhs_examined = get_program_vars_helper (Term n1) examined in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Term n2) lhs_examined
      in
      (VS.union lhs_set rhs_set, rhs_examined)
  | Boolean (Less (n1, n2)) ->
      let lhs_set, lhs_examined = get_program_vars_helper (Term n1) examined in
      let rhs_set, rhs_examined =
        get_program_vars_helper (Term n2) lhs_examined
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
  | Stmt Skip -> (VS.empty, examined)
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n ->
          let rhs_set, rhs_examined =
            get_program_vars_helper (Term (Numeric n)) examined
          in
          (VS.add (IntTermVar (T v)) rhs_set, rhs_examined)
      | Bitvec btv ->
          let rhs_set, rhs_examined =
            get_program_vars_helper (Term (Bitvec btv)) examined
          in
          (VS.add (BitvTermVar (T v)) rhs_set, rhs_examined))
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
  | Term (Numeric _) ->
      VS.add (IntTermVar ET) (fst (get_program_vars_helper prog []))
  | Term (Bitvec _) ->
      VS.add (BitvTermVar ET) (fst (get_program_vars_helper prog []))
  | Boolean _ -> VS.add (BoolVar BT) (fst (get_program_vars_helper prog []))
  | Stmt _ -> fst (get_program_vars_helper prog [])

(* Returns vars (as formula vars) whose values may be changed by any program in the set.
   This is good to have for the adapt rule. *)
let rec reassigned_vars_helper prog examined =
  match prog with
  | Term (Numeric _) -> VS.empty
  | Term (Bitvec _) -> VS.empty
  | Boolean _ -> VS.empty
  | Stmt Skip -> VS.empty
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric _ -> VS.singleton (IntTermVar (T v))
      | Bitvec _ -> VS.singleton (BitvTermVar (T v)))
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
  (* If something broke, it happened here. *)
  match prog with
  | Term (Numeric _) ->
      VS.add (IntTermVar ET) (reassigned_vars_helper prog SNTS.empty)
  | Term (Bitvec _) ->
      VS.add (BitvTermVar ET) (reassigned_vars_helper prog SNTS.empty)
  | Boolean _ -> VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty)
  | Stmt _ -> reassigned_vars_helper prog SNTS.empty

(* Returns set of reassigned vars excluding ET and BT, unless the program is a bool or int *)
let reassigned_vars_clean prog =
  match prog with
  | Term (Numeric _) ->
      VS.add (IntTermVar ET) (reassigned_vars_helper prog SNTS.empty)
  | Term (Bitvec _) ->
      VS.add (BitvTermVar ET) (reassigned_vars_helper prog SNTS.empty)
  | Boolean _ -> VS.add (BoolVar BT) (reassigned_vars_helper prog SNTS.empty)
  | Stmt _ -> reassigned_vars_helper prog SNTS.empty

(* Substitution of nonterminals according to given grammar. Useful when recursively defining grammars. *)
type grammar = {
  grammar_num : numeric_exp nonterminal list;
  grammar_bitv : bitv_exp nonterminal list;
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
  | Minus n -> Minus (subs_nonterms_numeric lazy_grammar n)
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

and subs_nonterms_bitvec lazy_grammar bitv =
  let grammar = Lazy.force lazy_grammar in
  match bitv with
  | BitvUnApp (op, btv) -> BitvUnApp (op, subs_nonterms_bitvec lazy_grammar btv)
  | BinApp (op, btv1, btv2) ->
      BinApp
        ( op,
          subs_nonterms_bitvec lazy_grammar btv1,
          subs_nonterms_bitvec lazy_grammar btv2 )
  | BitvITE (b, btv1, btv2) ->
      BitvITE
        ( subs_nonterms_boolean lazy_grammar b,
          subs_nonterms_bitvec lazy_grammar btv1,
          subs_nonterms_bitvec lazy_grammar btv2 )
  | BitvNTerm nt ->
      if List.exists (fun n -> n.name = nt.name) grammar.grammar_bitv then
        BitvNTerm (List.find (fun n -> n.name = nt.name) grammar.grammar_bitv)
      else bitv
  | _ -> bitv

and subs_nonterms_term lazy_grammar term =
  match term with
  | Numeric n -> Numeric (subs_nonterms_numeric lazy_grammar n)
  | Bitvec btv -> Bitvec (subs_nonterms_bitvec lazy_grammar btv)

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
        (subs_nonterms_term lazy_grammar n1, subs_nonterms_term lazy_grammar n2)
  | Less (n1, n2) ->
      Less
        (subs_nonterms_term lazy_grammar n1, subs_nonterms_term lazy_grammar n2)
  | BNTerm nt ->
      if List.exists (fun b -> b.name = nt.name) grammar.grammar_bool then
        BNTerm (List.find (fun b -> b.name = nt.name) grammar.grammar_bool)
      else boolean
  | _ -> boolean

and subs_nonterms_stmt lazy_grammar stmt =
  let grammar = Lazy.force lazy_grammar in
  match stmt with
  | Skip -> Skip
  | Assign (s, t) -> (
      match t with
      | Numeric n -> Assign (s, Numeric (subs_nonterms_numeric lazy_grammar n))
      | Bitvec btv -> Assign (s, Bitvec (subs_nonterms_bitvec lazy_grammar btv))
      )
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
  | Term (Numeric n) -> Term (Numeric (subs_nonterms_numeric lazy_grammar n))
  | Term (Bitvec btv) -> Term (Bitvec (subs_nonterms_bitvec lazy_grammar btv))
  | Boolean b -> Boolean (subs_nonterms_boolean lazy_grammar b)
  | Stmt s -> Stmt (subs_nonterms_stmt lazy_grammar s)

let rec get_nonterms_helper prog grm =
  match prog with
  | Term (Numeric (Int _)) -> grm
  | Term (Numeric (Var _)) -> grm
  | Term (Numeric (Plus (n1, n2))) ->
      get_nonterms_helper (Term (Numeric n2))
        (get_nonterms_helper (Term (Numeric n1)) grm)
  | Term (Numeric (Minus n)) -> get_nonterms_helper (Term (Numeric n)) grm
  | Term (Numeric (ITE (b, n1, n2))) ->
      get_nonterms_helper (Boolean b)
        (get_nonterms_helper (Term (Numeric n1))
           (get_nonterms_helper (Term (Numeric n2)) grm))
  | Term (Numeric (NNTerm nterm)) ->
      if List.mem nterm grm.grammar_num then grm
      else
        List.fold_left
          (fun gram num -> get_nonterms_helper (Term (Numeric num)) gram)
          {
            grammar_num = List.cons nterm grm.grammar_num;
            grammar_bitv = grm.grammar_bitv;
            grammar_bool = grm.grammar_bool;
            grammar_stmt = grm.grammar_stmt;
          }
          (expand nterm)
  | Term (Bitvec (Bitv _)) -> grm
  | Term (Bitvec (BitvVar _)) -> grm
  | Term (Bitvec (BitvUnApp (_, btv))) ->
      get_nonterms_helper (Term (Bitvec btv)) grm
  | Term (Bitvec (BinApp (_, btv1, btv2))) ->
      get_nonterms_helper (Term (Bitvec btv2))
        (get_nonterms_helper (Term (Bitvec btv1)) grm)
  | Term (Bitvec (BitvITE (b, btv1, btv2))) ->
      get_nonterms_helper (Boolean b)
        (get_nonterms_helper (Term (Bitvec btv1))
           (get_nonterms_helper (Term (Bitvec btv2)) grm))
  | Term (Bitvec (BitvNTerm nterm)) ->
      if List.mem nterm grm.grammar_bitv then grm
      else
        List.fold_left
          (fun gram btv -> get_nonterms_helper (Term (Bitvec btv)) gram)
          {
            grammar_num = grm.grammar_num;
            grammar_bitv = List.cons nterm grm.grammar_bitv;
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
  | Boolean (Equals (t1, t2)) ->
      get_nonterms_helper (Term t1) (get_nonterms_helper (Term t2) grm)
  | Boolean (Less (t1, t2)) ->
      get_nonterms_helper (Term t1) (get_nonterms_helper (Term t2) grm)
  | Boolean (BNTerm nterm) ->
      if List.mem nterm grm.grammar_bool then grm
      else
        List.fold_left
          (fun gram bol -> get_nonterms_helper (Boolean bol) gram)
          {
            grammar_num = grm.grammar_num;
            grammar_bitv = grm.grammar_bitv;
            grammar_bool = List.cons nterm grm.grammar_bool;
            grammar_stmt = grm.grammar_stmt;
          }
          (expand nterm)
  | Stmt Skip -> grm
  | Stmt (Assign (_, t)) -> (
      match t with
      | Numeric n -> get_nonterms_helper (Term (Numeric n)) grm
      | Bitvec btv -> get_nonterms_helper (Term (Bitvec btv)) grm)
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
            grammar_bitv = grm.grammar_bitv;
            grammar_bool = grm.grammar_bool;
            grammar_stmt = List.cons nterm grm.grammar_stmt;
          }
          (expand nterm)

let get_nonterms prog =
  get_nonterms_helper prog
    {
      grammar_num = [];
      grammar_bitv = [];
      grammar_bool = [];
      grammar_stmt = [];
    }

(* Given a grammar, converts it to a pareseable string *)
let grammar_to_parseable_str gram =
  let ns =
    List.map
      (nonterminal_to_parseable_str_def "Int" (fun num ->
           prog_to_parseable_str (Term (Numeric num))))
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

(* Finite vector-state transformations on program hole values. *)
(* Repeated code because OCaml didn't allow polymorphism here... why? *)
let rec transform_int_nterm (nterm : 'program nonterminal)
    (length : int) (* (transformer : 'program -> int -> 'program) *) =
  {
    name = nterm.name;
    expansions =
      lazy
        (List.map
           (fun x -> int_term_finite_vs_transformer x length)
           (Lazy.force nterm.expansions));
    (* When a non-terminal is not recursive, strongest should be None. *)
    strongest =
      lazy
        (match Lazy.force nterm.strongest with
        | None -> None
        | Some (var_pairs_list, form) ->
            Some
              ( var_pairs_list,
                Logic.Formula.bool_finite_vs_transformer length form ));
  }

and transform_bitv_nterm (nterm : bitv_exp nonterminal)
    (length : int) (* (transformer : bitv_exp -> int -> bitv_exp) *) =
  {
    name = nterm.name;
    expansions =
      lazy
        (List.map
           (fun x -> bitv_term_finite_vs_transformer x length)
           (Lazy.force nterm.expansions));
    (* When a non-terminal is not recursive, strongest should be None. *)
    strongest =
      lazy
        (match Lazy.force nterm.strongest with
        | None -> None
        | Some (var_pairs_list, form) ->
            Some
              ( var_pairs_list,
                Logic.Formula.bool_finite_vs_transformer length form ));
  }

and transform_bool_nterm (nterm : boolean_exp nonterminal)
    (length : int) (* (transformer : boolean_exp -> int -> boolean_exp) *) =
  {
    name = nterm.name;
    expansions =
      lazy
        (List.map
           (fun x -> bool_prog_finite_vs_transformer x length)
           (Lazy.force nterm.expansions));
    (* When a non-terminal is not recursive, strongest should be None. *)
    strongest =
      lazy
        (match Lazy.force nterm.strongest with
        | None -> None
        | Some (var_pairs_list, form) ->
            Some
              ( var_pairs_list,
                Logic.Formula.bool_finite_vs_transformer length form ));
  }

and transform_stmt_nterm (nterm : stmt nonterminal)
    (length : int) (* (transformer : stmt -> int -> stmt) *) =
  {
    name = nterm.name;
    expansions =
      lazy
        (List.map
           (fun x -> stmt_finite_vs_transformer x length)
           (Lazy.force nterm.expansions));
    (* When a non-terminal is not recursive, strongest should be None. *)
    strongest =
      lazy
        (match Lazy.force nterm.strongest with
        | None -> None
        | Some (var_pairs_list, form) ->
            Some
              ( var_pairs_list,
                Logic.Formula.bool_finite_vs_transformer length form ));
  }

and int_term_finite_vs_transformer iterm length =
  match iterm with
  | Plus (t1, t2) ->
      Plus
        ( int_term_finite_vs_transformer t1 length,
          int_term_finite_vs_transformer t2 length )
  | Minus t -> Minus (int_term_finite_vs_transformer t length)
  | ITE (b, t1, t2) ->
      ITE
        ( bool_prog_finite_vs_transformer b length,
          int_term_finite_vs_transformer t1 length,
          int_term_finite_vs_transformer t2 length )
  | NNTerm n -> NNTerm (transform_int_nterm n length)
  | _ -> iterm

and bitv_term_finite_vs_transformer bitvterm length =
  match bitvterm with
  | BitvUnApp (op, btv) ->
      BitvUnApp (op, bitv_term_finite_vs_transformer btv length)
  | BinApp (op, btv1, btv2) ->
      BinApp
        ( op,
          bitv_term_finite_vs_transformer btv1 length,
          bitv_term_finite_vs_transformer btv2 length )
  | BitvITE (b, btv1, btv2) ->
      BitvITE
        ( bool_prog_finite_vs_transformer b length,
          bitv_term_finite_vs_transformer btv1 length,
          bitv_term_finite_vs_transformer btv2 length )
  | BitvNTerm n -> BitvNTerm (transform_bitv_nterm n length)
  | _ -> bitvterm

and term_finite_vs_transformer term length =
  match term with
  | Numeric it -> Numeric (int_term_finite_vs_transformer it length)
  | Bitvec btv -> Bitvec (bitv_term_finite_vs_transformer btv length)

and bool_prog_finite_vs_transformer form length =
  match form with
  | Not f -> Not (bool_prog_finite_vs_transformer f length)
  | And (f1, f2) ->
      And
        ( bool_prog_finite_vs_transformer f1 length,
          bool_prog_finite_vs_transformer f2 length )
  | Or (f1, f2) ->
      Or
        ( bool_prog_finite_vs_transformer f1 length,
          bool_prog_finite_vs_transformer f2 length )
  | Equals (t1, t2) ->
      Equals
        ( term_finite_vs_transformer t1 length,
          term_finite_vs_transformer t2 length )
  | Less (t1, t2) ->
      Less
        ( term_finite_vs_transformer t1 length,
          term_finite_vs_transformer t2 length )
  | BNTerm n -> BNTerm (transform_bool_nterm n length)
  | _ -> form

and stmt_finite_vs_transformer stmt length =
  match stmt with
  | Skip -> Skip
  | Assign (v, t) -> (
      match t with
      | Numeric it ->
          Assign (v, Numeric (int_term_finite_vs_transformer it length))
      | Bitvec bitvt ->
          Assign (v, Bitvec (bitv_term_finite_vs_transformer bitvt length)))
  | Seq (s1, s2) ->
      Seq
        ( stmt_finite_vs_transformer s1 length,
          stmt_finite_vs_transformer s2 length )
  | ITE (b, s1, s2) ->
      ITE
        ( bool_prog_finite_vs_transformer b length,
          stmt_finite_vs_transformer s1 length,
          stmt_finite_vs_transformer s2 length )
  | While (b, inv, s) ->
      While
        ( bool_prog_finite_vs_transformer b length,
          Logic.Formula.bool_finite_vs_transformer length inv,
          stmt_finite_vs_transformer s length )
  | SNTerm n -> SNTerm (transform_stmt_nterm n length)

and prog_finite_vs_transformer prog length =
  if length < 1 then prog
  else
    match prog with
    | Term t -> Term (term_finite_vs_transformer t length)
    | Boolean b -> Boolean (bool_prog_finite_vs_transformer b length)
    | Stmt s -> Stmt (stmt_finite_vs_transformer s length)
