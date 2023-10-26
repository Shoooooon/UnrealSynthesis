%{  open Logic
    open Logic.Formula
    open Logic.Variable
    open Programs.Program
    exception Parse_Bad_Formula
    let make_exists body quant = Formula.Exists (quant, body)
    let make_forall body quant = Formula.Forall (quant, body)
%}

%token <int> INT
%token <string> STRING
%token INT_KWD
%token ARRAY_INT_KWD
%token BOOL_KWD
%token ARRAY_BOOL_KWD
%token STMT_KWD
%token NT_KWD
%token NONE_KWD
%token SOME_KWD
%token HOLE_KWD
%token ET
%token BT
%token NOT
%token AND
%token OR
%token TRUE
%token FALSE
%token PLUS
%token TIMES
%token MINUS
%token EQUALS
%token IFF
%token IMPLIES
%token LESS
%token LESS_EQUALS
%token GREATER
%token GREATER_EQUALS
%token ASSIGN
%token SEMICOLON
%token COLON
%token COMMA
%token IF
%token THEN
%token ELSE
%token WHILE
%token EXISTS
%token FORALL
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_SQUARE
%token RIGHT_SQUARE
%token LEFT_FORM_DEMARCATOR
%token RIGHT_FORM_DEMARCATOR
%start <Proofrules.ProofRule.triple> ultriple
%%

// Parse UL triples.
ultriple:
    nt_list=grammar LEFT_FORM_DEMARCATOR pren=formula RIGHT_FORM_DEMARCATOR progn=program LEFT_FORM_DEMARCATOR postn=formula RIGHT_FORM_DEMARCATOR {
      (*This will hang. We may need to make nonterminal expansions lazy. *)
      let rec grammar = lazy {
          grammar_num = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Numeric (NNTerm n) -> Some {Programs.NonTerminal.name=n.name; expansions=lazy (List.map (subs_nonterms_numeric grammar) (Lazy.force n.expansions)); strongest=n.strongest}
        | _ -> None)) (nt_list grammar));
        grammar_bool = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Boolean (BNTerm b) -> Some {Programs.NonTerminal.name=b.name; expansions=lazy (List.map (subs_nonterms_boolean grammar) (Lazy.force b.expansions)); strongest=b.strongest}
        | _ -> None)) (nt_list grammar));
        grammar_stmt = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Stmt (SNTerm s) -> Some {Programs.NonTerminal.name=s.name; expansions=lazy (List.map (subs_nonterms_stmt grammar) (Lazy.force s.expansions)); strongest=s.strongest}
        | _ -> None)) (nt_list grammar))
      } in 
      {Proofrules.ProofRule.pre = pren; prog = (progn grammar); post = postn}      
      }

// Utilities for parsing formulas -- Roughly matches smt2 format except = is only for ints, and <-> is boolean equality
form_args_list:
  |LEFT_PAREN RIGHT_PAREN {[]}
  |LEFT_PAREN args=form_args RIGHT_PAREN {args}

form_args:
  |a=form_arg {[a]}
  |arg=form_arg args=form_args {List.cons arg args}

form_arg: 
  | LEFT_PAREN BT INT_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN ET ARRAY_INT_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN BT BOOL_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN BT ARRAY_BOOL_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN {Variable.TermVar (T s)}
  | LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN {Variable.BoolVar (B s)}
  | LEFT_PAREN s=STRING ARRAY_INT_KWD RIGHT_PAREN {Variable.ATermVar (T s)}
  | LEFT_PAREN s=STRING ARRAY_BOOL_KWD RIGHT_PAREN {Variable.ABoolVar (B s)}

form_term:
  | i = INT {Int i}
  | ET {TVar ET}
  | ET LEFT_SQUARE index=form_term RIGHT_SQUARE {ATVar (TApp (ET, index))}
  | s = STRING {TVar (T s)}
  | s = STRING LEFT_SQUARE index=form_term RIGHT_SQUARE {ATVar (TApp (T s, index))}
  | LEFT_PAREN MINUS t=form_term RIGHT_PAREN {Formula.Minus t}
  | LEFT_PAREN PLUS t1=form_term t2=form_term RIGHT_PAREN {Formula.Plus (t1, t2)}
  | LEFT_PAREN TIMES t1=form_term t2=form_term RIGHT_PAREN {Formula.Times (t1, t2)}

formula:
  | TRUE {True}
  | FALSE {False}
  | BT {BVar BT}
  | BT LEFT_SQUARE index=form_term RIGHT_SQUARE {ABVar (BApp (BT, index))}
  | s = STRING {BVar (B s)}
  | s = STRING LEFT_SQUARE index=form_term RIGHT_SQUARE {ABVar (BApp (B s, index))}
  | LEFT_PAREN AND f1=formula f2=formula RIGHT_PAREN {And (f1, f2)}
  | LEFT_PAREN OR f1=formula f2=formula RIGHT_PAREN {Or (f1, f2)}
  | LEFT_PAREN NOT f=formula RIGHT_PAREN {Not f}
  | LEFT_PAREN IMPLIES f1=formula f2=formula RIGHT_PAREN {Implies (f1, f2)}
  | LEFT_PAREN EQUALS t1=form_term t2=form_term RIGHT_PAREN {Equals (t1, t2)}
  | LEFT_PAREN IFF b1=formula b2=formula RIGHT_PAREN {Iff (b1, b2)}
  | LEFT_PAREN LESS t1=form_term t2=form_term RIGHT_PAREN {Less (t1, t2)}
  | LEFT_PAREN LESS_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Or (Less (t1, t2), Equals (t1, t2))}
  | LEFT_PAREN GREATER t1=form_term t2=form_term RIGHT_PAREN {Less (t2, t1)}
  | LEFT_PAREN GREATER_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Or (Less (t2, t1), Equals (t2, t1))}
  | EXISTS quants=form_args_list body=formula {(List.fold_left make_exists body quants)} 
  | FORALL quants=form_args_list body=formula {(List.fold_left make_forall body quants)} 

// Utilities for program parsing 
// Note, all returns will be functions that take in a lazy grammar. This prevents different parses from interfering with one another. 
prog_num: 
  | i = INT {fun _ -> Int i}
  | LEFT_PAREN PLUS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Plus ((n1 gram), (n2 gram))}
  | LEFT_PAREN IF b=prog_bool THEN n1=prog_num ELSE n2=prog_num RIGHT_PAREN {fun gram -> ITE ((b gram), (n1 gram), (n2 gram))}
  | NT_KWD s = STRING {fun gram -> (if (List.exists (fun n -> (Programs.NonTerminal.name n)= s) (Lazy.force gram).grammar_num)
    then (NNTerm (List.find (fun n -> (Programs.NonTerminal.name n) = s) (Lazy.force gram).grammar_num)) 
    else (NNTerm ({name=s; expansions=lazy []; strongest=lazy None})))
    }
  | s = STRING {fun _ -> Var s}

prog_bool:
 | TRUE {fun _ ->True}
 | FALSE {fun _ -> False}
 | LEFT_PAREN NOT b=prog_bool RIGHT_PAREN {fun gram -> Not (b gram)}
 | LEFT_PAREN OR b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> Or ((b1 gram), (b2 gram))}
 | LEFT_PAREN AND b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> And ((b1 gram), (b2 gram))}
 | LEFT_PAREN EQUALS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Equals ((n1 gram), (n2 gram))}
 | LEFT_PAREN LESS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Less ((n1 gram), (n2 gram))}
 | NT_KWD s = STRING {fun gram -> (if (List.exists (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    then BNTerm (List.find (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    else BNTerm ({name=s; expansions=lazy []; strongest=lazy None}))
    }

prog_stmt:
  | LEFT_PAREN ASSIGN s=STRING t=prog_num RIGHT_PAREN {fun gram -> Assign (s, (t gram))}
  | LEFT_PAREN SEMICOLON s1=prog_stmt s2=prog_stmt RIGHT_PAREN {fun gram -> Seq ((s1 gram), (s2 gram))}
  | LEFT_PAREN IF b=prog_bool THEN s1=prog_stmt ELSE s2=prog_stmt RIGHT_PAREN {fun gram -> ITE ((b gram), (s1 gram), (s2 gram))}
  | LEFT_PAREN WHILE b=prog_bool LEFT_FORM_DEMARCATOR f=formula RIGHT_FORM_DEMARCATOR s=prog_stmt RIGHT_PAREN {fun gram -> While ((b gram), f, (s gram))}
  | NT_KWD s = STRING {fun gram -> (if (List.exists (fun st -> (Programs.NonTerminal.name st) = s) (Lazy.force gram).grammar_stmt)
    then SNTerm (List.find (fun st -> (Programs.NonTerminal.name st) = s) (Lazy.force gram).grammar_stmt)
    else SNTerm ({name=s; expansions=lazy []; strongest=lazy None}))
    }

program:
    | INT_KWD n=prog_num {fun gram -> Numeric (n gram)}
    | BOOL_KWD b=prog_bool {fun gram -> Boolean (b gram)}
    | STMT_KWD p=prog_stmt {fun gram -> Stmt (p gram)}

// Parse Grammar
grammar: 
  | LEFT_SQUARE RIGHT_SQUARE {fun _ -> []}
  | LEFT_SQUARE nt_list=nonterminal_defs RIGHT_SQUARE {fun gram -> (nt_list gram)}

nonterminal_defs:
  | n=nonterminal_def {fun gram -> [(n gram)]}
  | n=nonterminal_def SEMICOLON n_list=nonterminal_defs {fun gram -> List.cons (n gram) (n_list gram)}

nonterminal_def:
  | INT_KWD name=STRING COLON expansions=prog_num_list COLON str=strongest {fun gram -> Numeric (NNTerm { name = name; expansions = lazy (expansions gram); strongest = lazy str;})}
  | BOOL_KWD name=STRING COLON expansions=prog_bool_list COLON str=strongest {fun gram -> Boolean (BNTerm { name = name; expansions = lazy (expansions gram); strongest = lazy str;})}
  | STMT_KWD name=STRING COLON expansions=prog_stmt_list COLON str=strongest {fun gram -> Stmt (SNTerm { name = name; expansions = lazy (expansions gram); strongest = lazy str;})}

prog_bool_list:
  | LEFT_SQUARE RIGHT_SQUARE {fun _ -> []}
  | LEFT_SQUARE b_list=prog_bools RIGHT_SQUARE {fun gram -> (b_list gram)}

prog_bools:
  | b=prog_bool {fun gram -> [(b gram)]}
  | b=prog_bool COMMA b_list=prog_bools {fun gram -> List.cons (b gram) (b_list gram)}
  
prog_num_list:
  | LEFT_SQUARE RIGHT_SQUARE {fun _ -> []}
  | LEFT_SQUARE n_list=prog_nums RIGHT_SQUARE {fun gram -> (n_list gram)}

prog_nums:
  | n=prog_num {fun gram -> [(n gram)]}
  | n=prog_num COMMA n_list=prog_nums {fun gram -> List.cons (n gram) (n_list gram)}

prog_stmt_list:
  | LEFT_SQUARE RIGHT_SQUARE {fun _ -> []}
  | LEFT_SQUARE s_list=prog_stmts RIGHT_SQUARE {fun gram -> (s_list gram)}

prog_stmts:
  | s=prog_stmt {fun gram -> [(s gram)]}
  | s=prog_stmt COMMA s_list=prog_stmts {fun gram -> List.cons (s gram) (s_list gram)}

// Parse Nonterminal "Strongest"
strongest:
  | NONE_KWD {None}
  | SOME_KWD LEFT_PAREN v_list=var_pairs_list COLON form=formula_or_hole RIGHT_PAREN {Some (v_list, form)}

var_pairs_list:
  | LEFT_SQUARE RIGHT_SQUARE {[]}
  | LEFT_SQUARE v_list=var_pairs RIGHT_SQUARE {v_list}

var_pairs:
  | v=var_pair {[v]}
  | v=var_pair SEMICOLON v_list=var_pairs {List.cons v v_list}

var_pair:
  | LEFT_PAREN v1=var COMMA v2=var RIGHT_PAREN {match (v1, v2) with
    | (TermVar _, TermVar _) -> (v1, v2)
    | (ATermVar _, ATermVar _) -> (v1, v2)
    | (BoolVar _, BoolVar _) -> (v1, v2)
    | (ABoolVar _, ABoolVar _) -> (v1, v2)
    | _ -> raise Parse_Bad_Formula}

var:
  | INT_KWD s=STRING {TermVar (T s)}
  | INT_KWD ET {TermVar ET}
  | ARRAY_INT_KWD s=STRING {ATermVar (T s)}
  | ARRAY_INT_KWD ET {ATermVar ET}
  | BOOL_KWD s=STRING {BoolVar (B s)}
  | BOOL_KWD BT {BoolVar BT}
  | ARRAY_BOOL_KWD s1=STRING {ABoolVar (B s1)}
  | ARRAY_BOOL_KWD BT {ABoolVar BT}
  
formula_or_hole:
  | LEFT_PAREN HOLE_KWD COLON s=STRING vl=vars_list RIGHT_PAREN {BHole (s, vl)}
  | f=formula {f}

vars_list:
  | LEFT_SQUARE RIGHT_SQUARE {[]}
  | LEFT_SQUARE v_list=vars RIGHT_SQUARE {v_list}

vars:
  | v=var_as_exp {[v]}
  | v=var_as_exp COMMA v_list=vars {List.cons v v_list}

var_as_exp:
  | INT_KWD ET {Term (TVar ET)}
  | BOOL_KWD BT {Logic.Formula.Boolean (BVar BT)}
  | INT_KWD s=STRING {Term (TVar (T s))}
  | BOOL_KWD s=STRING {Logic.Formula.Boolean (BVar (B s))}
  | ARRAY_INT_KWD ET {Term (ATVar (TUnApp ET))}
  | ARRAY_BOOL_KWD BT {Logic.Formula.Boolean (ABVar (BUnApp BT))}
  | ARRAY_INT_KWD s=STRING {Term (ATVar (TUnApp (T s)))}
  | ARRAY_BOOL_KWD s=STRING {Logic.Formula.Boolean (ABVar (BUnApp (B s)))}