%{  open Logic
    open Logic.Formula
    open Logic.Variable
    open Programs.Program
    exception Parse_Bad_TVar
    exception Parse_Bad_BVar
    exception Parse_Bad_Var
    exception Parse_Bad_Equals_Type_Mismatch
    exception Parse_Bad_Prog_Int
    let make_exists body quant = Formula.Exists (quant, body)
    let make_forall body quant = Formula.Forall (quant, body)
    let variable_context = (ref [])
    let popper chop_num = variable_context := (List.filteri (fun i _ -> (i >= chop_num)) !variable_context)  
%}

%token <int> INT
%token <string> STRING
%token INT_KWD
%token BOOL_KWD
%token STMT_KWD
%token NOT
%token AND
%token OR
%token TRUE
%token FALSE
%token PLUS
%token MINUS
%token EQUALS
%token IMPLIES
%token LESS
%token LESS_EQUALS
%token GREATER
%token GREATER_EQUALS
%token ASSIGN
%token SEMICOLON
%token IF
%token THEN
%token ELSE
%token WHILE
%token EXISTS
%token FORALL
%token LEFT_PAREN
%token RIGHT_PAREN
%token LEFT_FORM_DEMARCATOR
%token RIGHT_FORM_DEMARCATOR
%start <ProofRule.triple> ultriple
%%

// Parse UL triples.
ultriple:
    LEFT_FORM_DEMARCATOR pren=formula RIGHT_FORM_DEMARCATOR progn=program LEFT_FORM_DEMARCATOR postn=formula RIGHT_FORM_DEMARCATOR {{ProofRule.pre = pren; prog = progn; post = postn}}



// Utilities for parsing formulas -- Should roughly match smt2 format
form_args_list:
  |LEFT_PAREN RIGHT_PAREN {[]}
  |LEFT_PAREN args=form_args RIGHT_PAREN {variable_context := List.append args !variable_context; args}

form_args:
  |LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN {[Variable.TermVar (T s)]}
  |LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN {[Variable.BoolVar (B s)]}
  |LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN args=form_args {List.cons (Variable.TermVar (T s)) args}
  |LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN args=form_args {List.cons (Variable.BoolVar (B s)) args}

form_term:
  | i = INT {Int i}
  | s = STRING {if s = "e_t" then (TVar ET) else (if (List.mem (Variable.TermVar (T s)) !variable_context) then (TVar (T s)) else raise Parse_Bad_TVar)}
  | LEFT_PAREN MINUS t=form_term RIGHT_PAREN {Formula.Minus t}
  | LEFT_PAREN PLUS t1=form_term t2=form_term RIGHT_PAREN {Formula.Plus (t1, t2)}

formula:
  | TRUE {True}
  | FALSE {False}
  | s = STRING {if s = "b_t" then (BVar BT) else (if (List.mem (Variable.BoolVar (B s)) !variable_context) then (BVar (B s)) else raise Parse_Bad_BVar)}
  | LEFT_PAREN AND f1=formula f2=formula RIGHT_PAREN {And (f1, f2)}
  | LEFT_PAREN OR f1=formula f2=formula RIGHT_PAREN {Or (f1, f2)}
  | LEFT_PAREN NOT f=formula RIGHT_PAREN {Not f}
  | LEFT_PAREN IMPLIES f1=formula f2=formula RIGHT_PAREN {Implies (f1, f2)}
  | LEFT_PAREN EQUALS e1=form_exp e2=form_exp RIGHT_PAREN {
    match e1, e2 with 
    | Formula.Term t1, Formula.Term t2 -> Equals (t1, t2)
    | Boolean b1, Boolean b2 -> Iff (b1, b2)
    | _, _ -> raise Parse_Bad_Equals_Type_Mismatch}
  | LEFT_PAREN LESS t1=form_term t2=form_term RIGHT_PAREN {Less (t1, t2)}
  | LEFT_PAREN LESS_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Or (Less (t1, t2), Equals (t1, t2))}
  | LEFT_PAREN GREATER t1=form_term t2=form_term RIGHT_PAREN {Less (t2, t1)}
  | LEFT_PAREN GREATER_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Or (Less (t2, t1), Equals (t2, t1))}
  | EXISTS quants=form_args_list body=formula {popper (List.length quants); (List.fold_left make_exists body quants)} 
  | FORALL quants=form_args_list body=formula {popper (List.length quants); (List.fold_left make_forall body quants)} 
  
form_exp:
  | i = INT {Term (Int i)}
  | LEFT_PAREN MINUS t=form_term RIGHT_PAREN {Term (Formula.Minus t)}
  | LEFT_PAREN PLUS t1=form_term t2=form_term RIGHT_PAREN {Term (Formula.Plus (t1, t2))}
  | TRUE {Boolean True}
  | FALSE {Boolean False}
  | LEFT_PAREN AND f1=formula f2=formula RIGHT_PAREN {Boolean (And (f1, f2))}
  | LEFT_PAREN OR f1=formula f2=formula RIGHT_PAREN {Boolean (Or (f1, f2))}
  | LEFT_PAREN NOT f=formula RIGHT_PAREN {Boolean (Not f)}
  | LEFT_PAREN IMPLIES f1=formula f2=formula RIGHT_PAREN {Boolean (Implies (f1, f2))}
  | LEFT_PAREN EQUALS e1=form_exp e2=form_exp RIGHT_PAREN {
    match e1, e2 with 
    | Formula.Term t1, Formula.Term t2 -> Boolean (Equals (t1, t2))
    | Boolean b1, Boolean b2 -> Boolean (Iff (b1, b2))
    | _, _ -> raise Parse_Bad_Equals_Type_Mismatch}
  | LEFT_PAREN LESS t1=form_term t2=form_term RIGHT_PAREN {Boolean (Less (t1, t2))}
  | LEFT_PAREN LESS_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Boolean (Or (Less (t1, t2), Equals (t1, t2)))}
  | LEFT_PAREN GREATER t1=form_term t2=form_term RIGHT_PAREN {Boolean (Less (t2, t1))}
  | LEFT_PAREN GREATER_EQUALS t1=form_term t2=form_term RIGHT_PAREN {Boolean (Or (Less (t2, t1), Equals (t2, t1)))}
  | EXISTS quants=form_args_list body=formula {popper (List.length quants); Boolean (List.fold_left make_exists body quants)} 
  | FORALL quants=form_args_list body=formula {popper (List.length quants); Boolean (List.fold_left make_forall body quants)} 
  | s = STRING {if s = "e_t" then Term (TVar ET) 
  else if s = "b_t" then Boolean (BVar BT)
  else if (List.mem (BoolVar (B s)) !variable_context) then Boolean (BVar (B s)) 
  else if (List.mem (TermVar (T s)) !variable_context) then Term (TVar (T s))
  else raise Parse_Bad_Var}
  

// Utilities for program parsing  
prog_num: 
  | i = INT {if i = 0 then Zero else if i = 1 then One else raise Parse_Bad_Prog_Int}
  | LEFT_PAREN PLUS n1=prog_num n2=prog_num RIGHT_PAREN {Plus (n1, n2)}
  | LEFT_PAREN IF b=prog_bool THEN n1=prog_num ELSE n2=prog_num RIGHT_PAREN {ITE (b, n1, n2)}
  | s = STRING {Var s}
//   NNterm

prog_bool:
 | TRUE {True}
 | FALSE {False}
 | LEFT_PAREN NOT b=prog_bool RIGHT_PAREN {Not b}
 | LEFT_PAREN OR b1=prog_bool b2=prog_bool RIGHT_PAREN {Or (b1, b2)}
 | LEFT_PAREN AND b1=prog_bool b2=prog_bool RIGHT_PAREN {And (b1, b2)}
 | LEFT_PAREN EQUALS n1=prog_num n2=prog_num RIGHT_PAREN {Equals (n1, n2)}
 | LEFT_PAREN LESS n1=prog_num n2=prog_num RIGHT_PAREN {Less (n1, n2)}
//  BNterm

prog_stmt:
  | LEFT_PAREN ASSIGN s=STRING t=prog_num RIGHT_PAREN {Assign (s, t)}
  | LEFT_PAREN SEMICOLON s1=prog_stmt s2=prog_stmt RIGHT_PAREN {Seq (s1, s2)}
  | LEFT_PAREN IF b=prog_bool THEN s1=prog_stmt ELSE s2=prog_stmt RIGHT_PAREN {ITE (b, s1, s2)}
  | LEFT_PAREN WHILE b=prog_bool LEFT_FORM_DEMARCATOR f=formula RIGHT_FORM_DEMARCATOR s=prog_stmt RIGHT_PAREN {While (b, f, s)}
//   SNTerm


program:
    | INT_KWD n=prog_num {Numeric n}
    | BOOL_KWD b=prog_bool {Boolean b}
    | STMT_KWD p=prog_stmt {Stmt p}