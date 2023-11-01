%{
    open Logic
    open Logic.Formula
    open Logic.Variable
    exception Parse_Bad_ITVar
    exception Parse_Bad_BVar
    exception Parse_Bad_Var
    exception Parse_Bad_Equals_Type_Mismatch
    let make_exists body quant = Formula.Exists (quant, body)
    let make_forall body quant = Formula.Forall (quant, body)
    let variable_context = (ref [])
    let popper chop_num = variable_context := (List.filteri (fun i _ -> (i >= chop_num)) !variable_context)    
%}

%token <int> INT
%token <string> STRING
%token DEF_FUN
%token INT_KWD
%token BOOL_KWD
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
%token EXISTS
%token FORALL
%token LEFT_PAREN
%token RIGHT_PAREN
%start <(string * Logic.Formula.formula)> fun_decl
%%

fun_decl:
  | LEFT_PAREN DEF_FUN fn_name=STRING args=args_list BOOL_KWD fn_body=form RIGHT_PAREN {popper (List.length args); (fn_name, fn_body)}

args_list:
  |LEFT_PAREN RIGHT_PAREN {[]}
  |LEFT_PAREN args=args RIGHT_PAREN {variable_context := List.append args !variable_context; args}

args:
  |LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN {[Variable.IntTermVar (T s)]}
  |LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN {[Variable.BoolVar (B s)]}
  |LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN args=args {List.cons (Variable.IntTermVar (T s)) args}
  |LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN args=args {List.cons (Variable.BoolVar (B s)) args}

term:
  | t=int_term {ITerm t}

int_term:
  | i = INT {Int i}
  | s = STRING {if s = "e_t" then (ITVar ET) else (if (List.mem (Variable.IntTermVar (T s)) !variable_context) then (ITVar (T s)) else raise Parse_Bad_ITVar)}
  | LEFT_PAREN MINUS t=int_term RIGHT_PAREN {Formula.Minus t}
  | LEFT_PAREN PLUS t1=int_term t2=int_term RIGHT_PAREN {Formula.Plus (t1, t2)}

form:
  | TRUE {True}
  | FALSE {False}
  | s = STRING {if s = "b_t" then (BVar BT) else (if (List.mem (Variable.BoolVar (B s)) !variable_context) then (BVar (B s)) else raise Parse_Bad_BVar)}
  | LEFT_PAREN AND f1=form f2=form RIGHT_PAREN {And (f1, f2)}
  | LEFT_PAREN OR f1=form f2=form RIGHT_PAREN {Or (f1, f2)}
  | LEFT_PAREN NOT f=form RIGHT_PAREN {Not f}
  | LEFT_PAREN IMPLIES f1=form f2=form RIGHT_PAREN {Implies (f1, f2)}
  | LEFT_PAREN EQUALS e1=exp e2=exp RIGHT_PAREN {
    match e1, e2 with 
    | Formula.Term t1, Formula.Term t2 -> Equals (t1, t2)
    | Boolean b1, Boolean b2 -> Iff (b1, b2)
    | _, _ -> raise Parse_Bad_Equals_Type_Mismatch}
  | LEFT_PAREN LESS t1=term t2=term RIGHT_PAREN {Less (t1, t2)}
  | LEFT_PAREN LESS_EQUALS t1=term t2=term RIGHT_PAREN {Or (Less (t1, t2), Equals (t1, t2))}
  | LEFT_PAREN GREATER t1=term t2=term RIGHT_PAREN {Less (t2, t1)}
  | LEFT_PAREN GREATER_EQUALS t1=term t2=term RIGHT_PAREN {Or (Less (t2, t1), Equals (t2, t1))}
  | EXISTS quants=args_list body=form {popper (List.length quants); (List.fold_left make_exists body quants)} 
  | FORALL quants=args_list body=form {popper (List.length quants); (List.fold_left make_forall body quants)} 
  
exp:
  | i = INT {Term (ITerm (Int i))}
  | LEFT_PAREN MINUS t=int_term RIGHT_PAREN {Term (ITerm (Formula.Minus t))}
  | LEFT_PAREN PLUS t1=int_term t2=int_term RIGHT_PAREN {Term (ITerm (Formula.Plus (t1, t2)))}
  | TRUE {Boolean True}
  | FALSE {Boolean False}
  | LEFT_PAREN AND f1=form f2=form RIGHT_PAREN {Boolean (And (f1, f2))}
  | LEFT_PAREN OR f1=form f2=form RIGHT_PAREN {Boolean (Or (f1, f2))}
  | LEFT_PAREN NOT f=form RIGHT_PAREN {Boolean (Not f)}
  | LEFT_PAREN IMPLIES f1=form f2=form RIGHT_PAREN {Boolean (Implies (f1, f2))}
  | LEFT_PAREN EQUALS e1=exp e2=exp RIGHT_PAREN {
    match e1, e2 with 
    | Formula.Term t1, Formula.Term t2 -> Boolean (Equals (t1, t2))
    | Boolean b1, Boolean b2 -> Boolean (Iff (b1, b2))
    | _, _ -> raise Parse_Bad_Equals_Type_Mismatch}
  | LEFT_PAREN LESS t1=term t2=term RIGHT_PAREN {Boolean (Less (t1, t2))}
  | LEFT_PAREN LESS_EQUALS t1=term t2=term RIGHT_PAREN {Boolean (Or (Less (t1, t2), Equals (t1, t2)))}
  | LEFT_PAREN GREATER t1=term t2=term RIGHT_PAREN {Boolean (Less (t2, t1))}
  | LEFT_PAREN GREATER_EQUALS t1=term t2=term RIGHT_PAREN {Boolean (Or (Less (t2, t1), Equals (t2, t1)))}
  | EXISTS quants=args_list body=form {popper (List.length quants); Boolean (List.fold_left make_exists body quants)} 
  | FORALL quants=args_list body=form {popper (List.length quants); Boolean (List.fold_left make_forall body quants)} 
  | s = STRING {if s = "e_t" then Term (ITerm (ITVar ET)) 
  else if s = "b_t" then Boolean (BVar BT)
  else if (List.mem (BoolVar (B s)) !variable_context) then Boolean (BVar (B s)) 
  else if (List.mem (IntTermVar (T s)) !variable_context) then Term (ITerm (ITVar (T s)))
  else raise Parse_Bad_Var}
  
