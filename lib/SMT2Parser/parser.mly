%{
    open Logic
    let make_exists body quant = Formula.Exists (quant, body)
    let make_forall body quant = Formula.Forall (quant, body)
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
  | LEFT_PAREN DEF_FUN fn_name=STRING args_list BOOL_KWD fn_body=form RIGHT_PAREN {(fn_name, fn_body)}

args_list:
  |LEFT_PAREN RIGHT_PAREN {[]}
  |LEFT_PAREN args RIGHT_PAREN {[]}

args:
  |LEFT_PAREN STRING INT_KWD RIGHT_PAREN {0}
  |LEFT_PAREN STRING BOOL_KWD RIGHT_PAREN {0}
  |LEFT_PAREN STRING BOOL_KWD RIGHT_PAREN args {0}
  |LEFT_PAREN STRING INT_KWD RIGHT_PAREN args {0}

term:
  | i = INT {Int i}
  | s = STRING {if s = "e_t" then (TVar ET) else (TVar (T s))}
  | LEFT_PAREN MINUS t=term RIGHT_PAREN {Formula.Minus t}
  | LEFT_PAREN PLUS t1=term t2=term RIGHT_PAREN {Formula.Plus (t1, t2)}

// Note: Reduce/reduce conflict with (= ... ) since it's polymorphic
// TODO: In general, we may want to introduce a better interface between our formula implementation and this SMT2 one
form:
  | TRUE {True}
  | FALSE {False}
  | s = STRING {if s = "b_t" then (BVar BT) else (BVar (B s))}
  | LEFT_PAREN AND f1=form f2=form RIGHT_PAREN {And (f1, f2)}
  | LEFT_PAREN OR f1=form f2=form RIGHT_PAREN {Or (f1, f2)}
  | LEFT_PAREN NOT f=form RIGHT_PAREN {Not f}
  | LEFT_PAREN IMPLIES f1=form f2=form RIGHT_PAREN {Implies (f1, f2)}
  | LEFT_PAREN EQUALS t1=term t2=term RIGHT_PAREN {Equals (t1, t2)}
  | LEFT_PAREN EQUALS f1=form f2=form RIGHT_PAREN {Iff (f1, f2)}
  | LEFT_PAREN LESS t1=term t2=term RIGHT_PAREN {Less (t1, t2)}
  | LEFT_PAREN LESS_EQUALS t1=term t2=term RIGHT_PAREN {Or (Less (t1, t2), Equals (t1, t2))}
  | LEFT_PAREN GREATER t1=term t2=term RIGHT_PAREN {Less (t2, t1)}
  | LEFT_PAREN GREATER_EQUALS t1=term t2=term RIGHT_PAREN {Or (Less (t2, t1), Equals (t2, t1))}
  | EXISTS quants=args_list body=form {(List.fold_left make_exists body quants)} 
  | FORALL quants=args_list body=form {(List.fold_left make_forall body quants)} 
  