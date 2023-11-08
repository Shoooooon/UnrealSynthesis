%{  open Logic
    open Logic.Formula
    open Logic.Variable
    open Programs.Program
    exception Parse_Bad_Formula
    let make_exists body quant = Formula.Exists (quant, body)
    let make_forall body quant = Formula.Forall (quant, body)
%}

%token <int> INT
%token <string> BITV
%token <string> STRING
%token INT_KWD
%token ARRAY_INT_KWD
%token BITVEC_KWD
%token ARRAY_BITVEC_KWD
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
%token BVNEG
%token BVADD
%token BVMULT
%token BVSUB
%token BVOR
%token BVXOR
%token BVAND
%token PLUS
%token TIMES
%token MINUS
%token EQUALS
%token BVEQUALS
%token IFF
%token IMPLIES
%token LESS
%token BVLESS
%token LESS_EQUALS
%token GREATER
%token GREATER_EQUALS
%token ASSIGN
%token BVASSIGN
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
        | Term (Numeric (NNTerm n)) -> Some {Programs.NonTerminal.name=n.name; expansions=lazy (List.map (subs_nonterms_numeric grammar) (Lazy.force n.expansions)); strongest=n.strongest}
        | _ -> None)) (nt_list grammar));
        grammar_bitv = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Term (Bitvec (BitvNTerm n)) -> Some {Programs.NonTerminal.name=n.name; expansions=lazy (List.map (subs_nonterms_bitvec grammar) (Lazy.force n.expansions)); strongest=n.strongest}
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
  | LEFT_PAREN ET INT_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN ET ARRAY_INT_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN ET BITVEC_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN ET ARRAY_BITVEC_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN BT BOOL_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN BT ARRAY_BOOL_KWD RIGHT_PAREN {raise Parse_Bad_Formula}
  | LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN {Variable.IntTermVar (T s)}
  | LEFT_PAREN s=STRING BITVEC_KWD RIGHT_PAREN {Variable.BitvTermVar (T s)}
  | LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN {Variable.BoolVar (B s)}
  | LEFT_PAREN s=STRING ARRAY_INT_KWD RIGHT_PAREN {Variable.AIntTermVar (T s)}
  | LEFT_PAREN s=STRING ARRAY_BITVEC_KWD RIGHT_PAREN {Variable.ABitvTermVar (T s)}
  | LEFT_PAREN s=STRING ARRAY_BOOL_KWD RIGHT_PAREN {Variable.ABoolVar (B s)}

form_int_term:
  | i = INT {Int i}
  | ET {ITVar ET}
  | ET LEFT_SQUARE index=form_int_term RIGHT_SQUARE {AITVar (ITApp (ET, index))}
  | s = STRING {ITVar (T s)}
  | s = STRING LEFT_SQUARE index=form_int_term RIGHT_SQUARE {AITVar (ITApp (T s, index))}
  | LEFT_PAREN MINUS t=form_int_term RIGHT_PAREN {Formula.Minus t}
  | LEFT_PAREN PLUS t1=form_int_term t2=form_int_term RIGHT_PAREN {Formula.Plus (t1, t2)}
  | LEFT_PAREN TIMES t1=form_int_term t2=form_int_term RIGHT_PAREN {Formula.Times (t1, t2)}

form_bitv_term:
  | btv = BITV {(Bitv btv)}
  | ET {BitvTVar ET}
  | ET LEFT_SQUARE index=form_int_term RIGHT_SQUARE {ABitvTVar (BitvTApp (ET, index))}
  | s = STRING {BitvTVar (T s)}
  | s = STRING LEFT_SQUARE index=form_int_term RIGHT_SQUARE {ABitvTVar (BitvTApp (T s, index))}
  | LEFT_PAREN BVNEG btv=form_bitv_term RIGHT_PAREN {(Formula.BitvUnarApp (Minus, btv))}
  | LEFT_PAREN BVADD btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (Plus, btv1, btv2))}
  | LEFT_PAREN BVMULT btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (Mult, btv1, btv2))}
  | LEFT_PAREN BVSUB btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (Sub, btv1, btv2))}
  | LEFT_PAREN BVOR btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (Or, btv1, btv2))}
  | LEFT_PAREN BVXOR btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (Xor, btv1, btv2))}
  | LEFT_PAREN BVAND btv1=form_bitv_term btv2=form_bitv_term RIGHT_PAREN {(Formula.BitvBinarApp (And, btv1, btv2))}
  
formula:
  | TRUE {True}
  | FALSE {False}
  | BT {BVar BT}
  | BT LEFT_SQUARE index=form_int_term RIGHT_SQUARE {ABVar (BApp (BT, index))}
  | s = STRING {BVar (B s)}
  | s = STRING LEFT_SQUARE index=form_int_term RIGHT_SQUARE {ABVar (BApp (B s, index))}
  | LEFT_PAREN AND f1=formula f2=formula RIGHT_PAREN {And (f1, f2)}
  | LEFT_PAREN OR f1=formula f2=formula RIGHT_PAREN {Or (f1, f2)}
  | LEFT_PAREN NOT f=formula RIGHT_PAREN {Not f}
  | LEFT_PAREN IMPLIES f1=formula f2=formula RIGHT_PAREN {Implies (f1, f2)}
  | LEFT_PAREN EQUALS t1=form_int_term t2=form_int_term RIGHT_PAREN {Equals (ITerm t1, ITerm t2)}
  | LEFT_PAREN BVEQUALS t1=form_bitv_term t2=form_bitv_term RIGHT_PAREN {Equals (BitvTerm t1, BitvTerm t2)}
  | LEFT_PAREN IFF b1=formula b2=formula RIGHT_PAREN {Iff (b1, b2)}
  | LEFT_PAREN LESS t1=form_int_term t2=form_int_term RIGHT_PAREN {Less (ITerm t1, ITerm t2)}
  | LEFT_PAREN BVLESS t1=form_bitv_term t2=form_bitv_term RIGHT_PAREN {Less (BitvTerm t1, BitvTerm t2)}
  | LEFT_PAREN LESS_EQUALS t1=form_int_term t2=form_int_term RIGHT_PAREN {Or (Less (ITerm t1, ITerm t2), Equals (ITerm t1, ITerm t2))}
  | LEFT_PAREN GREATER t1=form_int_term t2=form_int_term RIGHT_PAREN {Less (ITerm t1, ITerm t2)}
  | LEFT_PAREN GREATER_EQUALS t1=form_int_term t2=form_int_term RIGHT_PAREN {Or (Less (ITerm t1, ITerm t2), Equals (ITerm t1, ITerm t2))}
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

prog_bitv: 
  | btv = BITV {fun _ -> Bitv btv}
  | LEFT_PAREN BVADD btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (Plus, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVMULT btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (Mult, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVSUB btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (Sub, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVOR btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (Or, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVXOR btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (Xor, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVAND btv1=prog_bitv btv2=prog_bitv RIGHT_PAREN {fun gram -> BinApp (And, (btv1 gram), (btv2 gram))}
  | LEFT_PAREN BVNEG btv=prog_bitv RIGHT_PAREN {fun gram -> BitvUnApp (Minus, (btv gram))}
  | LEFT_PAREN IF b=prog_bool THEN btv1=prog_bitv ELSE btv2=prog_bitv RIGHT_PAREN {fun gram -> BitvITE ((b gram), (btv1 gram), (btv2 gram))}
  | NT_KWD s = STRING {fun gram -> (if (List.exists (fun n -> (Programs.NonTerminal.name n)= s) (Lazy.force gram).grammar_bitv)
    then (BitvNTerm (List.find (fun n -> (Programs.NonTerminal.name n) = s) (Lazy.force gram).grammar_bitv)) 
    else (BitvNTerm ({name=s; expansions=lazy []; strongest=lazy None})))
    }
  | s = STRING {fun _ -> BitvVar s}

prog_bool:
 | TRUE {fun _ ->True}
 | FALSE {fun _ -> False}
 | LEFT_PAREN NOT b=prog_bool RIGHT_PAREN {fun gram -> Not (b gram)}
 | LEFT_PAREN OR b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> Or ((b1 gram), (b2 gram))}
 | LEFT_PAREN AND b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> And ((b1 gram), (b2 gram))}
 | LEFT_PAREN EQUALS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Equals (Numeric (n1 gram), Numeric (n2 gram))}
 | LEFT_PAREN BVEQUALS n1=prog_bitv n2=prog_bitv RIGHT_PAREN {fun gram -> Equals (Bitvec (n1 gram), Bitvec (n2 gram))}
 | LEFT_PAREN LESS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Less (Numeric (n1 gram), Numeric (n2 gram))}
 | LEFT_PAREN BVLESS n1=prog_bitv n2=prog_bitv RIGHT_PAREN {fun gram -> Less (Bitvec (n1 gram), Bitvec (n2 gram))}
 | NT_KWD s = STRING {fun gram -> (if (List.exists (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    then BNTerm (List.find (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    else BNTerm ({name=s; expansions=lazy []; strongest=lazy None}))
    }

prog_stmt:
  | LEFT_PAREN ASSIGN s=STRING t=prog_num RIGHT_PAREN {fun gram -> Assign (s, Numeric (t gram))}
  | LEFT_PAREN BVASSIGN s=STRING t=prog_bitv RIGHT_PAREN {fun gram -> Assign (s, Bitvec (t gram))}
  | LEFT_PAREN SEMICOLON s1=prog_stmt s2=prog_stmt RIGHT_PAREN {fun gram -> Seq ((s1 gram), (s2 gram))}
  | LEFT_PAREN IF b=prog_bool THEN s1=prog_stmt ELSE s2=prog_stmt RIGHT_PAREN {fun gram -> ITE ((b gram), (s1 gram), (s2 gram))}
  | LEFT_PAREN WHILE b=prog_bool LEFT_FORM_DEMARCATOR f=formula RIGHT_FORM_DEMARCATOR s=prog_stmt RIGHT_PAREN {fun gram -> While ((b gram), f, (s gram))}
  | NT_KWD s = STRING {fun gram -> (if (List.exists (fun st -> (Programs.NonTerminal.name st) = s) (Lazy.force gram).grammar_stmt)
    then SNTerm (List.find (fun st -> (Programs.NonTerminal.name st) = s) (Lazy.force gram).grammar_stmt)
    else SNTerm ({name=s; expansions=lazy []; strongest=lazy None}))
    }

program:
    | INT_KWD n=prog_num {fun gram -> Term (Numeric (n gram))}
    | BITVEC_KWD n=prog_bitv {fun gram -> Term (Bitvec (n gram))}
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
  | INT_KWD name=STRING COLON expansions=prog_num_list COLON str=strongest {fun gram -> Term (Numeric (NNTerm { name = name; expansions = lazy (expansions gram); strongest = lazy str;}))}
  | BITVEC_KWD name=STRING COLON expansions=prog_bitv_list COLON str=strongest {fun gram -> Term (Bitvec (BitvNTerm { name = name; expansions = lazy (expansions gram); strongest = lazy str;}))}
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

prog_bitv_list:
  | LEFT_SQUARE RIGHT_SQUARE {fun _ -> []}
  | LEFT_SQUARE n_list=prog_bitvs RIGHT_SQUARE {fun gram -> (n_list gram)}

prog_bitvs:
  | n=prog_bitv {fun gram -> [(n gram)]}
  | n=prog_bitv COMMA n_list=prog_bitvs {fun gram -> List.cons (n gram) (n_list gram)}

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
    | (IntTermVar _, IntTermVar _) -> (v1, v2)
    | (AIntTermVar _, AIntTermVar _) -> (v1, v2)
    | (BitvTermVar _, BitvTermVar _) -> (v1, v2)
    | (ABitvTermVar _, ABitvTermVar _) -> (v1, v2)
    | (BoolVar _, BoolVar _) -> (v1, v2)
    | (ABoolVar _, ABoolVar _) -> (v1, v2)
    | _ -> raise Parse_Bad_Formula}

var:
  | INT_KWD s=STRING {IntTermVar (T s)}
  | INT_KWD ET {IntTermVar ET}
  | ARRAY_INT_KWD s=STRING {AIntTermVar (T s)}
  | ARRAY_INT_KWD ET {AIntTermVar ET}
  | BITVEC_KWD s=STRING {BitvTermVar (T s)}
  | BITVEC_KWD ET {BitvTermVar ET}
  | ARRAY_BITVEC_KWD s=STRING {ABitvTermVar (T s)}
  | ARRAY_BITVEC_KWD ET {ABitvTermVar ET}
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
  | INT_KWD ET {Term (ITerm (ITVar ET))}
  | BITVEC_KWD ET {Term (BitvTerm (BitvTVar ET))}
  | BOOL_KWD BT {Logic.Formula.Boolean (BVar BT)}
  | INT_KWD s=STRING {Term (ITerm (ITVar (T s)))}
  | BITVEC_KWD s=STRING {Term (BitvTerm (BitvTVar (T s)))}
  | BOOL_KWD s=STRING {Logic.Formula.Boolean (BVar (B s))}
  | ARRAY_INT_KWD ET {Term (ITerm (AITVar (ITUnApp ET)))}
  | ARRAY_BITVEC_KWD ET {Term (BitvTerm (ABitvTVar (BitvTUnApp ET)))}
  | ARRAY_BOOL_KWD BT {Logic.Formula.Boolean (ABVar (BUnApp BT))}
  | ARRAY_INT_KWD s=STRING {Term (ITerm (AITVar (ITUnApp (T s))))}
  | ARRAY_BITVEC_KWD s=STRING {Term (BitvTerm (ABitvTVar (BitvTUnApp (T s))))}
  | ARRAY_BOOL_KWD s=STRING {Logic.Formula.Boolean (ABVar (BUnApp (B s)))}