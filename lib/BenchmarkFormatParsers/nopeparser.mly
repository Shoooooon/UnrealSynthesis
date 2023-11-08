%{  open Logic.Formula
    open Logic.Variable
    open Programs.Program
    exception Bad
%}

%token <int> INT
%token <string> STRING
%token SYNTH_FUN
%token INT_KWD
%token BOOL_KWD
%token NOT
%token AND
%token OR
%token TRUE
%token FALSE
%token PLUS
%token EQUALS
%token LESS
%token LESS_EQUALS
%token GREATER
%token GREATER_EQUALS
%token ITE
%token LEFT_PAREN
%token RIGHT_PAREN
%start <Proofrules.ProofRule.triple> triple
%%

// The most general treatement since we can have finitely many examples is to treat everything as vectors. 
// Then, when we process internally, we will ahve a finite vector-state mode that can untangle this. 

// Entire triple to prove
triple:
conds=examples_to_pre_post prog=prog {
      {Proofrules.ProofRule.pre = (fst conds); prog = prog; post = (snd conds)}}


// Parse Examples First:
examples_to_pre_post:
    vl=vars_list il=int_list {
      (match (List.fold_left (fun (index, form, outs, vars) integer ->
          (match vars with
          | [] -> (index + 1, form, Logic.Formula.And (outs, (Equals (ITerm (AITVar (ITApp (ET, Int index))), ITerm (Int integer)))), vl)
          | (hd::tl) -> (index, Logic.Formula.And (form, Equals (ITerm (AITVar (ITApp ((T hd), Int index))), ITerm (Int integer))), outs, tl)))
          (1, Logic.Formula.True, Logic.Formula.True, vl)
          il) with
          | (_, pre, post, _) -> (pre, Not post))
    }

vars_list:
    v=var {[v]}
    | v=var vl=vars_list {List.cons v vl}

var:
  s=STRING{s}

int_list:
    i=INT {[i]}
    | i=INT il=int_list {List.cons i il}

// Instantiate programs:
prog:
    LEFT_PAREN SYNTH_FUN STRING LEFT_PAREN tvl=typed_vars_list_parens RIGHT_PAREN INT_KWD LEFT_PAREN grammar=grammar RIGHT_PAREN RIGHT_PAREN {
      (let pairs = 
      (* TODO: We need b_t=b_t_2 and same for e_t so that, when nonterminals are plugged in, we generate e_t_y and b_t_y.
          At some point, we should remove these equalities and make the special behavior of e_t and b_t explicit when applying Adapt. *)
      List.cons (ABoolVar BT, ABoolVar (B "b_t_cpy")) 
      (List.cons (AIntTermVar ET, AIntTermVar (T "e_t_cpy"))
      (List.map (fun x -> 
      match x with
      | AIntTermVar _ -> (x, (AIntTermVar (T (Printf.sprintf "%s_cpy" (var_tostr x)))))
      | ABoolVar _ -> (x, (ABoolVar (B (Printf.sprintf "%s_cpy" (var_tostr x)))))
      | _ -> raise Bad) tvl) )
      in
      let strongest_maker nterm_prog =
        lazy (let name = (match nterm_prog with | Term (Numeric (NNTerm n)) -> (Programs.NonTerminal.name n) | Boolean (BNTerm b) -> (Programs.NonTerminal.name b) | Stmt (SNTerm s) -> (Programs.NonTerminal.name s) | _ -> raise Bad) in
        let reassigned_vars = reassigned_vars_clean nterm_prog in
        let reassigned_pairs = (List.filter (fun (x, _) -> (VS.mem x (reassigned_vars))) pairs) 
        in
        let reassigned_vars_and_copies = (List.fold_left (fun set (x,y) -> VS.add x (VS.add y set)) VS.empty reassigned_pairs)
(*        (List.fold_left (fun lst (a,b) -> List.cons a (List.cons b lst)) [] (List.filter (fun (x, _) -> (VS.mem x reassigned_vars)) pairs))*) 
        and program_vars = (get_program_vars nterm_prog) in
        Some (reassigned_pairs, 
        BHole ((Printf.sprintf "hole_%s" name), 
        (List.map (fun x -> match x with IntTermVar ET -> (Logic.Formula.Term (ITerm (AITVar (ITUnApp ET)))) 
          | IntTermVar (T t) -> (Term (ITerm (AITVar (ITUnApp (T t))))) 
          | BoolVar BT -> (Boolean (ABVar (BUnApp BT)))
          | BoolVar (B b) -> (Boolean (ABVar (BUnApp (B b))))
          | _ -> raise Bad)
         (VS.elements (VS.remove (ABoolVar (B "b_t_cpy")) (VS.remove (AIntTermVar (T "e_t_cpy")) (VS.union program_vars reassigned_vars_and_copies))))
         )))) 
      in
        Term (Numeric ((fun gram -> (if (List.exists (fun n -> (Programs.NonTerminal.name n)= "Start") (Lazy.force gram).grammar_num)
    then (NNTerm (List.find (fun n -> (Programs.NonTerminal.name n) = "Start") (Lazy.force gram).grammar_num)) 
    else (raise Bad))) (grammar strongest_maker))))
    }

typed_vars_list_parens:
    LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN {
        [AIntTermVar (T s)]}
    | LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN {
        [ABoolVar (B s)]}
    | LEFT_PAREN s=STRING INT_KWD RIGHT_PAREN vl=typed_vars_list_parens {
        List.cons (AIntTermVar (T s)) vl}
    | LEFT_PAREN s=STRING BOOL_KWD RIGHT_PAREN vl=typed_vars_list_parens {
        List.cons (ABoolVar (B s)) vl}


// Parse grammar
grammar:
    nt_list=nonterminal_defs
    {(fun strongest_maker -> (
      let rec grammar =  lazy {
          grammar_num = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Term (Numeric (NNTerm n)) -> Some {Programs.NonTerminal.name=n.name; expansions=lazy (List.map (subs_nonterms_numeric grammar) (Lazy.force n.expansions)); strongest=(strongest_maker (Term (Numeric (NNTerm { Programs.NonTerminal.name = n.name; expansions=lazy (List.map (subs_nonterms_numeric grammar) (Lazy.force n.expansions)); strongest = lazy None}))))}
        | _ -> None)) (nt_list (grammar)));
        grammar_bitv = [];
        grammar_bool = (List.filter_map (fun nterm_dummy -> 
      (match nterm_dummy with 
        | Boolean (BNTerm b) -> Some {Programs.NonTerminal.name=b.name; expansions=lazy (List.map (subs_nonterms_boolean grammar) (Lazy.force b.expansions)); strongest=(strongest_maker (Boolean (BNTerm { Programs.NonTerminal.name = b.name; expansions=lazy (List.map (subs_nonterms_boolean grammar) (Lazy.force b.expansions)); strongest = lazy None})))}
        | _ -> None)) (nt_list (grammar)));
        grammar_stmt = []
      } in 
      grammar))
    }
    
nonterminal_defs:
  | n=nonterminal_def {fun gram -> [(n gram)]}
  | n=nonterminal_def n_list=nonterminal_defs {fun gram -> List.cons (n gram) (n_list gram)}

nonterminal_def:
  | LEFT_PAREN name_str=STRING INT_KWD LEFT_PAREN expansions=prog_nums RIGHT_PAREN RIGHT_PAREN {fun gram -> Term (Numeric (NNTerm { name = name_str; expansions = lazy (expansions gram); strongest = lazy None;}))}
  | LEFT_PAREN name_str=STRING BOOL_KWD LEFT_PAREN expansions=prog_bools RIGHT_PAREN RIGHT_PAREN {fun gram -> Boolean (BNTerm { name = name_str; expansions = lazy (expansions gram); strongest = lazy None;})}
  
prog_bools:
  | b=prog_bool {fun gram -> [(b gram)]}
  | b=prog_bool b_list=prog_bools {fun gram -> List.cons (b gram) (b_list gram)}
  
prog_nums:
  | n=prog_num {fun gram -> [(n gram)]}
  | n=prog_num n_list=prog_nums {fun gram -> List.cons (n gram) (n_list gram)}


// Utilities for program parsing 
// Note, all returns will be functions that take in a lazy grammar. This prevents different parses from interfering with one another. 
prog_num: 
  | i = INT {fun _ -> Int i}
  | LEFT_PAREN PLUS n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> Plus ((n1 gram), (n2 gram))}
  | LEFT_PAREN ITE b=prog_bool n1=prog_num n2=prog_num RIGHT_PAREN {fun gram -> ITE ((b gram), (n1 gram), (n2 gram))}
  | s = STRING {fun gram -> (if (List.exists (fun n -> (Programs.NonTerminal.name n)= s) (Lazy.force gram).grammar_num)
    then (NNTerm (List.find (fun n -> (Programs.NonTerminal.name n) = s) (Lazy.force gram).grammar_num)) 
    else (Var s))
    }

prog_term:
  | n=prog_num {fun gram -> Numeric (n gram)}

prog_bool:
 | TRUE {fun _ ->True}
 | FALSE {fun _ -> False}
 | LEFT_PAREN NOT b=prog_bool RIGHT_PAREN {fun gram -> Not (b gram)}
 | LEFT_PAREN OR b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> Or ((b1 gram), (b2 gram))}
 | LEFT_PAREN AND b1=prog_bool b2=prog_bool RIGHT_PAREN {fun gram -> And ((b1 gram), (b2 gram))}
 | LEFT_PAREN EQUALS n1=prog_term n2=prog_term RIGHT_PAREN {fun gram -> Equals ((n1 gram), (n2 gram))}
 | LEFT_PAREN LESS n1=prog_term n2=prog_term RIGHT_PAREN {fun gram -> Less ((n1 gram), (n2 gram))}
 | LEFT_PAREN LESS_EQUALS n1=prog_term n2=prog_term RIGHT_PAREN {fun gram -> Or (Less ((n1 gram), (n2 gram)), Equals ((n1 gram), (n2 gram)))}
 | LEFT_PAREN GREATER n1=prog_term n2=prog_term RIGHT_PAREN {fun gram -> Not (Less ((n1 gram), (n2 gram)))}
 | LEFT_PAREN GREATER_EQUALS n1=prog_term n2=prog_term RIGHT_PAREN {fun gram -> Not (Less ((n1 gram), (n2 gram)))}
 | s = STRING {fun gram -> (if (List.exists (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    then BNTerm (List.find (fun b -> (Programs.NonTerminal.name b) = s) (Lazy.force gram).grammar_bool)
    else BNTerm ({name=s; expansions=lazy []; strongest=lazy None}))
    }
