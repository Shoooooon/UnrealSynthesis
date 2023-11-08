open Logic.Formula
open Logic.Variable

exception Unsupported_Formula_Constructor of int
exception Binary_Form_Term_Mismatch
(* exception Bad_Deconjunct of formula *)

module type ImplicationHandler = sig
  val implies : formula -> formula -> bool Lazy.t
  val hole_values : ((string * variable list) * formula) list Lazy.t
end

(* Helper Functions *)
(* Hole checking/manipulating functions *)
let rec has_bholes form =
  match form with
  | True -> false
  | False -> false
  | BVar _ -> false
  | And (l, r) -> has_bholes l || has_bholes r
  | Or (l, r) -> has_bholes l || has_bholes r
  | Not _ -> false
  | Implies (l, r) -> has_bholes l || has_bholes r
  | Equals (_, _) -> false
  | Less (_, _) -> false
  | Iff (l, r) -> has_bholes l || has_bholes r
  | Exists (_, body) -> has_bholes body
  | Forall (_, body) -> has_bholes body
  | BHole (_, _) -> true
  | ABVar _ -> false
  | T (f, _, _) -> has_bholes f
  | TPrime f -> has_bholes f

let rec get_bholes form =
  match form with
  | True -> []
  | False -> []
  | BVar _ -> []
  | And (l, r) -> List.append (get_bholes l) (get_bholes r)
  | Or (l, r) -> List.append (get_bholes l) (get_bholes r)
  | Not _ -> []
  | Implies (l, r) -> List.append (get_bholes l) (get_bholes r)
  | Equals (_, _) -> []
  | Less (_, _) -> []
  | Iff (l, r) -> List.append (get_bholes l) (get_bholes r)
  | Exists (_, body) -> get_bholes body
  | Forall (_, body) -> get_bholes body
  | BHole (h, vl) -> [ (h, vl) ]
  | ABVar _ -> []
  | T (f, _, _) -> get_bholes f
  | TPrime f -> get_bholes f

(* Given a formula A -> (B -> C & D), splits into (A -> (B -> C); A -> (B -> D)).
   Specifically:
   First, collects outermost foralls (i.e. not occuring inside an exists or on LHS of implication) together and makes them program vars.
    Thus, (\forall a ...) && (\forall b ...) becomes (var a) (var b) ... & ..., and when we negate this is fine.
   Then,
    converts A -> B -> C ... into A && B && C ... -> Z.
   Next, pulls exists on LHS out and adds them as vars.
   c*)
(* Collects outermost foralls (i.e. not occuring inside an exists or on LHS of implication) together and makes them program vars.
    Thus, (\forall a ...) && (\forall b ...) becomes (var a) (var b) ... & ..., and when we negate this is fine.
   Also renames variables so that pulling out universal quantifications doesn't cause overshadowing.
   Varlist should start with the unbound vars so those don't get overshadowed. *)
(* let rec universal_collecter formula varset =
     match formula with
     | Implies (a, b) -> (
         match universal_collecter b varset with
         | post, vars -> (Implies (a, post), vars))
     | And (a, b) -> (
         match universal_collecter b varset with
         | sec, vars -> (
             match universal_collecter a vars with
             | fir, vars -> (And (fir, sec), vars)))
     | Forall (v, form) ->
         if List.mem v varset then
           let newv_name = fresh_var_name form (List.map var_tostr varset) in
           let newv =
             match v with
             | IntTermVar _ -> IntTermVar (T newv_name)
             | BoolVar _ -> BoolVar (B newv_name)
             | AIntTermVar _ -> AIntTermVar (T newv_name)
             | ABoolVar _ -> ABoolVar (B newv_name)
           in
           let newv_exp =
             match newv with
             | IntTermVar tv -> Term (ITVar tv)
             | BoolVar bv -> Boolean (BVar bv)
             | AIntTermVar atv -> Term (AITVar (UnApp atv))
             | ABoolVar abv -> Boolean (ABVar (UnApp abv))
           in
           universal_collecter (subs form v newv_exp) (List.cons newv varset)
         else universal_collecter form (List.cons v varset)
     | _ -> (formula, varset)

   (* Converts nested implications to conjunctions (i.e., A -> (B -> (C ...)) into (A && B && C ...) -> Z). *)
   let rec conjunct_collector formula =
     match formula with
     | Implies (a, b) -> (
         match b with
         | Implies (c, d) -> conjunct_collector (Implies (And (a, c), d))
         | _ -> formula)
     | _ -> formula

   (* Splits A -> Z1 && Z2 && ... && Zn into [A -> Z1, ..., A -> Zn]. *)
   let rec deconjunctor formula =
     match formula with
     | Implies (a, b) -> (
         match b with
         | And (c, d) ->
             List.append
               (deconjunctor (Implies (a, c)))
               (deconjunctor (Implies (a, d)))
         | _ -> [ formula ])
     | _ -> [ formula ]

   (* Given (\exists x1. ...) && ... && (\exists xn. ...) -> Z, pulls out existential quantifiers and renames a needed.
      Assumes free variables in entire formula are given in varset as input.*)
   let rec existential_collecter formula varset =
     match formula with
     | And (a, b) -> (
         match existential_collecter b varset with
         | sec, vars -> (
             match existential_collecter a vars with
             | fir, vars -> (And (fir, sec), vars)))
     | Exists (v, form) ->
         if List.mem v varset then
           let newv_name = fresh_var_name form (List.map var_tostr varset) in
           let newv =
             match v with
             | IntTermVar _ -> IntTermVar (T newv_name)
             | BoolVar _ -> BoolVar (B newv_name)
             | AIntTermVar _ -> AIntTermVar (T newv_name)
             | ABoolVar _ -> ABoolVar (B newv_name)
           in
           let newv_exp =
             match newv with
             | IntTermVar tv -> Term (ITVar tv)
             | BoolVar bv -> Boolean (BVar bv)
             | AIntTermVar atv -> Term (AITVar (UnApp atv))
             | ABoolVar abv -> Boolean (ABVar (UnApp abv))
           in
           existential_collecter (subs form v newv_exp) (List.cons newv varset)
         else existential_collecter form (List.cons v varset)
     | _ -> (formula, varset)

   let deconjunctivizer pre post =
     let formula = Implies (pre, post) in
     (* print_endline(form_tostr formula); *)
     (* First, collect Foralls if you can. *)
     let forall_rmvd_formula, varset =
       universal_collecter formula (VS.elements (free_vars formula VS.empty))
     in
     (* print_endline(form_tostr forall_rmvd_formula); *)
     (* Then, convert nested implications A -> (B -> (C ...)) into (A && B && C ...) -> Z. *)
     let conjunct_collected = conjunct_collector forall_rmvd_formula in
     (* print_endline(form_tostr conjunct_collected); *)
     (* Next, extract existential variables from the LHS of the implication. *)
     let exists_rmvd_formula, _ =
       existential_collecter conjunct_collected varset
     in
     print_endline (form_tostr exists_rmvd_formula);
     (* Then, split our formula into a list of constraints if Z is a conjunction. *)
     let deconj_forms = deconjunctor exists_rmvd_formula in
     let final_forms = List.map conjunct_collector deconj_forms in
     List.map
       (fun imp ->
         match imp with
         | Implies (a, b) -> (a, b)
         | _ -> raise (Bad_Deconjunct imp))
       final_forms

   let deconjunctivizer pre post =
     let formula = Implies (pre, post) in
     (* print_endline(form_tostr formula); *)
     (* First, collect Foralls if you can. *)
     let forall_rmvd_formula, varset =
       universal_collecter formula (VS.elements (free_vars formula VS.empty))
     in
     (* print_endline(form_tostr forall_rmvd_formula); *)
     (* Then, convert nested implications A -> (B -> (C ...)) into (A && B && C ...) -> Z. *)
     let conjunct_collected = conjunct_collector forall_rmvd_formula in
     (* print_endline(form_tostr conjunct_collected); *)
     (* Next, extract existential variables from the LHS of the implication. *)
     let exists_rmvd_formula, _ =
       existential_collecter conjunct_collected varset
     in
     print_endline (form_tostr exists_rmvd_formula);
     (* Then, split our formula into a list of constraints if Z is a conjunction. *)
     let deconj_forms = deconjunctor exists_rmvd_formula in
     let final_forms = List.map conjunct_collector deconj_forms in
     List.map
       (fun imp ->
         match imp with
         | Implies (a, b) -> (a, b)
         | _ -> raise (Bad_Deconjunct imp))
       final_forms *)

(* Recursively pulls out \exists on LHS.
   Returns the new formula as well as previously existentially quantified variables (or what they are renamed to). *)
let rec deconjunctivizer_lhs form varset =
  match form with
  | Exists (v, body) ->
      (* Exists on lhs is essentially a forall -- strip and make it a free variable *)
      if List.mem (var_tostr v) (List.map var_tostr (VS.elements varset)) then
        let newv_name =
          fresh_var_name body (List.map var_tostr (VS.elements varset))
        in
        let newv = new_var_of_same_type v newv_name in
        let newv_exp = var_to_exp newv in
        let new_form, varset, existed =
          deconjunctivizer_lhs (subs body v newv_exp) (VS.add newv varset)
        in
        (new_form, varset, VS.add newv existed)
      else
        let form, varset, existed =
          deconjunctivizer_lhs body (VS.add v varset)
        in
        (form, varset, VS.add v existed)
  (* We aren't dealing with implications on LHS -- too complicated and doesn't occur in the system. *)
  (* For conjunctions, we might as well pull out \exists *)
  | And (a, b) ->
      let a_new, varset, a_existed = deconjunctivizer_lhs a varset in
      let b_new, varset, b_existed = deconjunctivizer_lhs b varset in
      (And (a_new, b_new), varset, VS.union a_existed b_existed)
  | _ -> (form, varset, VS.empty)

(* Returns list of form * previously_existed_vars and set of active var names. *)
let rec deconjunctivizer_rhs form varset =
  match form with
  | Forall (v, body) ->
      (* Forall on rhs -- strip and make it a free variable *)
      if List.mem (var_tostr v) (List.map var_tostr (VS.elements varset)) then
        let newv_name =
          fresh_var_name body (List.map var_tostr (VS.elements varset))
        in
        let newv = new_var_of_same_type v newv_name in
        let newv_exp = var_to_exp newv in
        deconjunctivizer_rhs (subs body v newv_exp) (VS.add newv varset)
      else deconjunctivizer_rhs body (VS.add v varset)
  | Implies (lhs, rhs) ->
      (* For Implies, eval the lhs and rhs then take the product of the lists. *)
      let lhs_new, varset, lhs_existed = deconjunctivizer_lhs lhs varset in
      let rhs_news, varset = deconjunctivizer_rhs rhs varset in
      ( List.map
          (fun (rhs_partic, rhs_existed) ->
            match rhs_partic with
            | Implies (a, b) ->
                (Implies (And (lhs_new, a), b), VS.union lhs_existed rhs_existed)
            | _ ->
                (Implies (lhs_new, rhs_partic), VS.union lhs_existed rhs_existed))
          rhs_news,
        varset )
  | And (a, b) ->
      (* For and, eval each side and produce a list -- one formula for each conclusion. *)
      let a_new, varset = deconjunctivizer_rhs a varset in
      let b_new, varset = deconjunctivizer_rhs b varset in
      (List.append a_new b_new, varset)
  | _ -> ([ (form, VS.empty) ], varset)

let deconjunctivizer pre post =
  let form = Implies (pre, post) in
  let frm_nd_existed, _ = deconjunctivizer_rhs form (free_vars form VS.empty) in
  frm_nd_existed

(* WRITING *)
(* Writing formulas to smt files *)
let rec to_smt_helper_int_term int_term =
  match int_term with
  | Int i ->
      if i < 0 then Printf.sprintf "(- %d)" (-1 * i) else Printf.sprintf "%d" i
  | ITVar v -> var_tostr (IntTermVar v)
  | Minus t -> Printf.sprintf "(- %s)" (to_smt_helper_int_term t)
  | Plus (t1, t2) ->
      Printf.sprintf "(+ %s %s)"
        (to_smt_helper_int_term t1)
        (to_smt_helper_int_term t2)
  | Times (t1, t2) ->
      Printf.sprintf "(* %s %s)"
        (to_smt_helper_int_term t1)
        (to_smt_helper_int_term t2)
  | THole (s, arg_list) ->
      Printf.sprintf "(%s %s)" s
        (String.concat " " (List.map to_smt_helper_exp arg_list))
  | _ -> raise (Unsupported_Formula_Constructor 1)

and to_smt_helper_bitv_term bitv_term =
  match bitv_term with
  | Bitv btv -> btv
  | BitvTVar v -> var_tostr (BitvTermVar v)
  | BitvUnarApp (Minus, btv) ->
      Printf.sprintf "(bvnot %s)" (to_smt_helper_bitv_term btv)
  | BitvBinarApp (Plus, btv1, btv2) ->
      Printf.sprintf "(bvadd %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvBinarApp (Mult, btv1, btv2) ->
      Printf.sprintf "(bvmul %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvBinarApp (Sub, btv1, btv2) ->
      Printf.sprintf "(bvsub %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvBinarApp (Or, btv1, btv2) ->
      Printf.sprintf "(bvor %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvBinarApp (Xor, btv1, btv2) ->
      Printf.sprintf "(bvxor %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvBinarApp (And, btv1, btv2) ->
      Printf.sprintf "(bvand %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | BitvTHole (s, arg_list) ->
    Printf.sprintf "(%s %s)" s
      (String.concat " " (List.map to_smt_helper_exp arg_list))
  | _ ->
      raise (Unsupported_Formula_Constructor 71)

and to_smt_helper_term term =
  match term with
  | ITerm it -> to_smt_helper_int_term it
  | BitvTerm bitv -> to_smt_helper_bitv_term bitv

and to_smt_helper form =
  match form with
  | True -> "true"
  | False -> "false"
  | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Or (b1, b2) ->
      Printf.sprintf "(or %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Not b -> Printf.sprintf "(not %s)" (to_smt_helper b)
  | Implies (b1, b2) ->
      Printf.sprintf "(=> %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | BVar v -> var_tostr (BoolVar v)
  | Equals (t1, t2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper_term t1) (to_smt_helper_term t2)
  | Less (ITerm n1, ITerm n2) ->
      Printf.sprintf "(< %s %s)"
        (to_smt_helper_int_term n1)
        (to_smt_helper_int_term n2)
  | Less (BitvTerm btv1, BitvTerm btv2) ->
      Printf.sprintf "(bvult %s %s)"
        (to_smt_helper_bitv_term btv1)
        (to_smt_helper_bitv_term btv2)
  | Less (_, _) -> raise Binary_Form_Term_Mismatch
  | Iff (b1, b2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper b1) (to_smt_helper b2)
  | Exists (IntTermVar v, b) ->
      Printf.sprintf "(exists ((%s Int) ) %s)" (var_tostr (IntTermVar v))
        (to_smt_helper b)
  | Exists (BitvTermVar v, b) ->
      Printf.sprintf "(exists ((%s (_ BitVec %d)) ) %s)"
        (var_tostr (BitvTermVar v))
        Logic.Formula.bvconst (to_smt_helper b)
  | Exists (BoolVar v, b) ->
      Printf.sprintf "(exists ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper b)
  | Forall (IntTermVar v, b) ->
      Printf.sprintf "(forall ((%s Int) ) %s)" (var_tostr (IntTermVar v))
        (to_smt_helper b)
  | Forall (BitvTermVar v, b) ->
      Printf.sprintf "(forall ((%s (_ BitVec %d)) ) %s)"
        (var_tostr (BitvTermVar v))
        Logic.Formula.bvconst (to_smt_helper b)
  | Forall (BoolVar v, b) ->
      Printf.sprintf "(forall ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper b)
  | BHole (s, arg_list) ->
      Printf.sprintf "(%s %s)" s
        (String.concat " " (List.map to_smt_helper_exp arg_list))
  | _ ->
      raise (Unsupported_Formula_Constructor 2)

and to_smt_helper_exp e =
  match e with Term t -> to_smt_helper_term t | Boolean b -> to_smt_helper b

let to_negated_smt_z3 form name =
  Printf.sprintf
    (* (set-logic NIA)\n\ *)
    ";%s\n\
     (set-info :smt-lib-version 2.6)\n\
     (set-info :status unsat)\n\
     %s(assert\n\
     (not\n\
     %s\n\
     )\n\
    \ )\n\
     (check-sat)\n\
     (exit)"
    name
    (VS.fold
       (fun var str ->
         match var with
         | BoolVar _ ->
             Printf.sprintf "%s(declare-const %s Bool)\n" str (var_tostr var)
         | IntTermVar _ ->
             Printf.sprintf "%s(declare-const %s Int)\n" str (var_tostr var)
         | BitvTermVar _ ->
             Printf.sprintf "%s(declare-const %s (_ BitVec %d))\n" str
               (var_tostr var) Logic.Formula.bvconst
         | _ -> raise (Unsupported_Formula_Constructor 3))
       (free_vars form VS.empty) "")
    (to_smt_helper form)

(* Writing formulas to vampire files. *)
let rec to_smt_helper_int_term_vamp int_term =
  match int_term with
  | Int i ->
      if i < 0 then Printf.sprintf "(- %d)" (-1 * i) else Printf.sprintf "%d" i
  | ITVar v -> var_tostr (IntTermVar v)
  | Minus t -> Printf.sprintf "(- %s)" (to_smt_helper_int_term_vamp t)
  | Plus (t1, t2) ->
      Printf.sprintf "(+ %s %s)"
        (to_smt_helper_int_term_vamp t1)
        (to_smt_helper_int_term_vamp t2)
  | Times (t1, t2) ->
      Printf.sprintf "(* %s %s)"
        (to_smt_helper_int_term_vamp t1)
        (to_smt_helper_int_term_vamp t2)
  | AITVar (ITApp (at, i)) ->
      Printf.sprintf "(select %s %s)"
        (var_tostr (AIntTermVar at))
        (to_smt_helper_int_term_vamp i)
  | _ -> raise (Unsupported_Formula_Constructor 4)

let to_smt_helper_bitv_term_vamp bitv_term =
  match bitv_term with
  (* Vampire does not support bitvectors according to github issues & PRs. *)
  | _ -> raise (Unsupported_Formula_Constructor 12)

let to_smt_helper_term_vamp term =
  match term with
  | ITerm it -> to_smt_helper_int_term_vamp it
  | BitvTerm bitv -> to_smt_helper_bitv_term_vamp bitv

let rec to_smt_helper_vamp form =
  match form with
  | True -> "true"
  | False -> "false"
  | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (to_smt_helper_vamp b1)
        (to_smt_helper_vamp b2)
  | Or (b1, b2) ->
      Printf.sprintf "(or %s %s)" (to_smt_helper_vamp b1)
        (to_smt_helper_vamp b2)
  | Not b -> Printf.sprintf "(not %s)" (to_smt_helper_vamp b)
  | Implies (b1, b2) ->
      Printf.sprintf "(=> %s %s)" (to_smt_helper_vamp b1)
        (to_smt_helper_vamp b2)
  | BVar v -> var_tostr (BoolVar v)
  | ABVar (BApp (at, i)) ->
      Printf.sprintf "(select %s %s)" (var_tostr (ABoolVar at))
        (to_smt_helper_int_term_vamp i)
  | Equals (t1, t2) ->
      Printf.sprintf "(= %s %s)"
        (to_smt_helper_term_vamp t1)
        (to_smt_helper_term_vamp t2)
  | Less (t1, t2) ->
      Printf.sprintf "(< %s %s)"
        (to_smt_helper_term_vamp t1)
        (to_smt_helper_term_vamp t2)
  | Iff (b1, b2) ->
      Printf.sprintf "(= %s %s)" (to_smt_helper_vamp b1) (to_smt_helper_vamp b2)
  | Exists (IntTermVar v, b) ->
      Printf.sprintf "(exists ((%s Int) ) %s)" (var_tostr (IntTermVar v))
        (to_smt_helper_vamp b)
  | Exists (AIntTermVar v, b) ->
      Printf.sprintf "(exists ((%s (Array Int Int)) ) %s)"
        (var_tostr (AIntTermVar v))
        (to_smt_helper_vamp b)
  | Exists (BoolVar v, b) ->
      Printf.sprintf "(exists ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper_vamp b)
  | Exists (ABoolVar v, b) ->
      Printf.sprintf "(exists ((%s (Array Int Bool)) ) %s)"
        (var_tostr (ABoolVar v)) (to_smt_helper_vamp b)
  | Forall (IntTermVar v, b) ->
      Printf.sprintf "(forall ((%s Int) ) %s)" (var_tostr (IntTermVar v))
        (to_smt_helper_vamp b)
  | Forall (AIntTermVar v, b) ->
      Printf.sprintf "(forall ((%s (Array Int Int)) ) %s)"
        (var_tostr (AIntTermVar v))
        (to_smt_helper_vamp b)
  | Forall (BoolVar v, b) ->
      Printf.sprintf "(forall ((%s Bool) ) %s)" (var_tostr (BoolVar v))
        (to_smt_helper_vamp b)
  | Forall (ABoolVar v, b) ->
      Printf.sprintf "(forall ((%s (Array Int Bool)) ) %s)"
        (var_tostr (ABoolVar v)) (to_smt_helper_vamp b)
  | BHole (s, arg_list) ->
      Printf.sprintf "(%s %s)" s
        (String.concat " " (List.map to_smt_helper_exp_vamp arg_list))
  | _ -> raise (Unsupported_Formula_Constructor 5)

and to_smt_helper_exp_vamp e =
  match e with
  | Term t -> to_smt_helper_term_vamp t
  | Boolean b -> to_smt_helper_vamp b

let to_negated_smt_vampire form name =
  Printf.sprintf
    ";%s\n(set-info :status unknown)\n%s(assert\n(not\n%s\n)\n )\n(check-sat)"
    name
    (VS.fold
       (fun var str ->
         match var with
         | IntTermVar _ ->
             Printf.sprintf "%s(declare-const %s Int)\n" str (var_tostr var)
         | AIntTermVar _ ->
             Printf.sprintf "%s(declare-const %s (Array Int Int))\n" str
               (var_tostr var)
         | BoolVar _ ->
             Printf.sprintf "%s(declare-const %s Bool)\n" str (var_tostr var)
         | ABoolVar _ ->
             Printf.sprintf "%s(declare-const %s (Array Int Bool))\n" str
               (var_tostr var)
         | BitvTermVar _ ->
             (* Vampire doesn't support bitvectors. *)
             raise (Unsupported_Formula_Constructor 12)
         | ABitvTermVar _ ->
             (* Vampire doesn't support bitvectors. *)
             raise (Unsupported_Formula_Constructor 12))
       (free_vars form VS.empty) "")
    (to_smt_helper_vamp form)

let to_sygus constraints bool_hole_list term_hole_list =
  let f_vars =
    List.fold_left
      (fun set aconstraint -> VS.union set (free_vars aconstraint VS.empty))
      VS.empty constraints
  in
  let str1 =
    Printf.sprintf "%s\n"
      (VS.fold
         (fun var str ->
           match var with
           | BoolVar _ ->
               Printf.sprintf "%s(declare-var %s Bool)\n" str (var_tostr var)
           | IntTermVar _ ->
               Printf.sprintf "%s(declare-var %s Int)\n" str (var_tostr var)
           | BitvTermVar _ ->
               Printf.sprintf "%s(declare-var %s (_ BitVec %d))\n" str
                 (var_tostr var) Logic.Formula.bvconst
           | _ -> raise (Unsupported_Formula_Constructor 6))
         f_vars "")
  in
  (* Declare Holes to synthesize *)
  let str2 =
    Printf.sprintf "%s\n"
      (String.concat "\n"
         (List.map
            (fun (s, vl) ->
              Printf.sprintf "(synth-fun %s (%s) Bool)" s
                (String.concat " "
                   (List.map
                      (fun var ->
                        match var with
                        | BoolVar _ ->
                            Printf.sprintf "(%s Bool)" (var_tostr var)
                        | IntTermVar _ ->
                            Printf.sprintf "(%s Int)" (var_tostr var)
                        | BitvTermVar _ ->
                            Printf.sprintf "(%s (_ BitVec %d))" (var_tostr var)
                              Logic.Formula.bvconst
                        | _ -> raise (Unsupported_Formula_Constructor 7))
                      vl)))
            bool_hole_list))
  in
  let str3 =
    Printf.sprintf "%s\n"
      (String.concat "\n"
         (List.map
            (fun (s, vl) ->
              Printf.sprintf "(synth-fun %s (%s) Int)" s
                (String.concat " "
                   (List.map
                      (fun var ->
                        match var with
                        | BoolVar _ ->
                            Printf.sprintf "(%s Bool)" (var_tostr var)
                        | IntTermVar _ ->
                            Printf.sprintf "(%s Int)" (var_tostr var)
                        | BitvTermVar _ ->
                            Printf.sprintf "(%s (_ BitVec %d))" (var_tostr var)
                              Logic.Formula.bvconst
                        | _ -> raise (Unsupported_Formula_Constructor 7))
                      vl)))
            term_hole_list))
  in
  (* Write constraints. *)
  let str4 =
    Printf.sprintf "%s\n"
      (String.concat "\n"
         (List.map
            (fun aconstraint ->
              Printf.sprintf "(constraint %s)" (to_smt_helper aconstraint))
            constraints))
  in
  "(set-logic ALL)\n\n" ^ str1 ^ str2 ^ str3 ^ str4 ^ "(check-synth)"

(* Utilities for discharging implications --
   The idea will be to spawn processes to invoke Z3 or whichever solver.
   We will generate a function that collects the process and makes sure it verified correctly, returning if not.
   At the end of the proof construction, we will run these functions; if none of them error, the proof is correct.
   Otherwise, an implication is incorrect (or a check did not complete).*)

(* Reading Synthesized formulas back in*)
let parse_cvc5_func_decl definition_str =
  SMT2Parser.Parser.fun_decl SMT2Parser.Lexer.read
    (Lexing.from_string definition_str)

(* FUNCITONS FOR DISCHARGING QUERIES *)
(* Spawn a process to check the implication.
   Return a blocking function that confirms implication is valid. *)
type file_info = { name_number : int; formul : formula; truth : bool option }
type file_pair = { name_num : int; form : formula }

(* Sets up loggers and returns a function that can be used to check implication, assuming z3.
   Logging discharged implications saves on repeat computations.
   The implication function returned takes a hyp:formula and conclusion:formula and returns a bool lazy.*)
let no_hole_simple_implicator_z3 () =
  let file_logger : file_info list ref = ref [] and file_counter = ref 0 in
  (* Utilities: *)
  (* Transforms variables to avoid 2 vars w same name *)
  let rec fresh_vars_all frm vset =
    match frm with
    | And (a, b) ->
        let frma, vseta = fresh_vars_all a vset in
        let frmb, vsetb = fresh_vars_all b vseta in
        (And (frma, frmb), vsetb)
    | Or (a, b) ->
        let frma, vseta = fresh_vars_all a vset in
        let frmb, vsetb = fresh_vars_all b vseta in
        (Or (frma, frmb), vsetb)
    | Not a ->
        let frm, set = fresh_vars_all a vset in
        (Not frm, set)
    | Implies (a, b) ->
        let frma, vseta = fresh_vars_all a vset in
        let frmb, vsetb = fresh_vars_all b vseta in
        (Implies (frma, frmb), vsetb)
    | Iff (a, b) ->
        let frma, vseta = fresh_vars_all a vset in
        let frmb, vsetb = fresh_vars_all b vseta in
        (Iff (frma, frmb), vsetb)
    | Exists (v, b) ->
        if VS.mem v vset then
          let v_new =
            new_var_of_same_type v
              (fresh_var_name b (List.map var_tostr (VS.elements vset)))
          in
          let frmb, vsetb =
            fresh_vars_all (subs b v (var_to_exp v_new)) (VS.add v_new vset)
          in
          (Exists (v_new, frmb), vsetb)
        else
          let frmb, vsetb = fresh_vars_all b (VS.add v vset) in
          (Exists (v, frmb), vsetb)
    | Forall (v, b) ->
        if VS.mem v vset then
          let v_new =
            new_var_of_same_type v
              (fresh_var_name b (List.map var_tostr (VS.elements vset)))
          in
          let frmb, vsetb =
            fresh_vars_all (subs b v (var_to_exp v_new)) (VS.add v_new vset)
          in
          (Forall (v_new, frmb), vsetb)
        else
          let frmb, vsetb = fresh_vars_all b (VS.add v vset) in
          (Forall (v, frmb), vsetb)
    | _ -> (frm, vset)
  in
  let rec new_holer frm =
    match frm with
    | And (a, b) -> VS.union (new_holer a) (new_holer b)
    | Or (a, b) -> VS.union (new_holer a) (new_holer b)
    | Not a -> new_holer a
    | Implies (a, b) -> VS.union (new_holer a) (new_holer b)
    | Iff (a, b) -> VS.union (new_holer a) (new_holer b)
    | Exists (v, b) -> VS.add v (new_holer b)
    | Forall (_, b) -> new_holer b
    | _ -> VS.empty
  in
  let rec strip_exists frm =
    match frm with
    | And (a, b) -> And (strip_exists a, strip_exists b)
    | Or (a, b) -> Or (strip_exists a, strip_exists b)
    | Not a -> Not (strip_exists a)
    | Implies (a, b) -> Implies (strip_exists a, strip_exists b)
    | Iff (a, b) -> Iff (strip_exists a, strip_exists b)
    | Exists (_, b) -> strip_exists b
    | Forall (v, b) -> Forall (v, strip_exists b)
    | _ -> frm
  in
  (* Converts a formula by replacing existentially quantified variables with function applications/holes that take in important vars.
     Returns new formula and holes. *)
  let backup_syguser form important_variables =
    let form = fst (fresh_vars_all form (free_vars form VS.empty)) in
    let important_vars = VS.elements important_variables in
    let important_vars_as_exps =
      List.map var_to_exp (VS.elements important_variables)
    in
    let new_holes =
      List.map
        (fun hole_var ->
          match hole_var with
          | IntTermVar _ ->
              ( hole_var,
                Term
                  (ITerm (THole (var_tostr hole_var, important_vars_as_exps)))
              )
          | AIntTermVar _ ->
              ( hole_var,
                Term
                  (ITerm (THole (var_tostr hole_var, important_vars_as_exps)))
              )
          | BitvTermVar _ -> 
              ( hole_var,
                Term
                  (BitvTerm (BitvTHole (var_tostr hole_var, important_vars_as_exps)))
              )
          | ABitvTermVar _ ->
              ( hole_var,
                Term
                  (BitvTerm (BitvTHole (var_tostr hole_var, important_vars_as_exps)))
              )
          | BoolVar _ ->
              ( hole_var,
                Boolean (BHole (var_tostr hole_var, important_vars_as_exps)) )
          | ABoolVar _ ->
              ( hole_var,
                Boolean (BHole (var_tostr hole_var, important_vars_as_exps)) ))
        (VS.elements (new_holer form))
    in
    ( List.fold_left
        (fun frm (hole_var, hole) -> subs frm hole_var hole)
        (strip_exists form) new_holes,
      List.map (fun (a, _) -> (var_tostr a, important_vars)) new_holes )
  in
  (* Note important_variables is a set of variables.
     If the smt query fails, we try a sygus query where existentially quantified variables are functions over the important variables.*)
  let no_hole_verify form important_variables =
    (* Write SMT2 File *)
    (* If the file named by our fresh counter exists, skip the number. It could be important to someone else. *)
    while
      Sys.file_exists (Printf.sprintf "Implication%d.smt" !file_counter)
      || Sys.file_exists (Printf.sprintf "Implication%d.sy" !file_counter)
    do
      file_counter := !file_counter + 1
    done;
    (* If we have not dispatched a query for this implication... *)
    if not (List.mem form (List.map (fun a -> a.formul) !file_logger)) then (
      let filename_pref = Printf.sprintf "Implication%d" !file_counter in
      (* Set up the file and record in the structure. *)
      let oc = open_out (Printf.sprintf "%s.smt" filename_pref) in
      Printf.fprintf oc "%s" (to_negated_smt_z3 form "test");
      close_out oc;
      file_logger :=
        List.cons
          { name_number = !file_counter; formul = form; truth = None }
          !file_logger;
      file_counter := !file_counter + 1;
      (* Fork and exec a z3 query *)
      let kid_pid = Unix.fork () in
      if kid_pid = 0 then (
        let fd =
          Unix.openfile
            (Printf.sprintf "%s.out" filename_pref)
            [ O_CREAT; O_WRONLY ] 0
        in
        Unix.dup2 fd Unix.stdout;
        Unix.execvp "z3alpha"
          (Array.of_list
             [ "z3alpha"; "-smt2"; Printf.sprintf "%s.smt" filename_pref ])
        (* Unix.execvp "cvc5"
           (Array.of_list
              [ "cvc5"; "-L"; "smt2.6"; "--no-incremental"; "--no-type-checking"; "--no-interactive"; Printf.sprintf "%s.smt" filename_pref ])) *))
      else if
        (* If it makes sense to do so (i.e., there are existentially quantified variables and we have some variables we think they are functions of), discharge a backup sygus query as well. *)
        has_exists form && not (VS.is_empty important_variables)
      then (
        (* Set up the file and record in the structure. *)
        let oc = open_out (Printf.sprintf "%s.sy" filename_pref) in
        let constraint_one, holes = backup_syguser form important_variables in
        Printf.fprintf oc "%s" (to_sygus [ constraint_one ] [] holes);
        close_out oc;
        file_counter := !file_counter + 1;
        (* Fork and exec the backup sygus query. *)
        let kid_pid2 = Unix.fork () in
        if kid_pid2 = 0 then (
          let fd =
            Unix.openfile
              (Printf.sprintf "%s.sy.out" filename_pref)
              [ O_CREAT; O_WRONLY ] 0
          in
          Unix.dup2 fd Unix.stdout;
          Unix.execvp "cvc5"
            (Array.of_list [ "cvc5"; Printf.sprintf "%s.sy" filename_pref ]))
        else
          lazy
            ((* This is truly bad, but idk how to wait on either process to finish.
                Internet seems to not know either. *)
             let i = ref 1
             and out = ref false in
             while !i < 2 do
               let a = ref (0, Unix.WEXITED 0)
               and b = ref (0, Unix.WEXITED 0) in
               while
                 a := Unix.waitpid [ Unix.WNOHANG ] kid_pid;
                 b := Unix.waitpid [ Unix.WNOHANG ] kid_pid2;
                 fst !a = 0 && fst !b = 0
               do
                 Unix.sleep 1
               done;
               if fst !a = kid_pid && snd !a <> Unix.WEXITED 0 then (
                 i := !i + 1;
                 a := (0, Unix.WEXITED 0))
               else ();
               if fst !b = kid_pid2 && snd !b <> Unix.WEXITED 0 then (
                 i := !i + 1;
                 b := (0, Unix.WEXITED 0))
               else ();
               if fst !a = kid_pid && fst !b = kid_pid2 then
                 let result =
                   In_channel.input_line
                     (open_in (Printf.sprintf "%s.out" filename_pref))
                 in
                 if result = Some "unsat" then (
                   i := 2;
                   out := true)
                 else if result = Some "sat" then i := 2
                 else
                   let result =
                     In_channel.input_line
                       (open_in (Printf.sprintf "%s.sy.out" filename_pref))
                   in
                   if result = Some "(" then (
                     i := 2;
                     out := true)
                   else i := 2
               else if fst !a = kid_pid then
                 let result =
                   In_channel.input_line
                     (open_in (Printf.sprintf "%s.out" filename_pref))
                 in
                 if result = Some "unsat" then (
                   i := 2;
                   out := true)
                 else if result = Some "sat" then i := 2
                 else i := !i + 1
               else if fst !b = kid_pid2 then
                 let result =
                   In_channel.input_line
                     (open_in (Printf.sprintf "%s.sy.out" filename_pref))
                 in
                 if result = Some "(" then (
                   i := 2;
                   out := true)
                 else if result = Some "infeasible" then i := !i + 1
                 else i := !i + 1
               else i := 2
             done;
             file_logger :=
               List.map
                 (fun finfo ->
                   if finfo.formul = form then
                     {
                       name_number = finfo.name_number;
                       formul = form;
                       truth = Some !out;
                     }
                   else finfo)
                 !file_logger;
             !out)
        (* Return function that collects SMT result *))
      else
        lazy
          (if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then false
           else
             let result =
               In_channel.input_line
                 (open_in (Printf.sprintf "%s.out" filename_pref))
             in
             file_logger :=
               List.map
                 (fun finfo ->
                   if finfo.formul = form then
                     {
                       name_number = finfo.name_number;
                       formul = form;
                       truth = Some (result = Some "unsat");
                     }
                   else finfo)
                 !file_logger;
             result = Some "unsat")
      (* TODO: It might be good to have the below behavior be the default in both branches, but waitpid might be better. *)
      (* If the query was already run, just read the result. *))
    else
      lazy
        (while
           not
             (List.exists
                (fun a -> a.formul = form && a.truth != None)
                !file_logger)
         do
           Unix.sleep 1
         done;
         match (List.find (fun a -> a.formul = form) !file_logger).truth with
         | None -> false
         | Some s -> s)
  in
  no_hole_verify

(* Sets up loggers and returns a function that can be used to check implication and a lazy with synthesized solutions to holes.
   Logging discharged implications saves on repeat computations and consolidates synthesis constraints.
   Such an implication checking function must take a hyp:Formula and conclusion:Formula and return a bool lazy.
   TODO: Evaluating the synthesized holes breaks the environment; we may want to fix that so we can build gradual proofs? Or something?*)
let implicator_hole_synth_cvc5 () =
  (* Create persistent context to track synthesis constraints. *)
  let constraint_logger = ref []
  (* and varset = ref VS.empty *)
  and (synth_mapper : ((string * variable list) * formula) list option ref) =
    ref None
  and file_counter = ref 0
  and has_solutions = ref None
  and no_hole_verif = no_hole_simple_implicator_z3 () in
  let synthesize_hole_values =
    lazy
      (match !synth_mapper with
      | Some s -> s
      | None ->
          (* Find distinct holes and rename vars (to write synth-invs later). Also set the synth-mapper.*)
          let varset =
            ref
              (List.fold_left
                 (fun set form -> VS.union set (free_vars form VS.empty))
                 VS.empty !constraint_logger)
          in
          let constraints =
            List.flatten
              (List.map
                 (fun form ->
                   let forms, new_varset = deconjunctivizer_rhs form !varset in
                   varset := new_varset;
                   List.map (fun (form, _) -> form) forms)
                 !constraint_logger)
          in
          constraint_logger := constraints;
          let hole_list =
            List.fold_left
              (fun list (name, vl) ->
                if List.exists (fun (s, _) -> String.equal name s) list then
                  list
                else List.cons (name, vl) list)
              []
              (List.flatten
                 (List.map
                    (fun aconstraint -> get_bholes aconstraint)
                    !constraint_logger))
          in
          let i = ref 0 in
          let hole_list =
            List.map
              (fun (s, vl) ->
                ( s,
                  List.map
                    (fun v ->
                      match v with
                      | Term (ITerm _) ->
                          i := !i + 1;
                          IntTermVar (T (Printf.sprintf "a_%d" !i))
                      | Term (BitvTerm _) ->
                          i := !i + 1;
                          BitvTermVar (T (Printf.sprintf "a_%d" !i))
                      | Boolean _ ->
                          i := !i + 1;
                          BoolVar (B (Printf.sprintf "a_%d" !i)))
                    vl ))
              hole_list
          in
          (* Assemble .sy file *)
          (* Make file *)
          while
            Sys.file_exists (Printf.sprintf "Synthesis%d.sy" !file_counter)
          do
            file_counter := !file_counter + 1
          done;
          let filename_pref = Printf.sprintf "Synthesis%d" !file_counter in
          (* Set up the file. *)
          let oc = open_out (Printf.sprintf "%s.sy" filename_pref) in
          Printf.fprintf oc "%s" (to_sygus !constraint_logger hole_list []);
          close_out oc;
          (* Dispatch synthesis to solver *)
          (* Fork and exec a query *)
          let kid_pid = Unix.fork () in
          if kid_pid = 0 then (
            (* Run synthesis via cvc5 *)
            let fd =
              Unix.openfile
                (Printf.sprintf "%s.out" filename_pref)
                [ O_CREAT; O_WRONLY ] 0
            in
            Unix.dup2 fd Unix.stdout;
            Unix.execvp "cvc5"
              (Array.of_list [ "cvc5"; Printf.sprintf "%s.sy" filename_pref ])
            (* Wait. If can't synth, then record no solutions.
                Else, record existenct of a solution, store solution, and return it as string (for now).
                TODO: Parse string so a mapping is returned instead; the contents of the mapping can be subbed intop the proof. *))
          else if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then (
            has_solutions := Some false;
            [])
          else
            let output = Arg.read_arg (Printf.sprintf "%s.out" filename_pref) in
            has_solutions := Some (Array.get output 0 = "(");
            if Array.get output 0 = "(" then (
              let syn_list =
                List.map
                  (fun (name, body) ->
                    (List.find (fun (h, _) -> h = name) hole_list, body))
                  (List.map
                     (fun decl_str ->
                       parse_cvc5_func_decl decl_str)
                     (Array.to_list
                        (Array.sub output 1 (Array.length output - 2))))
              in
              synth_mapper := Some syn_list;
              syn_list)
            else [])
  in

  let verify form =
    (* If there are no boolean holes (i.e., invariants/summaries), discharge separately. *)
    if not (has_bholes form) then no_hole_verif form VS.empty
    else (
      (* If holes are present, add the constraints to our constraint list.
         We will wait to deconjunctivize until we know all free variables involved (i.e., until the query is discharged).
         Otherwise, we may shoot ourselves in the foot by overshadowing a free variable in a later constraint.*)
      constraint_logger := List.cons form !constraint_logger;
      lazy
        (match !has_solutions with
        | None -> (
            ignore (Lazy.force synthesize_hole_values);
            match !has_solutions with None -> false | Some s -> s)
        | Some s -> s))
  in

  (verify, synthesize_hole_values)

(* Sets up loggers and returns a function that can be used to check implication, assuming vampire.
   Logging discharged implications saves on repeat computations.
   The implication function returned takes a hyp:formula and conclusion:formula and returns a bool lazy.*)
let no_hole_vector_state_implicator_vampire () =
  let file_logger = ref [] and file_counter = ref 0 in
  let no_hole_verify form =
    (* Write SMT2 File *)
    (* If the file named by our fresh counter exists, skip the number. It could be important to someone else. *)
    while Sys.file_exists (Printf.sprintf "Implication%d.smt" !file_counter) do
      file_counter := !file_counter + 1
    done;
    (* If we have not dispatched a query for this implication... *)
    if not (List.mem form (List.map (fun a -> a.form) !file_logger)) then (
      let filename_pref = Printf.sprintf "Implication%d" !file_counter in
      (* Set up the file and record in the structure. *)
      let oc = open_out (Printf.sprintf "%s.smt" filename_pref) in
      Printf.fprintf oc "%s" (to_negated_smt_vampire form "test");
      close_out oc;
      file_logger := List.cons { name_num = !file_counter; form } !file_logger;
      file_counter := !file_counter;
      (* Fork and exec a query *)
      let kid_pid = Unix.fork () in
      if kid_pid = 0 then (
        let fd =
          Unix.openfile
            (Printf.sprintf "%s.out" filename_pref)
            [ O_CREAT; O_WRONLY ] 0
        in
        Unix.dup2 fd Unix.stdout;
        Unix.execvp "vampire"
          (Array.of_list
             [
               "vampire";
               "-om";
               "smtcomp";
               "--input_syntax";
               "smtlib2";
               Printf.sprintf "%s.smt" filename_pref;
             ]))
      else
        (* Return function that collects SMT result *)
        lazy
          (if Unix.waitpid [] kid_pid <> (kid_pid, WEXITED 0) then false
           else
             let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
             input_line f_channel = "unsat")
      (* TODO: It might be good to have the below behavior be the default in both branches, but waitpid might be better. *)
      (* If the query was already run, just read the result. *))
    else
      let name_num =
        (List.find (fun a -> a.form = form) !file_logger).name_num
      in
      let filename_pref = Printf.sprintf "Implication%d" name_num in
      lazy
        (while not (Sys.file_exists (Printf.sprintf "%s.out" filename_pref)) do
           Unix.sleep 1
         done;
         let f_channel = open_in (Printf.sprintf "%s.out" filename_pref) in
         input_line f_channel = "unsat")
  in
  no_hole_verify

(* IMPLICATION MODULES *)
module NoHoleSimpleImplicatorZ3 () : ImplicationHandler = struct
  let base_verif = no_hole_simple_implicator_z3 ()

  let implies pre post =
    List.fold_left
      (fun lazy_boolean (form, existed) ->
        lazy (Lazy.force lazy_boolean && Lazy.force (base_verif form existed)))
      (lazy true)
      (deconjunctivizer pre post)

  let hole_values = lazy []
end

module HoleSynthSimpleImplicatorCVC5 () : ImplicationHandler = struct
  let base_verif, hole_values = implicator_hole_synth_cvc5 ()
  let implies pre post = base_verif (Implies (pre, post))
  (* Deconjuncting for cvc5 takes place inside base_verif *)
end

module NoHoleVectorStateImplicatorVampire () : ImplicationHandler = struct
  let base_verif = no_hole_vector_state_implicator_vampire ()

  let implies pre post =
    List.fold_left
      (fun lazy_boolean (form, _) ->
        lazy (Lazy.force lazy_boolean && Lazy.force (base_verif form)))
      (lazy true)
      (deconjunctivizer pre post)

  let hole_values = lazy []
end

(* Functions to transform formulas over many indices to formulas over only a few indices when vector length is bounded. *)
(* let indexer var_name index = Printf.sprintf "%s_finitevscpy_%d" var_name index

   let rec int_term_finite_vs_transformer int_term =
     match int_term with
     | AITVar (ITApp (ET, Int i)) -> ITVar (T (indexer "e_t" i))
     | AITVar (ITApp (T v, Int i)) -> ITVar (T (indexer v i))
     | Minus t -> Minus (int_term_finite_vs_transformer t)
     | Plus (t1, t2) ->
         Plus (int_term_finite_vs_transformer t1, int_term_finite_vs_transformer t2)
     | Times (t1, t2) ->
         Times
           (int_term_finite_vs_transformer t1, int_term_finite_vs_transformer t2)
     | _ -> int_term

   let rec bitv_term_finite_vs_transformer bitv_term =
     match bitv_term with
     | Bitv _ -> bitv_term
     | BitvTVar _ -> bitv_term
     | ABitvTVar (BitvTUnApp _) -> raise (Unsupported_Formula_Constructor 26)
     | BitvUnarApp (op, btv) ->
         BitvUnarApp (op, bitv_term_finite_vs_transformer btv)
     | BitvBinarApp (op, btv1, btv2) ->
         BitvBinarApp
           ( op,
             bitv_term_finite_vs_transformer btv1,
             bitv_term_finite_vs_transformer btv2 )
     | ABitvTVar (BitvTApp (ET, Int i)) -> BitvTVar (T (indexer "e_t" i))
     | ABitvTVar (BitvTApp (T v, Int i)) -> BitvTVar (T (indexer v i))
     | _ -> bitv_term

   let term_finite_vs_transformer term =
     match term with
     | ITerm it -> ITerm (int_term_finite_vs_transformer it)
     | BitvTerm bitv -> BitvTerm (bitv_term_finite_vs_transformer bitv)

   let rec bool_finite_vs_transformer max_ind form =
     match form with
     | ABVar (BApp (BT, Int i)) -> BVar (B (indexer "b_t" i))
     | ABVar (BApp (B v, Int i)) -> BVar (B (indexer v i))
     | And (f1, f2) ->
         And
           ( bool_finite_vs_transformer max_ind f1,
             bool_finite_vs_transformer max_ind f2 )
     | Or (f1, f2) ->
         Or
           ( bool_finite_vs_transformer max_ind f1,
             bool_finite_vs_transformer max_ind f2 )
     | Not f -> Not (bool_finite_vs_transformer max_ind f)
     | Implies (f1, f2) ->
         Implies
           ( bool_finite_vs_transformer max_ind f1,
             bool_finite_vs_transformer max_ind f2 )
     | Equals (t1, t2) ->
         Equals (term_finite_vs_transformer t1, term_finite_vs_transformer t2)
     | Less (t1, t2) ->
         Less (term_finite_vs_transformer t1, term_finite_vs_transformer t2)
     | Iff (f1, f2) ->
         Iff
           ( bool_finite_vs_transformer max_ind f1,
             bool_finite_vs_transformer max_ind f2 )
     | Exists (v, f) -> (
         match v with
         | IntTermVar _ -> Exists (v, bool_finite_vs_transformer max_ind f)
         | BoolVar _ -> Exists (v, bool_finite_vs_transformer max_ind f)
         | AIntTermVar (T t) ->
             List.fold_left
               (fun form i -> Exists (IntTermVar (T (indexer t i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | ABitvTermVar (T t) ->
             List.fold_left
               (fun form i -> Exists (BitvTermVar (T (indexer t i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | ABoolVar (B b) ->
             List.fold_left
               (fun form i -> Exists (BoolVar (B (indexer b i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | _ -> raise (Unsupported_Formula_Constructor 8))
     | Forall (v, f) -> (
         match v with
         | IntTermVar _ -> Forall (v, bool_finite_vs_transformer max_ind f)
         | BoolVar _ -> Forall (v, bool_finite_vs_transformer max_ind f)
         | AIntTermVar (T t) ->
             List.fold_left
               (fun form i -> Forall (IntTermVar (T (indexer t i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | ABitvTermVar (T t) ->
             List.fold_left
               (fun form i -> Forall (BitvTermVar (T (indexer t i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | ABoolVar (B b) ->
             List.fold_left
               (fun form i -> Forall (BoolVar (B (indexer b i)), form))
               (bool_finite_vs_transformer max_ind f)
               (List.init max_ind (fun n -> n + 1))
         | _ -> raise (Unsupported_Formula_Constructor 9))
     | BHole (h, arg_list) ->
         print_endline (form_tostr form);
         let big_args_list =
           List.concat
             (List.init max_ind (fun n ->
                  List.map
                    (fun exp ->
                      exp_finite_vs_transformer max_ind
                        (set_exp_index exp (Int (n + 1))))
                    arg_list))
         in
         print_endline (form_tostr (BHole (h, big_args_list)));
         BHole (h, big_args_list)
     | T (f, b_loop, vmaps) ->
         (* A list of (positive variables, formulas) for all 2^n combinations of bt[i] for the indices i appearing in t. If no indices appear, then it's just True.
            E.g., [([1, 2], bloop[1] && bloop[2]], ([1], bloop[1] && !bloop[2]), ([2], !bloop[1] && bloop[2]), ([], !bloop[1] && !bloop[2])] *)
         let t_guards =
           List.fold_left
             (fun partial_perms_list index ->
               List.append
                 (List.map
                    (fun (pos_list, conj) ->
                      (pos_list, And (Not (ABVar (BApp (b_loop, Int index))), conj)))
                    partial_perms_list)
                 (List.map
                    (fun (pos_list, conj) ->
                      ( List.cons index pos_list,
                        And (ABVar (BApp (b_loop, Int index)), conj) ))
                    partial_perms_list))
             [ ([], True) ]
             (List.init max_ind (fun n -> n + 1))
         in
         let expanded_hole = bool_finite_vs_transformer max_ind f in
         let implied_subbed_holes =
           List.map
             (fun (off_inds, prec) ->
               Implies
                 ( bool_finite_vs_transformer max_ind prec,
                   List.fold_left
                     (fun hole ind ->
                       List.fold_left
                         (fun hole (oldv, newv) ->
                           subs hole
                             (IntTermVar
                                (T (indexer (var_tostr (AIntTermVar oldv)) ind)))
                             (Term
                                (ITerm
                                   (ITVar
                                      (T
                                         (indexer
                                            (var_tostr (AIntTermVar newv))
                                            ind))))))
                         (List.fold_left
                            (fun hole (oldv, newv) ->
                              subs hole
                                (BitvTermVar (T (indexer (var_tostr (ABitvTermVar oldv)) ind)))
                                (Term (BitvTerm
                                   (BitvTVar (T (indexer (var_tostr (ABitvTermVar newv)) ind))))))
                            hole (VMap_ABitvT.bindings vmaps.bitv_map))
                         (VMap_AIT.bindings vmaps.int_map))
                     expanded_hole off_inds ))
             t_guards
         in
         let conjoined_holes =
           List.fold_left
             (fun form hole -> And (form, hole))
             True implied_subbed_holes
         in
         (* In the finite case, we don't reason about infinite vectors so we can expand explicitly.
            We perform an across-the-board conversion of holes over vector states to holes over the entries.
            This is a bit of a hack to use all the infinite vs machinery and change it at the very end, but let's not worry about that. *)
         conjoined_holes
     | TPrime f -> TPrime (bool_finite_vs_transformer max_ind f)
     | _ -> form

   and exp_finite_vs_transformer max_ind exp =
     match exp with
     | Term t -> Term (term_finite_vs_transformer t)
     | Boolean b -> Boolean (bool_finite_vs_transformer max_ind b) *)

let finite_holeless_implicator max_ind =
  (module struct
    let base_verif = no_hole_simple_implicator_z3 ()

    let implies pre post =
      List.fold_left
        (fun lazy_boolean (form, existed) ->
          lazy (Lazy.force lazy_boolean && Lazy.force (base_verif form existed)))
        (lazy true)
        (deconjunctivizer
           (bool_finite_vs_transformer max_ind pre)
           (bool_finite_vs_transformer max_ind post))

    let hole_values = lazy []
  end : ImplicationHandler)

let finite_holes_implicator max_ind =
  (module struct
    let base_verif, hole_values = implicator_hole_synth_cvc5 ()

    let implies pre post =
      base_verif
        (Implies
           ( bool_finite_vs_transformer max_ind pre,
             bool_finite_vs_transformer max_ind post ))
    (* First, load constraints. *)
    (* let lst =
         List.map (fun form -> base_verif form) (deconjunctivizer (bool_finite_vs_transformer max_ind pre)(
         bool_finite_vs_transformer max_ind post ))
       in
       (* Second, discharge them. *)
       lazy (List.fold_left (fun lzb1 lzb2 -> lzb1 && Lazy.force lzb2) true lst) *)
  end : ImplicationHandler)
