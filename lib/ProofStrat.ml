open Logic.Formula
open Logic.Variable
open Programs.Program
open Programs.NonTerminal
open Proofrules.ProofRule

exception Bad_Strongest_Triple of string * string
exception Unsupported_Var
exception Unsupported_Mode

type synthMode = HOLE_SYNTH | INVS_SPECIFIED
type formMode = SIMPLE | FINITE_VECTOR_STATE | VECTOR_STATE
type holeGuideMode = NONE | BITVEC
type vcSimplificationMode = NO_SIMP | QUANTIFY_COLLECT

(* Handles building proofs for the 3 types of non-terminals polymorphically.
   Reassigned_var_finder finds the reassigned vars from a given program; taking this as input lets us support simple and vector-state behaviors.
   If finite_vectors=0, vectors are treated as inifinte. Otherwise, they are treated as having length finite_vectors.*)

let nonterm_handler_template expansion_to_prog nterm_to_prog
    (vector_state : bool) nterm ctrip (finite_vectors : int)
    (build_wpc_proof :
      contextualized_triple_no_pre ->
      (formula -> formula -> bool Lazy.t) ->
      ruleApp) implies =
  let trip = ctrip.trip in
  match strongest nterm with
  | None ->
      (* If non-recursive, apply GrmDisj *)
      (* Build a list of hypotheses *)
      let hypotheses =
        List.fold_right
          (fun expansion pflist ->
            List.cons
              (build_wpc_proof
                 {
                   context = ctrip.context;
                   trip =
                     { prog = expansion_to_prog expansion; post = trip.post };
                 }
                 implies)
              pflist)
          (Programs.NonTerminal.expand nterm)
          []
      in
      (* Assemble the grmdisj proof *)
      GrmDisj
        ( {
            context = ctrip.context;
            trip =
              {
                pre =
                  List.fold_left
                    (fun form hypothesis ->
                      (* "T \land" Could be better *)
                      Logic.Formula.And
                        (form, (get_conclusion hypothesis).trip.pre))
                    True hypotheses;
                prog = trip.prog;
                post = trip.post;
              };
          },
          hypotheses )
  (* If the non-terminal is recursive, apply Adapt, then try ApplyHP if the strongest formula is in the context; else, Weaken to x=z (ghost_pre) and apply HP. *)
  | Some (var_pairs_list, postc) ->
      (* First, we need to fix the hole *)
      (* let postc = if finite_vectors = 0 then postc else (Implications.bool_finite_vs_transformer finite_vectors postc) in *)
      (* First, make sure the proposed x covers all program variables whose values can change in the body.
          TODO: Move this check to intake of non-terminal at some point. *)
      (* VS.iter
         (fun var ->
           if
             List.mem (var_tostr var)
               (List.map (fun (a, _) -> var_tostr a) var_pairs_list)
           then ()
           else
             raise
               (Bad_Strongest_Triple
                  ( prog_tostr trip.prog,
                    Printf.sprintf "[%s]"
                      (String.concat "; "
                         (List.map
                            (fun (a, b) ->
                              Printf.sprintf "(%s, %s)" (var_tostr a)
                                (var_tostr b))
                            var_pairs_list)) )))
         (reassigned_var_finder trip.prog); *)
      (*Write x=z. *)
      let ghost_pre =
        List.fold_left
          (fun form (prog_var, ghost_var) ->
            match (prog_var, ghost_var) with
            | IntTermVar p, IntTermVar g ->
                Logic.Formula.And
                  (form, Equals (ITerm (ITVar p), ITerm (ITVar g)))
            | BitvTermVar p, BitvTermVar g ->
                Logic.Formula.And
                  (form, Equals (BitvTerm (BitvTVar p), BitvTerm (BitvTVar g)))
            | BoolVar p, BoolVar g ->
                Logic.Formula.And (form, Iff (BVar p, BVar g))
            | ABoolVar p, ABoolVar g ->
                Logic.Formula.And
                  ( form,
                    if finite_vectors != 0 then
                      List.fold_left
                        (fun form index ->
                          Logic.Formula.And
                            ( form,
                              Iff
                                ( ABVar (BApp (p, Int index)),
                                  ABVar (BApp (g, Int index)) ) ))
                        True
                        (List.init finite_vectors (fun x -> x + 1))
                    else
                      Forall
                        ( IntTermVar (T "i"),
                          Iff
                            ( ABVar (BApp (p, ITVar (T "i"))),
                              ABVar (BApp (g, ITVar (T "i"))) ) ) )
            | AIntTermVar p, AIntTermVar g ->
                Logic.Formula.And
                  ( form,
                    if finite_vectors != 0 then
                      List.fold_left
                        (fun form index ->
                          Logic.Formula.And
                            ( form,
                              Equals
                                ( ITerm (AITVar (ITApp (p, Int index))),
                                  ITerm (AITVar (ITApp (g, Int index))) ) ))
                        True
                        (List.init finite_vectors (fun x -> x + 1))
                    else
                      Forall
                        ( IntTermVar (T "i"),
                          Equals
                            ( ITerm (AITVar (ITApp (p, ITVar (T "i")))),
                              ITerm (AITVar (ITApp (g, ITVar (T "i")))) ) ) )
            | ABitvTermVar p, ABitvTermVar g ->
                Logic.Formula.And
                  ( form,
                    if finite_vectors != 0 then
                      List.fold_left
                        (fun form index ->
                          Logic.Formula.And
                            ( form,
                              Equals
                                ( BitvTerm (ABitvTVar (BitvTApp (p, Int index))),
                                  BitvTerm (ABitvTVar (BitvTApp (g, Int index)))
                                ) ))
                        True
                        (List.init finite_vectors (fun x -> x + 1))
                    else
                      Forall
                        ( IntTermVar (T "i"),
                          Equals
                            ( BitvTerm (ABitvTVar (BitvTApp (p, ITVar (T "i")))),
                              BitvTerm (ABitvTVar (BitvTApp (g, ITVar (T "i"))))
                            ) ) )
            | _ -> raise (Bad_Strongest_Triple (prog_tostr trip.prog, "")))
          True var_pairs_list
      in
      (* Write the adapt precondition \forall y. Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      (* Q_0[y/x] *)
      (* Generation of y is also dependent on Q to avoid capture *)
      (* This first step handles e_t and b_t which may not appear in var_pairs_list.
         Admittedly, it is messy. *)
      let var_pairs_list =
        List.append var_pairs_list
          (List.map
             (fun x ->
               match x with
               | IntTermVar y ->
                   if not vector_state then
                     ( x,
                       IntTermVar
                         (T
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
                   else
                     ( (match y with
                       | ET -> AIntTermVar ET
                       | T v -> AIntTermVar (T v)),
                       AIntTermVar
                         (T
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
               | BitvTermVar y ->
                   if not vector_state then
                     ( x,
                       BitvTermVar
                         (T
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
                   else
                     ( (match y with
                       | ET -> ABitvTermVar ET
                       | T v -> ABitvTermVar (T v)),
                       BitvTermVar
                         (T
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
               | BoolVar y ->
                   if not vector_state then
                     ( x,
                       BoolVar
                         (B
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
                   else
                     ( (match y with BT -> ABoolVar BT | B v -> ABoolVar (B v)),
                       ABoolVar
                         (B
                            "unusedconstanITVarthatshouldbereplacedbysomtehingrobustwhenpossible")
                     )
               | _ -> raise Unsupported_Var)
             (List.filter
                (fun var ->
                  List.for_all
                    (fun (a, _) -> var_tostr a <> var_tostr var)
                    var_pairs_list)
                (VS.elements (reassigned_vars (nterm_to_prog nterm)))))
      in
      let adapted_pre_1, xyz_list =
        List.fold_left
          (fun (form, xyz_list) (prog_var, ghost_var) ->
            let y =
              fresh_var_name
                (And (form, trip.post))
                (List.map (fun (_, y, _) -> var_tostr y) xyz_list)
            in
            match prog_var with
            | IntTermVar _ ->
                ( subs form prog_var (Term (ITerm (ITVar (T y)))),
                  List.cons (prog_var, IntTermVar (T y), ghost_var) xyz_list )
            | BitvTermVar _ ->
                ( subs form prog_var (Term (BitvTerm (BitvTVar (T y)))),
                  List.cons (prog_var, BitvTermVar (T y), ghost_var) xyz_list )
            | BoolVar _ ->
                ( subs form prog_var (Boolean (BVar (B y))),
                  List.cons (prog_var, BoolVar (B y), ghost_var) xyz_list )
            | ABoolVar _ ->
                ( subs form prog_var (Boolean (ABVar (BUnApp (B y)))),
                  List.cons (prog_var, ABoolVar (B y), ghost_var) xyz_list )
            | AIntTermVar _ ->
                ( subs form prog_var (Term (ITerm (AITVar (ITUnApp (T y))))),
                  List.cons (prog_var, AIntTermVar (T y), ghost_var) xyz_list )
            | ABitvTermVar _ ->
                ( subs form prog_var
                    (Term (BitvTerm (ABitvTVar (BitvTUnApp (T y))))),
                  List.cons (prog_var, ABitvTermVar (T y), ghost_var) xyz_list
                ))
          (postc, []) var_pairs_list
      in
      (* List.iter
           (fun (x, y, z) ->
             print_endline
               (Printf.sprintf "%s - %s - %s" (var_tostr x) (var_tostr y)
                  (var_tostr z)))
           xyz_list;
         print_endline (form_tostr adapted_pre_1); *)
      (* Q_0[y/x][x/z] *)
      let adapted_pre_2 =
        List.fold_left
          (fun form (x, _, z) ->
            match x with
            | IntTermVar x -> subs form z (Term (ITerm (ITVar x)))
            | BitvTermVar x -> subs form z (Term (BitvTerm (BitvTVar x)))
            | BoolVar x -> subs form z (Boolean (BVar x))
            | AIntTermVar x -> subs form z (Term (ITerm (AITVar (ITUnApp x))))
            | ABoolVar x -> subs form z (Boolean (ABVar (BUnApp x)))
            | ABitvTermVar x ->
                subs form z (Term (BitvTerm (ABitvTVar (BitvTUnApp x)))))
          adapted_pre_1 xyz_list
      in
      (* Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      let adapted_pre_3 =
        Implies
          ( adapted_pre_2,
            List.fold_left
              (fun form (x, y, _) ->
                match y with
                | IntTermVar yv -> subs form x (Term (ITerm (ITVar yv)))
                | BitvTermVar yv -> subs form x (Term (BitvTerm (BitvTVar yv)))
                | BoolVar yv -> subs form x (Boolean (BVar yv))
                | AIntTermVar yv ->
                    subs form x (Term (ITerm (AITVar (ITUnApp yv))))
                | ABitvTermVar yv ->
                    subs form x (Term (BitvTerm (ABitvTVar (BitvTUnApp yv))))
                | ABoolVar yv -> subs form x (Boolean (ABVar (BUnApp yv))))
              trip.post xyz_list )
      in
      (* \forall y. Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      let adapted_pre =
        List.fold_left
          (fun form (_, y, _) -> forall y form)
          adapted_pre_3 xyz_list
      in
      let the_proof_before_adapt =
        (* If the strongest triple and is in context, ApplyHP.*)
        if
          List.mem
            { pre = ghost_pre; prog = trip.prog; post = postc }
            ctrip.context
        then
          ApplyHP
            {
              context = ctrip.context;
              trip = { pre = ghost_pre; prog = trip.prog; post = postc };
            }
          (* Else, to apply rule of adaptation -- adapt to conclusion, add strongest to context then apply GrmDisj.
              In other words Adapt... -> [x=z, Q_0] -Weaken-> [?, Q_0] -HP-> stuff *)
        else
          let bigger_context =
            List.cons
              { pre = ghost_pre; prog = trip.prog; post = postc }
              ctrip.context
          in
          let hp_proofs =
            List.map
              (fun expansion ->
                build_wpc_proof
                  {
                    context = bigger_context;
                    trip = { prog = expansion_to_prog expansion; post = postc };
                  }
                  implies)
              (Programs.NonTerminal.expand nterm)
          in
          (* TODO - Improve T \land ... *)
          let hp =
            HP
              ( {
                  context = ctrip.context;
                  trip =
                    {
                      pre =
                        List.fold_left
                          (fun form pf ->
                            Logic.Formula.And
                              (form, (get_conclusion pf).trip.pre))
                          True hp_proofs;
                      prog = trip.prog;
                      post = postc;
                    };
                },
                hp_proofs )
          in
          Weaken
            ( {
                context = ctrip.context;
                trip = { pre = ghost_pre; prog = trip.prog; post = postc };
              },
              hp,
              implies ghost_pre (get_conclusion hp).trip.pre )
      in
      Adapt
        ( {
            context = ctrip.context;
            trip = { pre = adapted_pre; prog = trip.prog; post = trip.post };
          },
          the_proof_before_adapt )

let nonterm_handler_simple_numeric =
  nonterm_handler_template
    (fun expression -> Term (Numeric expression))
    (fun nt -> Term (Numeric (NNTerm nt)))
    false

let nonterm_handler_simple_bitvec =
  nonterm_handler_template
    (fun expression -> Term (Bitvec expression))
    (fun nt -> Term (Bitvec (BitvNTerm nt)))
    false

let nonterm_handler_simple_boolean =
  nonterm_handler_template
    (fun expression -> Boolean expression)
    (fun nt -> Boolean (BNTerm nt))
    false

let nonterm_handler_simple_stmt =
  nonterm_handler_template
    (fun expression -> Stmt expression)
    (fun nt -> Stmt (SNTerm nt))
    false

(* let simple_to_vector_state var_set =
   VS.map
     (fun var ->
       match var with
       | IntTermVar ET -> AIntTermVar ET
       | IntTermVar (T x) -> AIntTermVar (T x)
       | BoolVar BT -> ABoolVar BT
       | BoolVar (B x) -> ABoolVar (B x)
       | _ -> raise Unsupported_Var)
     var_set *)

let nonterm_handler_vector_state_numeric =
  nonterm_handler_template
    (fun expression -> Term (Numeric expression))
    (fun nt -> Term (Numeric (NNTerm nt)))
    true

let nonterm_handler_vector_state_bitvec =
  nonterm_handler_template
    (fun expression -> Term (Bitvec expression))
    (fun nt -> Term (Bitvec (BitvNTerm nt)))
    true

let nonterm_handler_vector_state_boolean =
  nonterm_handler_template
    (fun expression -> Boolean expression)
    (fun nt -> Boolean (BNTerm nt))
    true

let nonterm_handler_vector_state_stmt =
  nonterm_handler_template
    (fun expression -> Stmt expression)
    (fun nt -> Stmt (SNTerm nt))
    true

(* Various proof substrategies for different prog constructors: *)
(* Trace Variants give the strategies for constructing different types of variable-related objects.
   This lets us use the same template for simple and vector-state rules in many cases.
   TODO: Should this be a module type? Records feel like a non-idomatic choice. *)
type trace_variant = {
  et_var : variable;
  strvar_to_int_term : string -> int_term;
  strvar_to_bitv_term : string -> bitv_term;
  strvar_to_term : string -> term;
  strvar_to_var_term : string -> variable;
  et_int_term : int_term;
  et_bitv_term : bitv_term;
  et_term : term;
  bt_var : variable;
  strvar_to_var_bool : string -> variable;
  bt_form : formula;
  strvar_to_bool_form : string -> formula;
}

let simple_int_tv =
  {
    et_var = IntTermVar ET;
    strvar_to_int_term = (fun x -> ITVar (T x));
    strvar_to_bitv_term = (fun _ -> raise Unsupported_Mode);
    strvar_to_term = (fun x -> ITerm (ITVar (T x)));
    strvar_to_var_term = (fun x -> IntTermVar (T x));
    et_int_term = ITVar ET;
    et_bitv_term = BitvTVar ET;
    et_term = ITerm (ITVar ET);
    bt_var = BoolVar BT;
    strvar_to_var_bool = (fun v -> BoolVar (B v));
    bt_form = BVar BT;
    strvar_to_bool_form = (fun v -> BVar (B v));
  }

let simple_bitv_tv =
  {
    et_var = BitvTermVar ET;
    strvar_to_int_term = (fun _ -> raise Unsupported_Mode);
    strvar_to_bitv_term = (fun x -> BitvTVar (T x));
    strvar_to_term = (fun x -> BitvTerm (BitvTVar (T x)));
    strvar_to_var_term = (fun x -> BitvTermVar (T x));
    et_int_term = ITVar ET;
    et_bitv_term = BitvTVar ET;
    et_term = BitvTerm (BitvTVar ET);
    bt_var = BoolVar BT;
    strvar_to_var_bool = (fun v -> BoolVar (B v));
    bt_form = BVar BT;
    strvar_to_bool_form = (fun v -> BVar (B v));
  }

let vector_state_int_tv =
  {
    et_var = AIntTermVar ET;
    strvar_to_int_term = (fun x -> AITVar (ITUnApp (T x)));
    strvar_to_term = (fun x -> ITerm (AITVar (ITUnApp (T x))));
    strvar_to_bitv_term = (fun _ -> raise Unsupported_Mode);
    strvar_to_var_term = (fun x -> AIntTermVar (T x));
    et_int_term = AITVar (ITUnApp ET);
    et_bitv_term = ABitvTVar (BitvTUnApp ET);
    et_term = ITerm (AITVar (ITUnApp ET));
    bt_var = ABoolVar BT;
    strvar_to_var_bool = (fun v -> ABoolVar (B v));
    bt_form = ABVar (BUnApp BT);
    strvar_to_bool_form = (fun v -> ABVar (BUnApp (B v)));
  }

let vector_state_bitv_tv =
  {
    et_var = ABitvTermVar ET;
    strvar_to_int_term = (fun _ -> raise Unsupported_Mode);
    strvar_to_term = (fun x -> BitvTerm (ABitvTVar (BitvTUnApp (T x))));
    strvar_to_bitv_term = (fun x -> ABitvTVar (BitvTUnApp (T x)));
    strvar_to_var_term = (fun x -> ABitvTermVar (T x));
    et_int_term = AITVar (ITUnApp ET);
    et_bitv_term = ABitvTVar (BitvTUnApp ET);
    et_term = BitvTerm (ABitvTVar (BitvTUnApp ET));
    bt_var = ABoolVar BT;
    strvar_to_var_bool = (fun v -> ABoolVar (B v));
    bt_form = ABVar (BUnApp BT);
    strvar_to_bool_form = (fun v -> ABVar (BUnApp (B v)));
  }

(* INT & BITV Const *)
let const_template tv termer i (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  Const
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.et_var (termer i);
          prog = trip.prog;
          post = trip.post;
        };
    }

let int_simple = const_template simple_int_tv (fun i -> Term (ITerm (Int i)))

let int_vector_state =
  const_template vector_state_int_tv (fun i -> Term (ITerm (Int i)))

let bitv_simple =
  const_template simple_bitv_tv (fun btv -> Term (BitvTerm (Bitv btv)))

let bitv_vector_state =
  const_template vector_state_bitv_tv (fun btv -> Term (BitvTerm (Bitv btv)))

(* VAR *)
let var_template tv termer x (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  Var
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.et_var (termer x);
          prog = trip.prog;
          post = trip.post;
        };
    }

let int_var_simple =
  var_template simple_int_tv (fun i -> Term (ITerm (ITVar (T i))))

let int_var_vector_state =
  var_template vector_state_int_tv (fun i ->
      Term (ITerm (AITVar (ITUnApp (T i)))))

let bitv_var_simple =
  var_template simple_bitv_tv (fun btv -> Term (BitvTerm (BitvTVar (T btv))))

let bitv_var_vector_state =
  var_template vector_state_bitv_tv (fun btv ->
      Term (BitvTerm (ABitvTVar (BitvTUnApp (T btv)))))

(* TRUE *)
let true_template tv (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  True
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.bt_var (Boolean True);
          prog = trip.prog;
          post = trip.post;
        };
    }

let true_simple = true_template simple_int_tv
let true_vector_state = true_template vector_state_int_tv

(* FALSE *)
let false_template tv (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  False
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.bt_var (Boolean False);
          prog = trip.prog;
          post = trip.post;
        };
    }

let false_simple = false_template simple_int_tv
let false_vector_state = false_template vector_state_int_tv

(* SKIP *)
let skip (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  Skip
    {
      context = ctrip.context;
      trip = { pre = trip.post; prog = trip.prog; post = trip.post };
    }

(* NOT *)
let not_template tv b (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  let hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b;
            post = subs trip.post tv.bt_var (Boolean (Not tv.bt_form));
          };
      }
      implies
  in
  Not
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      hyp )

let not_simple = not_template simple_int_tv
let not_vector_state = not_template vector_state_int_tv

let unapp_template tv formula_unapp_on_et term
    (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  let hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Bitvec term);
            post =
              subs trip.post tv.et_var (formula_unapp_on_et tv.et_bitv_term);
          };
      }
      implies
  in
  UnApp
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      hyp )

let bitv_minus_simple =
  unapp_template simple_bitv_tv (fun x ->
      Term (BitvTerm (BitvUnarApp (Minus, x))))

let bitv_minus_vector_state =
  unapp_template vector_state_bitv_tv (fun x ->
      Term (BitvTerm (BitvUnarApp (Minus, x))))

let binapp_template tv formula_binapp btv1 btv2
    (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Bitvec btv2);
            post =
              subs trip.post tv.et_var
                (formula_binapp (tv.strvar_to_bitv_term fresh) tv.et_bitv_term);
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Bitvec btv1);
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_term fresh)
                (Term (BitvTerm tv.et_bitv_term));
          };
      }
      implies
  in
  BinApp
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let bitv_plus_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Plus, x, y))))

let bitv_mult_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Mult, x, y))))

let bitv_sub_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Sub, x, y))))

let bitv_or_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Or, x, y))))

let bitv_xor_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Xor, x, y))))

let bitv_and_simple =
  binapp_template simple_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (And, x, y))))

let bitv_plus_vector_state =
  binapp_template vector_state_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Plus, x, y))))

let bitv_mult_vector_state =
  binapp_template vector_state_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Mult, x, y))))

let bitv_or_vector_state =
  binapp_template vector_state_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Or, x, y))))

let bitv_xor_vector_state =
  binapp_template vector_state_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (Xor, x, y))))

let bitv_and_vector_state =
  binapp_template vector_state_bitv_tv (fun x y ->
      Term (BitvTerm (BitvBinarApp (And, x, y))))

(* AND *)
let and_template tv b1 b2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b2;
            post =
              subs trip.post tv.bt_var
                (Boolean (And (tv.strvar_to_bool_form fresh, tv.bt_form)));
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b1;
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_bool fresh)
                (Boolean tv.bt_form);
          };
      }
      implies
  in
  And
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let and_simple = and_template simple_int_tv
let and_vector_state = and_template vector_state_int_tv

(* OR *)
let or_template tv b1 b2 (ctrip : contextualized_triple_no_pre) build_pf implies
    =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b2;
            post =
              subs trip.post tv.bt_var
                (Boolean (Or (tv.strvar_to_bool_form fresh, tv.bt_form)));
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b1;
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_bool fresh)
                (Boolean tv.bt_form);
          };
      }
      implies
  in
  Or
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let or_simple = or_template simple_int_tv
let or_vector_state = or_template vector_state_int_tv

(* PLUS *)
let plus_template tv n1 n2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Numeric n2);
            post =
              subs trip.post tv.et_var
                (Term
                   (ITerm (Plus (tv.strvar_to_int_term fresh, tv.et_int_term))));
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Numeric n1);
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_term fresh)
                (Term (ITerm tv.et_int_term));
          };
      }
      implies
  in
  Plus
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let plus_simple = plus_template simple_int_tv
let plus_vector_state = plus_template vector_state_int_tv

(* MINUS *)
let minus_template tv n (ctrip : contextualized_triple_no_pre) build_pf implies
    =
  let trip = ctrip.trip in
  let hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term (Numeric n);
            post =
              subs trip.post tv.et_var (Term (ITerm (Minus tv.et_int_term)));
          };
      }
      implies
  in
  UnaryMinus
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      hyp )

let int_unaryminus_simple = minus_template simple_int_tv
let int_unaryminus_vector_state = minus_template vector_state_int_tv

(* EQUALS *)
let equals_template tv t1 t2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term t2;
            post =
              subs trip.post tv.bt_var
                (Boolean (Equals (tv.strvar_to_term fresh, tv.et_term)));
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term t1;
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_term fresh)
                (Term tv.et_term);
          };
      }
      implies
  in
  Equals
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let equals_int_simple = equals_template simple_int_tv
let equals_int_vector_state = equals_template vector_state_int_tv
let equals_bitv_simple = equals_template simple_bitv_tv
let equals_bitv_vector_state = equals_template vector_state_bitv_tv

let equals_simple a b =
  match (a, b) with
  | Numeric _, Numeric _ -> equals_int_simple a b
  | Bitvec _, Bitvec _ -> equals_bitv_simple a b
  | _ -> raise Unsupported_Mode

let equals_vector_state a b =
  match (a, b) with
  | Numeric _, Numeric _ -> equals_int_vector_state a b
  | Bitvec _, Bitvec _ -> equals_bitv_vector_state a b
  | _ -> raise Unsupported_Mode

(* LESS *)
let less_template tv t1 t2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term t2;
            post =
              subs trip.post tv.bt_var
                (Boolean (Less (tv.strvar_to_term fresh, tv.et_term)));
          };
      }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Term t1;
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_term fresh)
                (Term tv.et_term);
          };
      }
      implies
  in
  Less
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let less_int_simple = less_template simple_int_tv
let less_int_vector_state = less_template vector_state_int_tv
let less_bitv_simple = less_template simple_bitv_tv
let less_bitv_vector_state = less_template vector_state_bitv_tv

let less_simple a b =
  match (a, b) with
  | Numeric _, Numeric _ -> less_int_simple a b
  | Bitvec _, Bitvec _ -> less_bitv_simple a b
  | _ -> raise Unsupported_Mode

let less_vector_state a b =
  match (a, b) with
  | Numeric _, Numeric _ -> less_int_vector_state a b
  | Bitvec _, Bitvec _ -> less_bitv_vector_state a b
  | _ -> raise Unsupported_Mode

(* ASSIGN *)
let assign_template tv input_to_prog v t (ctrip : contextualized_triple_no_pre)
    build_pf implies =
  let trip = ctrip.trip in
  let hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = input_to_prog t;
            post = subs trip.post (tv.strvar_to_var_term v) (Term tv.et_term);
          };
      }
      implies
  in
  Assign
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      hyp )

let assign_int_simple =
  assign_template simple_int_tv (fun it -> Term (Numeric it))

let assign_int_vector_state =
  assign_template vector_state_int_tv (fun it -> Term (Numeric it))

let assign_bitv_simple =
  assign_template simple_bitv_tv (fun bitvt -> Term (Bitvec bitvt))

let assign_bitv_vector_state =
  assign_template vector_state_bitv_tv (fun bitvt -> Term (Bitvec bitvt))

(* SEQ *)
let seq_template s1 s2 (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  let right_hyp =
    build_pf
      { context = ctrip.context; trip = { prog = Stmt s2; post = trip.post } }
      implies
  in
  let left_hyp =
    build_pf
      {
        context = ctrip.context;
        trip = { prog = Stmt s1; post = (get_conclusion right_hyp).trip.pre };
      }
      implies
  in
  Seq
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion left_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      left_hyp,
      right_hyp )

let seq_simple = seq_template
let seq_vecor_state = seq_template

(* ITE *)
let ite_simple_template prog_setter b a1 a2
    (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  let else_hyp =
    build_pf
      {
        context = ctrip.context;
        trip = { prog = prog_setter a2; post = trip.post };
      }
      implies
  in
  let then_hyp =
    build_pf
      {
        context = ctrip.context;
        trip = { prog = prog_setter a1; post = trip.post };
      }
      implies
  in
  let guard_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b;
            post =
              And
                ( Implies (BVar BT, (get_conclusion then_hyp).trip.pre),
                  Implies (Not (BVar BT), (get_conclusion else_hyp).trip.pre) );
          };
      }
      implies
  in
  ITE
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion guard_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      guard_hyp,
      then_hyp,
      else_hyp )

let ite_simple_numeric = ite_simple_template (fun x -> Term (Numeric x))
let ite_simple_bitvec = ite_simple_template (fun x -> Term (Bitvec x))
let ite_simple_stmt = ite_simple_template (fun x -> Stmt x)

let ite_vector_state_template prog_setter b a1 a2
    (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  (* Make a loop variable, b_loop. *)
  let b_loop : bool_array_var = B (fresh_var_name trip.post []) in
  (* Determine x, the variables whose values can be changed by executing the loop.
     These should all be vectors. *)
  (* TODO: Make this neater -- two mutated_vars? *)
  let mutated_aint_term_vars : variable list =
    List.map
      (fun x ->
        match x with
        | IntTermVar ET -> AIntTermVar (ET : int_term_array_var)
        | IntTermVar (T x) -> AIntTermVar (T x : int_term_array_var)
        | BitvTermVar ET -> ABitvTermVar (ET : bitv_term_array_var)
        | BitvTermVar (T x) -> ABitvTermVar (T x : bitv_term_array_var)
        | _ -> raise Unsupported_Var)
      (VS.elements (VS.remove (BoolVar BT) (reassigned_vars trip.prog)))
  in
  (* Construct term mappings (x -> y) and (x -> z) for later use.
     Note, we don't want variables introduced here to collide with separate fresh vars introduced later on (i.e., in the then/else analysis).
     I think the easiest way to do that is to bar the substitution of bound variables (i.e., quantified ones).
     In principle, we should never introduce a new, unbound variable in the precondition because {|P(new)|}S{|Q|} when Q does not reference new is the same as {|\forall new. P(new)|}S{|Q|}.
     If there are weird overshadowing errors in the future though, this is a place to look.*)
  let x2y_map =
    mutated_aint_term_vars
    |> List.fold_left
         (fun xymap x ->
           List.cons
             ( x,
               new_var_of_same_type x
                 (fresh_var_name trip.post
                    (List.cons
                       (var_tostr (ABoolVar b_loop))
                       (List.map (fun (_, y) -> var_tostr y) xymap))) )
             xymap)
         []
  in
  let x2z_map =
    mutated_aint_term_vars
    |> List.fold_left
         (fun xzmap x ->
           List.cons
             ( x,
               new_var_of_same_type x
                 (fresh_var_name trip.post
                    (List.cons
                       (var_tostr (ABoolVar b_loop))
                       (List.map
                          (fun (_, y) -> var_tostr y)
                          (List.append x2y_map xzmap)))) )
             xzmap)
         []
  in
  let else_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = prog_setter a2;
            post =
              t_transform trip.post b_loop
                {
                  int_map =
                    VMap_AIT.of_seq
                      (List.to_seq
                         (List.filter_map
                            (fun (x, y) ->
                              match (x, y) with
                              | AIntTermVar a, AIntTermVar b -> Some (a, b)
                              | _ -> None)
                            x2y_map));
                  bitv_map =
                    VMap_ABitvT.of_seq
                      (List.to_seq
                         (List.filter_map
                            (fun (x, y) ->
                              match (x, y) with
                              | ABitvTermVar a, ABitvTermVar b -> Some (a, b)
                              | _ -> None)
                            x2y_map));
                };
          };
      }
      implies
  in
  let then_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = prog_setter a1;
            post =
              subs_several
                (subs_several (get_conclusion else_hyp).trip.pre
                   (List.map
                      (fun (x, z) ->
                        match (x, z) with
                        | AIntTermVar _, AIntTermVar a ->
                            (x, Logic.Formula.Term (ITerm (AITVar (ITUnApp a))))
                        | ABitvTermVar _, ABitvTermVar a ->
                            (x, Term (BitvTerm (ABitvTVar (BitvTUnApp a))))
                        | _ -> raise Unsupported_Var)
                      x2z_map))
                (List.map
                   (fun (x, y) ->
                     match (x, y) with
                     | AIntTermVar a, AIntTermVar _ ->
                         (y, Logic.Formula.Term (ITerm (AITVar (ITUnApp a))))
                     | ABitvTermVar a, ABitvTermVar _ ->
                         (y, Term (BitvTerm (ABitvTVar (BitvTUnApp a))))
                     | _ -> raise Unsupported_Var)
                   x2y_map);
          };
      }
      implies
  in
  (* TODO: Having b_loop as a pseudo-program variable causes problems when applying Adapt.
     Instead, let's just subs b_t for b_loop.
     That way, we don't need to worry about quantifying out b_loop along with our other nonterminal expansion-dependent variables.*)
  let guard_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b;
            post =
              (let post_p1 =
                 subs_several (get_conclusion then_hyp).trip.pre
                   (List.map
                      (fun (x, z) ->
                        match (x, z) with
                        | AIntTermVar a, AIntTermVar _ ->
                            (z, Logic.Formula.Term (ITerm (AITVar (ITUnApp a))))
                        | ABitvTermVar a, ABitvTermVar _ ->
                            (z, Term (BitvTerm (ABitvTVar (BitvTUnApp a))))
                        | _ -> raise Unsupported_Var)
                      x2z_map)
               in
               subs post_p1 (ABoolVar b_loop) (Boolean (ABVar (BUnApp BT))));
            (* let i : int_term_var =
                 T (fresh_var_name post_p1 [ var_tostr (ABoolVar b_loop) ])
               in
               Implies
                 ( Forall
                     ( IntTermVar i,
                       Iff
                         (ABVar (BApp (BT, ITVar i)), ABVar (BApp (b_loop, ITVar i)))
                     ),
                   post_p1 )); *)
          };
      }
      implies
  in
  ITE
    ( {
        context = ctrip.context;
        trip =
          {
            pre = (get_conclusion guard_hyp).trip.pre;
            prog = trip.prog;
            post = trip.post;
          };
      },
      guard_hyp,
      then_hyp,
      else_hyp )

let ite_vector_state_numeric =
  ite_vector_state_template (fun x -> Term (Numeric x))

let ite_vector_state_bitvec =
  ite_vector_state_template (fun x -> Term (Bitvec x))

let ite_vector_state_stmt = ite_vector_state_template (fun x -> Stmt x)

(* WHILE *)
let while_simple b inv s (ctrip : contextualized_triple_no_pre) build_pf implies
    =
  let trip = ctrip.trip in
  (* Add free vars in Q to invariant if invariant is a hole. *)
  let inv = 
    match inv with
    | BHole(s, vars) -> 
      (let newvars = VS.elements (VS.filter (fun x -> (List.for_all (fun y -> (var_to_exp x) <> y) vars)) (free_vars trip.post VS.empty)) in
      let name = (List.fold_left (fun str var -> Printf.sprintf "%s_%s" str (var_tostr var)) s newvars) in
      BHole(name, (List.append vars (List.map var_to_exp newvars))))
    | _ -> inv 
  in
  let body_hyp =
    build_pf
      { context = ctrip.context; trip = { prog = Stmt s; post = inv } }
      implies
  in
  let guard_hyp_raw =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b;
            post =
              Implies
                ( inv,
                  And
                    ( Implies (Not (BVar BT), trip.post),
                      Implies (BVar BT, (get_conclusion body_hyp).trip.pre) ) );
          };
      }
      implies
  in
  While
    ( {
        context = ctrip.context;
        trip = { pre = inv; prog = trip.prog; post = trip.post };
      },
      Weaken
        ( {
            context = ctrip.context;
            trip =
              {
                pre = True;
                prog = Boolean b;
                post = (get_conclusion guard_hyp_raw).trip.post;
              };
          },
          guard_hyp_raw,
          implies Logic.Formula.True (get_conclusion guard_hyp_raw).trip.pre ),
      body_hyp )

(* Severely underapproximate/incomplete VSWhile rule. *)
(* The rule is I(ITE)I + P(B)(\forall i. \neg b_t[i]) => I(whileBdoS)(I \land P) *)
let while_vector_state b inv s (ctrip : contextualized_triple_no_pre)
    vector_length build_pf implies =
  let trip = ctrip.trip in
  let fresh_index = fresh_var_name trip.post [] in
  let guard_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Boolean b;
            post =
              (if vector_length = 0 then
                 Forall
                   ( IntTermVar (T fresh_index),
                     Not (ABVar (BApp (BT, ITVar (T fresh_index)))) )
               else
                 List.fold_left
                   (fun form index ->
                     Logic.Formula.And (form, Not (ABVar (BApp (BT, Int index)))))
                   True
                   (List.init vector_length (fun x -> x + 1)));
          };
      }
      implies
  in
  let ite_hyp =
    build_pf
      {
        context = ctrip.context;
        trip = { prog = Stmt (ITE (b, s, Skip)); post = inv };
      }
      implies
  in
  let ite_hyp_wknd =
    Weaken
      ( {
          context = ctrip.context;
          trip = { pre = inv; prog = Stmt (ITE (b, s, Skip)); post = inv };
        },
        ite_hyp,
        implies inv (get_conclusion ite_hyp).trip.pre )
  in
  let strong_while =
    While
      ( {
          context = ctrip.context;
          trip =
            {
              pre = inv;
              prog = trip.prog;
              post = And (inv, (get_conclusion guard_hyp).trip.pre);
            };
        },
        guard_hyp,
        ite_hyp_wknd )
  in
  Weaken
    ( {
        context = ctrip.context;
        trip = { pre = inv; prog = trip.prog; post = trip.post };
      },
      strong_while,
      implies (And (inv, (get_conclusion guard_hyp).trip.pre)) trip.post )

(* let while_vector_state b inv s (ctrip : contextualized_triple_no_pre) build_pf implies
       =
     let trip = ctrip.trip in
     let body_hyp =
       build_pf
         { context = ctrip.context; trip = { prog = Stmt s; post = inv } }
         implies
     in
     let guard_hyp_raw =
       build_pf
         {
           context = ctrip.context;
           trip =
             {
               prog = Boolean b;
               post =
                 Implies
                   ( inv,
                     And
                       ( Implies (Not (BVar BT), trip.post),
                         Implies (BVar BT, (get_conclusion body_hyp).trip.pre) ) );
             };
         }
         implies
     in
     While
       ( {
           context = ctrip.context;
           trip = { pre = inv; prog = trip.prog; post = trip.post };
         },
         Weaken
           ( {
               context = ctrip.context;
               trip =
                 {
                   pre = True;
                   prog = Boolean b;
                   post = (get_conclusion guard_hyp_raw).trip.post;
                 };
             },
             guard_hyp_raw,
             implies Logic.Formula.True (get_conclusion guard_hyp_raw).trip.pre ),
         body_hyp )


         let while_simple b inv s (ctrip : contextualized_triple_no_pre) build_pf implies
         =
       let trip = ctrip.trip in
       let body_hyp =
         build_pf
           { context = ctrip.context; trip = { prog = Stmt s; post = inv } }
           implies
       in
       let guard_hyp_raw =
         build_pf
           {
             context = ctrip.context;
             trip =
               {
                 prog = Boolean b;
                 post =
                   Implies
                     ( inv,
                       And
                         ( Implies (Not (BVar BT), trip.post),
                           Implies (BVar BT, (get_conclusion body_hyp).trip.pre) ) );
               };
           }
           implies
       in
       While
         ( {
             context = ctrip.context;
             trip = { pre = inv; prog = trip.prog; post = trip.post };
           },
           Weaken
             ( {
                 context = ctrip.context;
                 trip =
                   {
                     pre = True;
                     prog = Boolean b;
                     post = (get_conclusion guard_hyp_raw).trip.post;
                   };
               },
               guard_hyp_raw,
               implies Logic.Formula.True (get_conclusion guard_hyp_raw).trip.pre ),
           body_hyp )

     let while_simple b inv s (ctrip : contextualized_triple_no_pre) build_pf implies
     =
   let trip = ctrip.trip in
   let body_hyp =
     build_pf
       { context = ctrip.context; trip = { prog = Stmt s; post = inv } }
       implies
   in
   let guard_hyp_raw =
     build_pf
       {
         context = ctrip.context;
         trip =
           {
             prog = Boolean b;
             post =
               Implies
                 ( inv,
                   And
                     ( Implies (Not (BVar BT), trip.post),
                       Implies (BVar BT, (get_conclusion body_hyp).trip.pre) ) );
           };
       }
       implies
   in
   While
     ( {
         context = ctrip.context;
         trip = { pre = inv; prog = trip.prog; post = trip.post };
       },
       Weaken
         ( {
             context = ctrip.context;
             trip =
               {
                 pre = True;
                 prog = Boolean b;
                 post = (get_conclusion guard_hyp_raw).trip.post;
               };
           },
           guard_hyp_raw,
           implies Logic.Formula.True (get_conclusion guard_hyp_raw).trip.pre ),
       body_hyp )
*)
let rec build_wpc_proof (ctrip : contextualized_triple_no_pre)
    (implies : formula -> formula -> bool Lazy.t) =
  match ctrip.trip.prog with
  | Term (Numeric (Int i)) -> int_simple i ctrip
  | Term (Numeric (Var x)) -> int_var_simple x ctrip
  | Term (Numeric (Plus (t1, t2))) ->
      plus_simple t1 t2 ctrip build_wpc_proof implies
  | Term (Numeric (Minus t)) ->
      int_unaryminus_simple t ctrip build_wpc_proof implies
  | Term (Numeric (ITE (b, n1, n2))) ->
      ite_simple_numeric b n1 n2 ctrip build_wpc_proof implies
  | Term (Numeric (NNTerm nterm)) ->
      nonterm_handler_simple_numeric nterm ctrip 0 build_wpc_proof implies
  | Term (Bitvec (Bitv btv)) -> bitv_simple btv ctrip
  | Term (Bitvec (BitvVar x)) -> bitv_var_simple x ctrip
  | Term (Bitvec (BitvUnApp (Minus, x))) ->
      bitv_minus_simple x ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (Plus, btv1, btv2))) ->
      bitv_plus_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (Mult, btv1, btv2))) ->
      bitv_mult_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (Sub, btv1, btv2))) ->
      bitv_sub_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (Or, btv1, btv2))) ->
      bitv_or_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (Xor, btv1, btv2))) ->
      bitv_xor_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BinApp (And, btv1, btv2))) ->
      bitv_and_simple btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BitvITE (b, btv1, btv2))) ->
      ite_simple_bitvec b btv1 btv2 ctrip build_wpc_proof implies
  | Term (Bitvec (BitvNTerm nterm)) ->
      nonterm_handler_simple_bitvec nterm ctrip 0 build_wpc_proof implies
  | Boolean True -> true_simple ctrip
  | Boolean False -> false_simple ctrip
  | Boolean (Not b) -> not_simple b ctrip build_wpc_proof implies
  | Boolean (And (b1, b2)) -> and_simple b1 b2 ctrip build_wpc_proof implies
  | Boolean (Or (b1, b2)) -> or_simple b1 b2 ctrip build_wpc_proof implies
  | Boolean (Equals (n1, n2)) ->
      equals_simple n1 n2 ctrip build_wpc_proof implies
  | Boolean (Less (n1, n2)) -> less_simple n1 n2 ctrip build_wpc_proof implies
  | Boolean (BNTerm nterm) ->
      nonterm_handler_simple_boolean nterm ctrip 0 build_wpc_proof implies
  | Stmt Skip -> skip ctrip
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n -> assign_int_simple v n ctrip build_wpc_proof implies
      | Bitvec btv -> assign_bitv_simple v btv ctrip build_wpc_proof implies)
  | Stmt (Seq (s1, s2)) -> seq_simple s1 s2 ctrip build_wpc_proof implies
  | Stmt (ITE (b, s1, s2)) ->
      ite_simple_stmt b s1 s2 ctrip build_wpc_proof implies
  | Stmt (While (b, inv, s)) ->
      while_simple b inv s ctrip build_wpc_proof implies
  | Stmt (SNTerm nterm) ->
      nonterm_handler_simple_stmt nterm ctrip 0 build_wpc_proof implies

(* Recursively build proof of stuff. *)
let rec build_wpc_proof_finite_vector_state (length : int)
    (ctrip : contextualized_triple_no_pre)
    (implies : formula -> formula -> bool Lazy.t) =
  let trip = ctrip.trip in
  match trip.prog with
  | Term (Numeric (Int i)) -> int_vector_state i ctrip
  | Term (Numeric (Var x)) -> int_var_vector_state x ctrip
  | Term (Numeric (Plus (t1, t2))) ->
      plus_vector_state t1 t2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Numeric (Minus t)) ->
      int_unaryminus_vector_state t ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Numeric (ITE (b, s1, s2))) ->
      ite_vector_state_numeric b s1 s2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Numeric (NNTerm nterm)) ->
      nonterm_handler_vector_state_numeric nterm ctrip length
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (Bitv btv)) -> bitv_vector_state btv ctrip
  | Term (Bitvec (BitvVar v)) -> bitv_var_vector_state v ctrip
  | Term (Bitvec (BitvUnApp (Minus, btv))) ->
      bitv_minus_vector_state btv ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (Plus, btv1, btv2))) ->
      bitv_plus_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (Mult, btv1, btv2))) ->
      bitv_mult_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (Sub, btv1, btv2))) ->
      bitv_plus_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (Or, btv1, btv2))) ->
      bitv_or_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (Xor, btv1, btv2))) ->
      bitv_xor_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BinApp (And, btv1, btv2))) ->
      bitv_and_vector_state btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BitvITE (b, btv1, btv2))) ->
      ite_vector_state_bitvec b btv1 btv2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Term (Bitvec (BitvNTerm nterm)) ->
      nonterm_handler_vector_state_bitvec nterm ctrip length
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean (Equals (n1, n2)) ->
      equals_vector_state n1 n2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean (Less (n1, n2)) ->
      less_vector_state n1 n2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean True -> true_vector_state ctrip
  | Boolean False -> false_vector_state ctrip
  | Boolean (Not b) ->
      not_vector_state b ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean (And (b1, b2)) ->
      and_vector_state b1 b2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean (Or (b1, b2)) ->
      or_vector_state b1 b2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Boolean (BNTerm nterm) ->
      nonterm_handler_vector_state_boolean nterm ctrip length
        (build_wpc_proof_finite_vector_state length)
        implies
  | Stmt Skip -> skip ctrip
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n ->
          assign_int_vector_state v n ctrip
            (build_wpc_proof_finite_vector_state length)
            implies
      | Bitvec btv ->
          assign_bitv_vector_state v btv ctrip
            (build_wpc_proof_finite_vector_state length)
            implies)
  | Stmt (Seq (s1, s2)) ->
      seq_vecor_state s1 s2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Stmt (ITE (b, s1, s2)) ->
      ite_vector_state_stmt b s1 s2 ctrip
        (build_wpc_proof_finite_vector_state length)
        implies
  | Stmt (SNTerm nterm) ->
      nonterm_handler_vector_state_stmt nterm ctrip length
        (build_wpc_proof_finite_vector_state length)
        implies
  | Stmt (While (b, inv, s)) ->
      while_vector_state b inv s ctrip length
        (build_wpc_proof_finite_vector_state length)
        implies

let rec build_wpc_proof_vector_state (ctrip : contextualized_triple_no_pre)
    (implies : formula -> formula -> bool Lazy.t) =
  let trip = ctrip.trip in
  match trip.prog with
  | Term (Numeric (Int i)) -> int_vector_state i ctrip
  | Term (Numeric (Var x)) -> int_var_vector_state x ctrip
  | Term (Numeric (Plus (t1, t2))) ->
      plus_vector_state t1 t2 ctrip build_wpc_proof_vector_state implies
  | Term (Numeric (Minus t)) ->
      int_unaryminus_vector_state t ctrip build_wpc_proof_vector_state implies
  | Term (Numeric (ITE (b, s1, s2))) ->
      ite_vector_state_numeric b s1 s2 ctrip build_wpc_proof_vector_state
        implies
  | Term (Numeric (NNTerm nterm)) ->
      nonterm_handler_vector_state_numeric nterm ctrip 0
        build_wpc_proof_vector_state implies
  | Term (Bitvec (Bitv btv)) -> bitv_vector_state btv ctrip
  | Term (Bitvec (BitvVar x)) -> bitv_var_vector_state x ctrip
  | Term (Bitvec (BitvUnApp (Minus, btv))) ->
      bitv_minus_vector_state btv ctrip build_wpc_proof_vector_state implies
  | Term (Bitvec (BinApp (Plus, btv1, btv2))) ->
      bitv_plus_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state
        implies
  | Term (Bitvec (BinApp (Mult, btv1, btv2))) ->
      bitv_mult_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state
        implies
  | Term (Bitvec (BinApp (Sub, btv1, btv2))) ->
      bitv_plus_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state
        implies
  | Term (Bitvec (BinApp (Or, btv1, btv2))) ->
      bitv_or_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state implies
  | Term (Bitvec (BinApp (Xor, btv1, btv2))) ->
      bitv_xor_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state implies
  | Term (Bitvec (BinApp (And, btv1, btv2))) ->
      bitv_and_vector_state btv1 btv2 ctrip build_wpc_proof_vector_state implies
  | Term (Bitvec (BitvITE (b, s1, s2))) ->
      ite_vector_state_bitvec b s1 s2 ctrip build_wpc_proof_vector_state implies
  | Term (Bitvec (BitvNTerm nterm)) ->
      nonterm_handler_vector_state_bitvec nterm ctrip 0
        build_wpc_proof_vector_state implies
  | Boolean (Equals (n1, n2)) ->
      equals_vector_state n1 n2 ctrip build_wpc_proof_vector_state implies
  | Boolean (Less (n1, n2)) ->
      less_vector_state n1 n2 ctrip build_wpc_proof_vector_state implies
  | Boolean True -> true_vector_state ctrip
  | Boolean False -> false_vector_state ctrip
  | Boolean (Not b) ->
      not_vector_state b ctrip build_wpc_proof_vector_state implies
  | Boolean (And (b1, b2)) ->
      and_vector_state b1 b2 ctrip build_wpc_proof_vector_state implies
  | Boolean (Or (b1, b2)) ->
      or_vector_state b1 b2 ctrip build_wpc_proof_vector_state implies
  | Boolean (BNTerm nterm) ->
      nonterm_handler_vector_state_boolean nterm ctrip 0
        build_wpc_proof_vector_state implies
  | Stmt Skip -> skip ctrip
  | Stmt (Assign (v, t)) -> (
      match t with
      | Numeric n ->
          assign_int_vector_state v n ctrip build_wpc_proof_vector_state implies
      | Bitvec btv ->
          assign_bitv_vector_state v btv ctrip build_wpc_proof_vector_state
            implies)
  | Stmt (Seq (s1, s2)) ->
      seq_vecor_state s1 s2 ctrip build_wpc_proof_vector_state implies
  | Stmt (ITE (b, s1, s2)) ->
      ite_vector_state_stmt b s1 s2 ctrip build_wpc_proof_vector_state implies
  | Stmt (SNTerm nterm) ->
      nonterm_handler_vector_state_stmt nterm ctrip 0
        build_wpc_proof_vector_state implies
  | Stmt (While (b, inv, s)) ->
      while_vector_state b inv s ctrip 0 build_wpc_proof_vector_state implies

let prove (trip : triple) (smode : synthMode) (fmode : formMode)
    (hole_grm_mode : holeGuideMode) (vc_simp : vcSimplificationMode) =
  (* Imp is the implication handling module. The proof mode determines which module we use.
     Each module is set up as a 0-ary functor because the modules returned preserve a notion of state.
     Statefulness is necessary to gather implications, discharge them in parallel, etc.
     TODO: See if it makes more sense to do this with a continuation-passing-like scheme to fake statefulness. *)
  let module VCSimp : Implications.VCSimpStrat =
    (val match vc_simp with
         | NO_SIMP -> (module Implications.No_Simp : Implications.VCSimpStrat)
         | QUANTIFY_COLLECT ->
             (module Implications.Quantify_Collect : Implications.VCSimpStrat))
  in
  let module Imp =
    (val match (smode, fmode, hole_grm_mode) with
         | HOLE_SYNTH, SIMPLE, NONE ->
             (module Implications.HoleSynthSimpleImplicatorCVC5
                       (Implications.UnconstrainedGrammarStrat)
                       (VCSimp))
         | INVS_SPECIFIED, SIMPLE, _ ->
             (module Implications.NoHoleSimpleImplicatorZ3 (VCSimp))
         | INVS_SPECIFIED, VECTOR_STATE, _ ->
             (module Implications.NoHoleVectorStateImplicatorVampire (VCSimp))
         | INVS_SPECIFIED, FINITE_VECTOR_STATE, _ ->
             Implications.finite_holeless_implicator
               (max_index (Boolean (And (trip.pre, trip.post))))
               VCSimp.deconjunctivizer
         | HOLE_SYNTH, FINITE_VECTOR_STATE, NONE ->
             Implications.finite_holes_implicator
               (max_index (Boolean (And (trip.pre, trip.post))))
               Implications.UnconstrainedGrammarStrat.bool_hole_to_sygus_grammar
               VCSimp.deconjunctivizer_rhs
         | HOLE_SYNTH, FINITE_VECTOR_STATE, BITVEC ->
             Implications.finite_holes_implicator
               (max_index (Boolean (And (trip.pre, trip.post))))
               Implications.BitvecGrammarStrat.bool_hole_to_sygus_grammar
               VCSimp.deconjunctivizer_rhs
         | _ -> raise Unsupported_Mode
        : Implications.ImplicationHandler)
  in
  let length = Logic.Formula.max_index (Boolean (And (trip.pre, trip.post))) in
  let build =
    match fmode with
    | SIMPLE -> build_wpc_proof
    | FINITE_VECTOR_STATE ->
        (* Check max vector length referenced. *)
        build_wpc_proof_finite_vector_state length
    | VECTOR_STATE -> build_wpc_proof_vector_state
  in
  let strongest =
    build
      { context = []; trip = { prog = trip.prog; post = trip.post } }
      Imp.implies
  in
  let full_pf =
    Weaken
      ( { context = []; trip },
        strongest,
        Imp.implies trip.pre (get_conclusion strongest).trip.pre )
  in
  plug_holes full_pf length (Lazy.force Imp.hole_values)
