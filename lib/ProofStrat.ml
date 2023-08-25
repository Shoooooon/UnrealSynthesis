open Logic.Formula
open Logic.Variable
open Programs.Program
open Programs.NonTerminal
open ProofRule

exception Bad_Strongest_Triple of string * string
exception Unsupported_Var
exception Unsupported_Mode

type synthMode = HOLE_SYNTH | INVS_SPECIFIED
type formMode = SIMPLE | VECTOR_STATE

(* Handles building proofs for the 3 types of non-terminals polymorphically.
   Reassigned_var_finder finds the reassigned vars from a given program; taking this as input lets us support simple and vector-state behaviors.*)
let nonterm_handler_template reassigned_var_finder to_prog nterm ctrip
    (build_wpc_proof :
      contextualized_triple_no_pre ->
      (formula -> formula -> bool Lazy.t) ->
      ruleApp) implies =
  let trip = ctrip.trip in
  match nterm.strongest with
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
                   trip = { prog = to_prog expansion; post = trip.post };
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
      (* First, make sure the proposed x covers all program variables whose values can change in the body.
          TODO: Move this check to intake of non-terminal at some point. *)
      VS.iter
        (fun var ->
          if List.mem var (List.map (fun (a, _) -> a) var_pairs_list) then ()
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
        (reassigned_var_finder trip.prog);
      (*Write x=z. *)
      let ghost_pre =
        List.fold_left
          (fun form (prog_var, ghost_var) ->
            match (prog_var, ghost_var) with
            | TermVar p, TermVar g ->
                Logic.Formula.And (form, Equals (TVar p, TVar g))
            | BoolVar p, BoolVar g ->
                Logic.Formula.And (form, Iff (BVar p, BVar g))
            | ABoolVar p, ABoolVar g ->
                Logic.Formula.And
                  ( form,
                    Forall
                      ( TermVar (T "i"),
                        Iff
                          ( ABVar (App (p, TVar (T "i"))),
                            ABVar (App (g, TVar (T "i"))) ) ) )
            | ATermVar p, ATermVar g ->
                Logic.Formula.And
                  ( form,
                    Forall
                      ( TermVar (T "i"),
                        Equals
                          ( ATVar (App (p, TVar (T "i"))),
                            ATVar (App (g, TVar (T "i"))) ) ) )
            | _ -> raise (Bad_Strongest_Triple (prog_tostr trip.prog, "")))
          True var_pairs_list
      in
      (* Write the adapt precondition \forall y. Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      (* Q_0[y/x] *)
      (* Generation of y is also dependent on Q to avoid capture *)
      let adapted_pre_1, xyz_list =
        List.fold_left
          (fun (form, xyz_list) (prog_var, ghost_var) ->
            let y =
              fresh_var_name
                (And (form, trip.post))
                (List.map (fun (_, y, _) -> var_tostr y) xyz_list)
            in
            match prog_var with
            | TermVar _ ->
                ( subs form prog_var (Term (TVar (T y))),
                  List.cons (prog_var, TermVar (T y), ghost_var) xyz_list )
            | BoolVar _ ->
                ( subs form prog_var (Boolean (BVar (B y))),
                  List.cons (prog_var, BoolVar (B y), ghost_var) xyz_list )
            | ABoolVar _ ->
                ( subs form prog_var (Boolean (ABVar (UnApp (B y)))),
                  List.cons (prog_var, ABoolVar (B y), ghost_var) xyz_list )
            | ATermVar _ ->
                ( subs form prog_var (Term (ATVar (UnApp (T y)))),
                  List.cons (prog_var, ATermVar (T y), ghost_var) xyz_list ))
          (postc, []) var_pairs_list
      in
      (* Q_0[y/x][x/z] *)
      let adapted_pre_2 =
        List.fold_left
          (fun form (x, _, z) ->
            match x with
            | TermVar x -> subs form z (Term (TVar x))
            | BoolVar x -> subs form z (Boolean (BVar x))
            | ATermVar x -> subs form z (Term (ATVar (UnApp x)))
            | ABoolVar x -> subs form z (Boolean (ABVar (UnApp x))))
          adapted_pre_1 xyz_list
      in
      (* Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      let adapted_pre_3 =
        Implies
          ( adapted_pre_2,
            List.fold_left
              (fun form (x, y, _) ->
                match y with
                | TermVar yv -> subs form x (Term (TVar yv))
                | BoolVar yv -> subs form x (Boolean (BVar yv))
                | ATermVar yv -> subs form x (Term (ATVar (UnApp yv)))
                | ABoolVar yv -> subs form x (Boolean (ABVar (UnApp yv))))
              trip.post xyz_list )
      in
      (* \forall y. Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      let adapted_pre =
        (* adapted_pre_3 *)
        List.fold_left
          (fun form (_, y, _) -> (forall y form))
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
                    trip = { prog = to_prog expansion; post = postc };
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
  nonterm_handler_template reassigned_vars (fun expression ->
      Numeric expression)

let nonterm_handler_simple_boolean =
  nonterm_handler_template reassigned_vars (fun expression ->
      Boolean expression)

let nonterm_handler_simple_stmt =
  nonterm_handler_template reassigned_vars (fun expression -> Stmt expression)

let simple_to_vector_state var_set =
  VS.map
    (fun var ->
      match var with
      | TermVar ET -> ATermVar ET
      | TermVar (T x) -> ATermVar (T x)
      | BoolVar BT -> ABoolVar BT
      | BoolVar (B x) -> ABoolVar (B x)
      | _ -> raise Unsupported_Var)
    var_set

let nonterm_handler_vector_state_numeric =
  nonterm_handler_template
    (fun prog -> simple_to_vector_state (reassigned_vars prog))
    (fun expression -> Numeric expression)

let nonterm_handler_vector_state_boolean =
  nonterm_handler_template
    (fun prog -> simple_to_vector_state (reassigned_vars prog))
    (fun expression -> Boolean expression)

let nonterm_handler_vector_state_stmt =
  nonterm_handler_template
    (fun prog -> simple_to_vector_state (reassigned_vars prog))
    (fun expression -> Stmt expression)

(* Various proof substrategies for different prog constructors: *)
(* Trace Variants give the strategies for constructing different types of variable-related objects.
   This lets us use the same template for simple and vector-state rules in many cases.
   TODO: Should this be a module type? Records feel like a non-idomatic choice. *)
type trace_variant = {
  et_var : variable;
  strvar_to_term : string -> term;
  strvar_to_var_term : string -> variable;
  et_term : term;
  bt_var : variable;
  strvar_to_var_bool : string -> variable;
  bt_form : formula;
  strvar_to_bool_form : string -> formula;
}

let simple_tv =
  {
    et_var = TermVar ET;
    strvar_to_term = (fun x -> TVar (T x));
    strvar_to_var_term = (fun x -> TermVar (T x));
    et_term = TVar ET;
    bt_var = BoolVar BT;
    strvar_to_var_bool = (fun v -> BoolVar (B v));
    bt_form = BVar BT;
    strvar_to_bool_form = (fun v -> BVar (B v));
  }

let vector_state_tv =
  {
    et_var = ATermVar ET;
    strvar_to_term = (fun x -> ATVar (UnApp (T x)));
    strvar_to_var_term = (fun x -> ATermVar (T x));
    et_term = ATVar (UnApp ET);
    bt_var = ABoolVar BT;
    strvar_to_var_bool = (fun v -> ABoolVar (B v));
    bt_form = ABVar (UnApp BT);
    strvar_to_bool_form = (fun v -> ABVar (UnApp (B v)));
  }

(* ZERO *)
let zero_template tv (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  Zero
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.et_var (Term (Int 0));
          prog = trip.prog;
          post = trip.post;
        };
    }

let zero_simple = zero_template simple_tv
let zero_vector_state = zero_template vector_state_tv

(* ONE *)
let one_template tv (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  One
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.et_var (Term (Int 1));
          prog = trip.prog;
          post = trip.post;
        };
    }

let one_simple = one_template simple_tv
let one_vector_state = one_template vector_state_tv

(* VAR *)
let var_template tv x (ctrip : contextualized_triple_no_pre) =
  let trip = ctrip.trip in
  Var
    {
      context = ctrip.context;
      trip =
        {
          pre = subs trip.post tv.et_var (Term (tv.strvar_to_term x));
          prog = trip.prog;
          post = trip.post;
        };
    }

let var_simple = var_template simple_tv
let var_vector_state = var_template vector_state_tv

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

let true_simple = true_template simple_tv
let true_vector_state = true_template vector_state_tv

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

let false_simple = false_template simple_tv
let false_vector_state = false_template vector_state_tv

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

let not_simple = not_template simple_tv
let not_vector_state = not_template vector_state_tv

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

let and_simple = and_template simple_tv
let and_vector_state = and_template vector_state_tv

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

let or_simple = or_template simple_tv
let or_vector_state = or_template vector_state_tv

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
            prog = Numeric n2;
            post =
              subs trip.post tv.et_var
                (Term (Plus (tv.strvar_to_term fresh, tv.et_term)));
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
            prog = Numeric n1;
            post =
              subs (get_conclusion right_hyp).trip.pre
                (tv.strvar_to_var_term fresh)
                (Term tv.et_term);
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

let plus_simple = plus_template simple_tv
let plus_vector_state = plus_template vector_state_tv

(* EQUALS *)
let equals_template tv n1 n2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Numeric n2;
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
            prog = Numeric n1;
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

let equals_simple = equals_template simple_tv
let equals_vector_state = equals_template vector_state_tv

(* LESS *)
let less_template tv n1 n2 (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let fresh = fresh_var_name trip.post [] in
  let right_hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Numeric n2;
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
            prog = Numeric n1;
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

let less_simple = less_template simple_tv
let less_vector_state = less_template vector_state_tv

(* ASSIGN *)
let assign_template tv v n (ctrip : contextualized_triple_no_pre) build_pf
    implies =
  let trip = ctrip.trip in
  let hyp =
    build_pf
      {
        context = ctrip.context;
        trip =
          {
            prog = Numeric n;
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

let assign_simple = assign_template simple_tv
let assign_vector_state = assign_template vector_state_tv

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

let ite_simple_numeric = ite_simple_template (fun x -> Numeric x)
let ite_simple_stmt = ite_simple_template (fun x -> Stmt x)

let ite_vector_state_template prog_setter b a1 a2
    (ctrip : contextualized_triple_no_pre) build_pf implies =
  let trip = ctrip.trip in
  (* Make a loop variable, b_loop. *)
  let b_loop : bool_array_var = B (fresh_var_name trip.post []) in
  (* Determine x, the variables whose values can be changed by executing the loop.
     These should all be vectors. *)
  (* TODO: Make this neater -- two mutated_vars? *)
  let mutated_aterm_vars : term_array_var list =
    List.map
      (fun x ->
        match x with
        | TermVar ET -> (ET : term_array_var)
        | TermVar (T x) -> (T x : term_array_var)
        | _ -> raise Unsupported_Var)
      (VS.elements (VS.remove (BoolVar BT) (reassigned_vars trip.prog)))
  in
  (* Construct term mappings (x -> y) and (x -> z) for later use. 
     Note, we don't want variables introduced here to collide with separate fresh vars introduced later on (i.e., in the then/else analysis).
     I think the easiest way to do that is to bar the substitution of bound variables (i.e., quantified ones).
     In principle, we should never introduce a new, unbound variable in the precondition because {|P(new)|}S{|Q|} when Q does not reference new is the same as {|\forall new. P(new)|}S{|Q|}.
     If there are weird overshadowing errors in the future though, this is a place to look.*)
  let x2y_map =
    mutated_aterm_vars
    |> List.fold_left
         (fun xymap x ->
           List.cons
             ( x,
               (T
                  (fresh_var_name trip.post
                     (List.cons
                        (var_tostr (ABoolVar b_loop))
                        (List.map (fun (_, y) -> var_tostr (ATermVar y)) xymap)))
                 : term_array_var) )
             xymap)
         []
  in
  let x2z_map =
    mutated_aterm_vars
    |> List.fold_left
         (fun xzmap x ->
           List.cons
             ( x,
               (T
                  (fresh_var_name trip.post
                     (List.cons
                        (var_tostr (ABoolVar b_loop))
                        (List.map
                           (fun (_, y) -> var_tostr (ATermVar y))
                           (List.append x2y_map xzmap))))
                 : term_array_var) )
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
                (VMap_AT.of_seq (List.to_seq x2y_map));
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
                      (fun (x, z) -> (ATermVar x, Term (ATVar (UnApp z))))
                      x2z_map))
                (List.map
                   (fun (x, y) -> (ATermVar y, Term (ATVar (UnApp x))))
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
                      (fun (x, z) -> (ATermVar z, Term (ATVar (UnApp x))))
                      x2z_map)
               in
               subs post_p1 (ABoolVar b_loop) (Boolean (ABVar (UnApp BT))));
               (* let i : term_var =
                 T (fresh_var_name post_p1 [ var_tostr (ABoolVar b_loop) ])
               in
               Implies
                 ( Forall
                     ( TermVar i,
                       Iff
                         (ABVar (App (BT, TVar i)), ABVar (App (b_loop, TVar i)))
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

let ite_vector_state_numeric = ite_vector_state_template (fun x -> Numeric x)
let ite_vector_state_stmt = ite_vector_state_template (fun x -> Stmt x)

(* WHILE *)
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
  | Numeric Zero -> zero_simple ctrip
  | Numeric One -> one_simple ctrip
  | Numeric (Var x) -> var_simple x ctrip
  | Numeric (Plus (t1, t2)) -> plus_simple t1 t2 ctrip build_wpc_proof implies
  | Numeric (ITE (b, n1, n2)) ->
      ite_simple_numeric b n1 n2 ctrip build_wpc_proof implies
  | Numeric (NNTerm nterm) ->
      nonterm_handler_simple_numeric nterm ctrip build_wpc_proof implies
  | Boolean True -> true_simple ctrip
  | Boolean False -> false_simple ctrip
  | Boolean (Not b) -> not_simple b ctrip build_wpc_proof implies
  | Boolean (And (b1, b2)) -> and_simple b1 b2 ctrip build_wpc_proof implies
  | Boolean (Or (b1, b2)) -> or_simple b1 b2 ctrip build_wpc_proof implies
  | Boolean (Equals (n1, n2)) ->
      equals_simple n1 n2 ctrip build_wpc_proof implies
  | Boolean (Less (n1, n2)) -> less_simple n1 n2 ctrip build_wpc_proof implies
  | Boolean (BNTerm nterm) ->
      nonterm_handler_simple_boolean nterm ctrip build_wpc_proof implies
  | Stmt (Assign (v, n)) -> assign_simple v n ctrip build_wpc_proof implies
  | Stmt (Seq (s1, s2)) -> seq_simple s1 s2 ctrip build_wpc_proof implies
  | Stmt (ITE (b, s1, s2)) ->
      ite_simple_stmt b s1 s2 ctrip build_wpc_proof implies
  | Stmt (While (b, inv, s)) ->
      while_simple b inv s ctrip build_wpc_proof implies
  | Stmt (SNTerm nterm) ->
      nonterm_handler_simple_stmt nterm ctrip build_wpc_proof implies

let rec build_wpc_proof_vector_state (ctrip : contextualized_triple_no_pre)
    (implies : formula -> formula -> bool Lazy.t) =
  let trip = ctrip.trip in
  match trip.prog with
  | Numeric Zero -> zero_vector_state ctrip
  | Numeric One -> one_vector_state ctrip
  | Numeric (Var x) -> var_vector_state x ctrip
  | Numeric (Plus (t1, t2)) ->
      plus_vector_state t1 t2 ctrip build_wpc_proof_vector_state implies
  | Numeric (ITE (b, s1, s2)) ->
      ite_vector_state_numeric b s1 s2 ctrip build_wpc_proof_vector_state
        implies
  | Numeric (NNTerm nterm) ->
      nonterm_handler_vector_state_numeric nterm ctrip
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
      nonterm_handler_vector_state_boolean nterm ctrip
        build_wpc_proof_vector_state implies
  | Stmt (Assign (v, n)) ->
      assign_vector_state v n ctrip build_wpc_proof_vector_state implies
  | Stmt (Seq (s1, s2)) ->
      seq_vecor_state s1 s2 ctrip build_wpc_proof_vector_state implies
  | Stmt (ITE (b, s1, s2)) ->
      ite_vector_state_stmt b s1 s2 ctrip build_wpc_proof_vector_state implies
  | Stmt (SNTerm nterm) ->
      nonterm_handler_vector_state_stmt nterm ctrip build_wpc_proof_vector_state
        implies
  | _ -> raise Unsupported_Var

let prove (trip : triple) (smode : synthMode) (fmode : formMode) =
  (* Imp is the implication handling module. The proof mode determines which module we use.
     Each module is set up as a 0-ary functor because the modules returned preserve a notion of state.
     Statefulness is necessary to gather implications, discharge them in parallel, etc.
     TODO: See if it makes more sense to do this with a continuation-passing-like scheme to fake statefulness. *)
  let module Imp =
    (val match (smode, fmode) with
         | HOLE_SYNTH, SIMPLE ->
             (module Implications.HoleSynthSimpleImplicatorCVC5 ())
         | INVS_SPECIFIED, SIMPLE ->
             (module Implications.NoHoleSimpleImplicatorZ3 ())
         | INVS_SPECIFIED, VECTOR_STATE ->
             (module Implications.NoHoleVectorStateImplicatorVampire ())
         | _ -> raise Unsupported_Mode
        : Implications.ImplicationHandler)
  in
  let build =
    match fmode with
    | SIMPLE -> build_wpc_proof
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
  plug_holes full_pf (Lazy.force Imp.hole_values)
