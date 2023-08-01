open Logic.Formula
open Implications
open Logic.Variable
open Programs.Program
open Programs.NonTerminal

exception Bad_Strongest_Triple of string * string

type proofMode = HOLE_SYNTH | INVS_SPECIFIED
type triple = { pre : formula; prog : program; post : formula }
type triple_no_pre = { prog : program; post : formula }
type contextualized_triple = { context : triple list; trip : triple }

type contextualized_triple_no_pre = {
  context : triple list;
  trip : triple_no_pre;
}

type ruleApp =
  | Zero of contextualized_triple
  | One of contextualized_triple
  | True of contextualized_triple
  | False of contextualized_triple
  | Var of contextualized_triple
  | Not of contextualized_triple * ruleApp
  | Plus of contextualized_triple * ruleApp * ruleApp
  | Or of contextualized_triple * ruleApp * ruleApp
  | And of contextualized_triple * ruleApp * ruleApp
  | Equals of contextualized_triple * ruleApp * ruleApp
  | Less of contextualized_triple * ruleApp * ruleApp
  | Assign of contextualized_triple * ruleApp
  | Seq of contextualized_triple * ruleApp * ruleApp
  | ITE of contextualized_triple * ruleApp * ruleApp * ruleApp
  | While of contextualized_triple * ruleApp * ruleApp
  | Weaken of contextualized_triple * ruleApp * bool Lazy.t
  | GrmDisj of contextualized_triple * ruleApp list
  | ApplyHP of contextualized_triple
  | HP of contextualized_triple * ruleApp list
  | Adapt of contextualized_triple * ruleApp

let trip_tostr trip =
  Printf.sprintf "{%s} %s {%s}" (form_tostr trip.pre) (prog_tostr trip.prog)
    (form_tostr trip.post)

let ctrip_tostr (ctrip : contextualized_triple) =
  match ctrip.context with
  | [] -> trip_tostr ctrip.trip
  | _ ->
      Printf.sprintf "[%s] |- %s"
        (String.concat ", " (List.map trip_tostr ctrip.context))
        (trip_tostr ctrip.trip)

let get_conclusion rule =
  match rule with
  | Zero ctrip -> ctrip
  | One ctrip -> ctrip
  | True ctrip -> ctrip
  | False ctrip -> ctrip
  | Var ctrip -> ctrip
  | Not (ctrip, _) -> ctrip
  | Plus (ctrip, _, _) -> ctrip
  | And (ctrip, _, _) -> ctrip
  | Or (ctrip, _, _) -> ctrip
  | Equals (ctrip, _, _) -> ctrip
  | Less (ctrip, _, _) -> ctrip
  | Assign (ctrip, _) -> ctrip
  | Seq (ctrip, _, _) -> ctrip
  | ITE (ctrip, _, _, _) -> ctrip
  | While (ctrip, _, _) -> ctrip
  | Weaken (conc, _, _) -> conc
  | GrmDisj (conc, _) -> conc
  | ApplyHP ctrip -> ctrip
  | HP (ctrip, _) -> ctrip
  | Adapt (ctrip, _) -> ctrip

let rec ruleApp_tostr rule =
  match rule with
  | Zero ctrip -> Printf.sprintf "Zero: -> %s" (ctrip_tostr ctrip)
  | One ctrip -> Printf.sprintf "One: -> %s" (ctrip_tostr ctrip)
  | True ctrip -> Printf.sprintf "True: -> %s" (ctrip_tostr ctrip)
  | False ctrip -> Printf.sprintf "False: -> %s" (ctrip_tostr ctrip)
  | Var ctrip -> Printf.sprintf "Var: -> %s" (ctrip_tostr ctrip)
  | Not (conc, pf) ->
      Printf.sprintf "%s\nNot: %s -> %s" (ruleApp_tostr pf)
        (ctrip_tostr (get_conclusion pf))
        (ctrip_tostr conc)
  | Plus (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nPlus: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | And (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nAnd: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | Or (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nOr: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | Equals (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nEquals: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | Less (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nLess: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | Assign (conc, pf) ->
      Printf.sprintf "%s\nAssign: %s -> %s" (ruleApp_tostr pf)
        (ctrip_tostr (get_conclusion pf))
        (ctrip_tostr conc)
  | Seq (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nSeq: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (ctrip_tostr (get_conclusion lpf))
        (ctrip_tostr (get_conclusion rpf))
        (ctrip_tostr conc)
  | ITE (conc, guardpf, thenpf, elsepf) ->
      Printf.sprintf "%s\n%s\n%s\nITE: %s, %s, %s -> %s" (ruleApp_tostr guardpf)
        (ruleApp_tostr thenpf) (ruleApp_tostr elsepf)
        (ctrip_tostr (get_conclusion guardpf))
        (ctrip_tostr (get_conclusion thenpf))
        (ctrip_tostr (get_conclusion elsepf))
        (ctrip_tostr conc)
  | While (conc, guardpf, bodypf) ->
      Printf.sprintf "%s\n%s\nWhile: %s, %s -> %s" (ruleApp_tostr guardpf)
        (ruleApp_tostr bodypf)
        (ctrip_tostr (get_conclusion guardpf))
        (ctrip_tostr (get_conclusion bodypf))
        (ctrip_tostr conc)
  | Weaken (conc, pf, truth) ->
      Printf.sprintf "%s\n%sWeaken: %s -> %s" (ruleApp_tostr pf)
        (if Lazy.force truth then "" else "FALSE!!!")
        (ctrip_tostr (get_conclusion pf))
        (ctrip_tostr conc)
  | GrmDisj (conc, pfs) ->
      Printf.sprintf "%s\nGrmDisj: %s -> %s"
        (String.concat "\n" (List.map ruleApp_tostr pfs))
        (String.concat ", "
           (List.map (fun pf -> ctrip_tostr (get_conclusion pf)) pfs))
        (ctrip_tostr conc)
  | ApplyHP ctrip -> Printf.sprintf "ApplyHP: -> %s" (ctrip_tostr ctrip)
  | HP (conc, pfs) ->
      Printf.sprintf "%s\nHP: %s -> %s"
        (String.concat "\n" (List.map ruleApp_tostr pfs))
        (String.concat ", "
           (List.map (fun pf -> ctrip_tostr (get_conclusion pf)) pfs))
        (ctrip_tostr conc)
  | Adapt (ctrip, pf) ->
      Printf.sprintf "%s\nAdapt: %s -> %s" (ruleApp_tostr pf)
        (ctrip_tostr (get_conclusion pf))
        (ctrip_tostr ctrip)

(* Handles building proofs for the 3 types of non-terminals polymorphically *)
let nonterm_handler nterm ctrip to_prog
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
        (reassigned_vars trip.prog);
      (*Write x=z. *)
      let ghost_pre =
        List.fold_left
          (fun form (prog_var, ghost_var) ->
            match (prog_var, ghost_var) with
            | TermVar p, TermVar g ->
                Logic.Formula.And (form, Equals (TVar p, TVar g))
            | BoolVar p, BoolVar g ->
                Logic.Formula.And (form, Iff (BVar p, BVar g))
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
                  List.cons (prog_var, BoolVar (B y), ghost_var) xyz_list ))
          (postc, []) var_pairs_list
      in
      (* Q_0[y/x][x/z] *)
      let adapted_pre_2 =
        List.fold_left
          (fun form (x, _, z) ->
            match x with
            | TermVar x -> subs form z (Term (TVar x))
            | BoolVar x -> subs form z (Boolean (BVar x)))
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
                | BoolVar yv -> subs form x (Boolean (BVar yv)))
              trip.post xyz_list )
      in
      (* \forall y. Q_0[y/x][x/z] \rightarrow Q[y/x] *)
      let adapted_pre =
        (* print_endline (String.concat "; " (List.map (fun (x, y, z) -> Printf.sprintf "(%s, %s, %s)" (var_tostr x) (var_tostr y) (var_tostr z)) xyz_list)); *)
        List.fold_left
          (fun form (_, y, _) -> Forall (y, form))
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
              nterm.expansions
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

(* Gives proof and set of functions that check if all weakens passed *)
let rec build_wpc_proof (ctrip : contextualized_triple_no_pre)
    (implies : formula -> formula -> bool Lazy.t) =
  let trip = ctrip.trip in
  match trip.prog with
  | Numeric Zero ->
      Zero
        {
          context = ctrip.context;
          trip =
            {
              pre = subs trip.post (TermVar ET) (Term (Int 0));
              prog = trip.prog;
              post = trip.post;
            };
        }
  | Numeric One ->
      One
        {
          context = ctrip.context;
          trip =
            {
              pre = subs trip.post (TermVar ET) (Term (Int 1));
              prog = trip.prog;
              post = trip.post;
            };
        }
  | Numeric (Var x) ->
      Var
        {
          context = ctrip.context;
          trip =
            {
              pre = subs trip.post (TermVar ET) (Term (TVar (T x)));
              prog = trip.prog;
              post = trip.post;
            };
        }
  | Numeric (Plus (t1, t2)) ->
      let fresh = T (fresh_var_name trip.post []) in
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric t2;
                post =
                  subs trip.post (TermVar ET)
                    (Term (Plus (TVar fresh, TVar ET)));
              };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric t1;
                post =
                  subs (get_conclusion right_hyp).trip.pre (TermVar fresh)
                    (Term (TVar ET));
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
  | Numeric (ITE (b, n1, n2)) ->
      let else_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip = { prog = Numeric n2; post = trip.post };
          }
          implies
      in
      let then_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip = { prog = Numeric n1; post = trip.post };
          }
          implies
      in
      let guard_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b;
                post =
                  And
                    ( Implies (BVar BT, (get_conclusion then_hyp).trip.pre),
                      Implies (Not (BVar BT), (get_conclusion else_hyp).trip.pre)
                    );
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
  | Numeric (NNTerm nterm) ->
      nonterm_handler nterm ctrip
        (fun expression -> Numeric expression)
        build_wpc_proof implies
  | Boolean True ->
      True
        {
          context = ctrip.context;
          trip =
            {
              pre = subs trip.post (BoolVar BT) (Boolean True);
              prog = trip.prog;
              post = trip.post;
            };
        }
  | Boolean False ->
      False
        {
          context = ctrip.context;
          trip =
            {
              pre = subs trip.post (BoolVar BT) (Boolean False);
              prog = trip.prog;
              post = trip.post;
            };
        }
  | Boolean (Not b) ->
      let hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b;
                post = subs trip.post (BoolVar BT) (Boolean (Not (BVar BT)));
              };
          }
          implies
      in
      let newPre =
        subs (get_conclusion hyp).trip.pre (BoolVar BT)
          (Boolean (Not (BVar BT)))
      in
      Not
        ( {
            context = ctrip.context;
            trip = { pre = newPre; prog = trip.prog; post = trip.post };
          },
          hyp )
  | Boolean (And (b1, b2)) ->
      let fresh = B (fresh_var_name trip.post []) in
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b2;
                post =
                  subs trip.post (BoolVar BT)
                    (Boolean (And (BVar fresh, BVar BT)));
              };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b1;
                post =
                  subs (get_conclusion right_hyp).trip.pre (BoolVar fresh)
                    (Boolean (BVar BT));
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
  | Boolean (Or (b1, b2)) ->
      let fresh = B (fresh_var_name trip.post []) in
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b2;
                post =
                  subs trip.post (BoolVar BT)
                    (Boolean (Or (BVar fresh, BVar BT)));
              };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b1;
                post =
                  subs (get_conclusion right_hyp).trip.pre (BoolVar fresh)
                    (Boolean (BVar BT));
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
  | Boolean (Equals (n1, n2)) ->
      let fresh = T (fresh_var_name trip.post []) in
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric n2;
                post =
                  subs trip.post (BoolVar BT)
                    (Boolean (Equals (TVar fresh, TVar ET)));
              };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric n1;
                post =
                  subs (get_conclusion right_hyp).trip.pre (TermVar fresh)
                    (Term (TVar ET));
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
  | Boolean (Less (n1, n2)) ->
      let fresh = T (fresh_var_name trip.post []) in
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric n2;
                post =
                  subs trip.post (BoolVar BT)
                    (Boolean (Less (TVar fresh, TVar ET)));
              };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric n1;
                post =
                  subs (get_conclusion right_hyp).trip.pre (TermVar fresh)
                    (Term (TVar ET));
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
  | Boolean (BNTerm nterm) ->
      nonterm_handler nterm ctrip
        (fun boolean -> Boolean boolean)
        build_wpc_proof implies
  | Stmt (Assign (v, n)) ->
      let hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Numeric n;
                post = subs trip.post (TermVar (T v)) (Term (TVar ET));
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
  | Stmt (Seq (s1, s2)) ->
      let right_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip = { prog = Stmt s2; post = trip.post };
          }
          implies
      in
      let left_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              { prog = Stmt s1; post = (get_conclusion right_hyp).trip.pre };
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
  | Stmt (ITE (b, s1, s2)) ->
      let else_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip = { prog = Stmt s2; post = trip.post };
          }
          implies
      in
      let then_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip = { prog = Stmt s1; post = trip.post };
          }
          implies
      in
      let guard_hyp =
        build_wpc_proof
          {
            context = ctrip.context;
            trip =
              {
                prog = Boolean b;
                post =
                  And
                    ( Implies (BVar BT, (get_conclusion then_hyp).trip.pre),
                      Implies (Not (BVar BT), (get_conclusion else_hyp).trip.pre)
                    );
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
  | Stmt (While (b, inv, s)) ->
      let body_hyp =
        build_wpc_proof
          { context = ctrip.context; trip = { prog = Stmt s; post = inv } }
          implies
      in
      let guard_hyp_raw =
        build_wpc_proof
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
                          Implies (BVar BT, (get_conclusion body_hyp).trip.pre)
                        ) );
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
              implies True (get_conclusion guard_hyp_raw).trip.pre ),
          body_hyp )
  | Stmt (SNTerm nterm) ->
      nonterm_handler nterm ctrip
        (fun statement -> Stmt statement)
        build_wpc_proof implies

(* Substitutes holes for formulae. *)
let plug_holes_trip (trip : triple)
    (hole_map : ((string * variable list) * formula) list) =
  match trip.prog with
  | Numeric (NNTerm n) ->
      {
        pre = sub_holes trip.pre hole_map;
        prog = Numeric (NNTerm (sub_hole_nterm n hole_map));
        post = sub_holes trip.post hole_map;
      }
  | Boolean (BNTerm n) ->
      {
        pre = sub_holes trip.pre hole_map;
        prog = Boolean (BNTerm (sub_hole_nterm n hole_map));
        post = sub_holes trip.post hole_map;
      }
  | Stmt (SNTerm n) ->
      {
        pre = sub_holes trip.pre hole_map;
        prog = Stmt (SNTerm (sub_hole_nterm n hole_map));
        post = sub_holes trip.post hole_map;
      }
  | _ ->
      {
        pre = sub_holes trip.pre hole_map;
        prog = trip.prog;
        post = sub_holes trip.post hole_map;
      }

let plug_holes_ctrip (ctrip : contextualized_triple)
    (hole_map : ((string * variable list) * formula) list) :
    contextualized_triple =
  {
    context = List.map (fun trip -> plug_holes_trip trip hole_map) ctrip.context;
    trip = plug_holes_trip ctrip.trip hole_map;
  }

let rec plug_holes (rule : ruleApp)
    (hole_map : ((string * variable list) * formula) list) =
  match rule with
  | Zero ctrip -> Zero (plug_holes_ctrip ctrip hole_map)
  | One ctrip -> One (plug_holes_ctrip ctrip hole_map)
  | True ctrip -> True (plug_holes_ctrip ctrip hole_map)
  | False ctrip -> False (plug_holes_ctrip ctrip hole_map)
  | Var ctrip -> Var (plug_holes_ctrip ctrip hole_map)
  | Not (ctrip, pf) ->
      Not (plug_holes_ctrip ctrip hole_map, plug_holes pf hole_map)
  | Plus (ctrip, lpf, rpf) ->
      Plus
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | And (ctrip, lpf, rpf) ->
      And
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | Or (ctrip, lpf, rpf) ->
      Or
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | Equals (ctrip, lpf, rpf) ->
      Equals
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | Less (ctrip, lpf, rpf) ->
      Less
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | Assign (ctrip, pf) ->
      Assign (plug_holes_ctrip ctrip hole_map, plug_holes pf hole_map)
  | Seq (ctrip, lpf, rpf) ->
      Seq
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes lpf hole_map,
          plug_holes rpf hole_map )
  | ITE (ctrip, branch_pf, then_pf, else_pf) ->
      ITE
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes branch_pf hole_map,
          plug_holes then_pf hole_map,
          plug_holes else_pf hole_map )
  | While (ctrip, guard_pf, body_pf) ->
      While
        ( plug_holes_ctrip ctrip hole_map,
          plug_holes guard_pf hole_map,
          plug_holes body_pf hole_map )
  | Weaken (ctrip, pf, truth) ->
      Weaken (plug_holes_ctrip ctrip hole_map, plug_holes pf hole_map, truth)
  | GrmDisj (ctrip, pfs) ->
      GrmDisj
        ( plug_holes_ctrip ctrip hole_map,
          List.map (fun pf -> plug_holes pf hole_map) pfs )
  | ApplyHP ctrip -> ApplyHP (plug_holes_ctrip ctrip hole_map)
  | HP (ctrip, pfs) ->
      HP
        ( plug_holes_ctrip ctrip hole_map,
          List.map (fun pf -> plug_holes pf hole_map) pfs )
  | Adapt (ctrip, pf) ->
      Adapt (plug_holes_ctrip ctrip hole_map, plug_holes pf hole_map)

let prove (trip : triple) (mode : proofMode) =
  let implies, hole_map =
    match mode with
    | HOLE_SYNTH -> implicator_synth ()
    | INVS_SPECIFIED -> implicator_synth ()
  in
  let strongest =
    build_wpc_proof
      { context = []; trip = { prog = trip.prog; post = trip.post } }
      implies
  in
  let full_pf =
    Weaken
      ( { context = []; trip },
        strongest,
        implies trip.pre (get_conclusion strongest).trip.pre )
  in
  plug_holes full_pf (Lazy.force hole_map)
