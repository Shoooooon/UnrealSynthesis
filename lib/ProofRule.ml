open Formula
open Variable
open Program

type triple = { pre : formula; prog : program; post : formula }
type triple_no_pre = { prog : program; post : formula }

type ruleApp =
  | Zero of triple
  | One of triple
  | True of triple
  | False of triple
  | Var of triple
  | Not of triple * ruleApp
  | Plus of triple * ruleApp * ruleApp
  | Or of triple * ruleApp * ruleApp
  | And of triple * ruleApp * ruleApp
  | Equals of triple * ruleApp * ruleApp
  | Less of triple * ruleApp * ruleApp
  | Assign of triple * ruleApp
  | Seq of triple * ruleApp * ruleApp
  | ITE of triple * ruleApp * ruleApp * ruleApp
  | While of triple * ruleApp * ruleApp
  | Weaken of triple * ruleApp * bool Lazy.t
  | GrmDisj of triple * ruleApp list

let trip_tostr trip =
  Printf.sprintf "{%s} %s {%s}" (form_tostr trip.pre) (prog_tostr trip.prog)
    (form_tostr trip.post)

let get_conclusion rule =
  match rule with
  | Zero trip -> trip
  | One trip -> trip
  | True trip -> trip
  | False trip -> trip
  | Var trip -> trip
  | Not (trip, _) -> trip
  | Plus (trip, _, _) -> trip
  | And (trip, _, _) -> trip
  | Or (trip, _, _) -> trip
  | Equals (trip, _, _) -> trip
  | Less (trip, _, _) -> trip
  | Assign (trip, _) -> trip
  | Seq (trip, _, _) -> trip
  | ITE (trip, _, _, _) -> trip
  | While (trip, _, _) -> trip
  | Weaken (conc, _, _) -> conc
  | GrmDisj (conc, _) -> conc

let rec ruleApp_tostr rule =
  match rule with
  | Zero trip -> Printf.sprintf "Zero: -> %s" (trip_tostr trip)
  | One trip -> Printf.sprintf "One: -> %s" (trip_tostr trip)
  | True trip -> Printf.sprintf "True: -> %s" (trip_tostr trip)
  | False trip -> Printf.sprintf "False: -> %s" (trip_tostr trip)
  | Var trip -> Printf.sprintf "Var: -> %s" (trip_tostr trip)
  | Not (conc, pf) ->
      Printf.sprintf "%s\nNot: %s -> %s" (ruleApp_tostr pf)
        (trip_tostr (get_conclusion pf))
        (trip_tostr conc)
  | Plus (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nPlus: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | And (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nAnd: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | Or (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nOr: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | Equals (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nEquals: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | Less (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nLess: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | Assign (conc, pf) ->
      Printf.sprintf "%s\nAssign: %s -> %s" (ruleApp_tostr pf)
        (trip_tostr (get_conclusion pf))
        (trip_tostr conc)
  | Seq (conc, lpf, rpf) ->
      Printf.sprintf "%s\n%s\nSeq: %s, %s -> %s" (ruleApp_tostr lpf)
        (ruleApp_tostr rpf)
        (trip_tostr (get_conclusion lpf))
        (trip_tostr (get_conclusion rpf))
        (trip_tostr conc)
  | ITE (conc, guardpf, thenpf, elsepf) ->
      Printf.sprintf "%s\n%s\n%s\nITE: %s, %s, %s -> %s" (ruleApp_tostr guardpf)
        (ruleApp_tostr thenpf) (ruleApp_tostr elsepf)
        (trip_tostr (get_conclusion guardpf))
        (trip_tostr (get_conclusion thenpf))
        (trip_tostr (get_conclusion elsepf))
        (trip_tostr conc)
  | While (conc, guardpf, bodypf) ->
      Printf.sprintf "%s\n%s\nWhile: %s, %s -> %s" (ruleApp_tostr guardpf)
        (ruleApp_tostr bodypf)
        (trip_tostr (get_conclusion guardpf))
        (trip_tostr (get_conclusion bodypf))
        (trip_tostr conc)
  | Weaken (conc, pf, truth) ->
      Printf.sprintf "%s\n%sWeaken: %s -> %s" (ruleApp_tostr pf)
        (if Lazy.force truth then "" else "FALSE!!!")
        (trip_tostr (get_conclusion pf))
        (trip_tostr conc)
  | GrmDisj (conc, pfs) ->
      Printf.sprintf "%s\nGrmDisj: %s -> %s"
        (String.concat "\n" (List.map ruleApp_tostr pfs))
        (String.concat ", "
           (List.map (fun pf -> trip_tostr (get_conclusion pf)) pfs))
        (trip_tostr conc)

(* Gives proof and set of functions that check if all weakens passed *)
let rec build_wpc_proof (trip : triple_no_pre) =
  match trip.prog with
  | Numeric Zero ->
      Zero
        {
          pre = subs trip.post ET (Term (Int 0));
          prog = trip.prog;
          post = trip.post;
        }
  | Numeric One ->
      One
        {
          pre = subs trip.post ET (Term (Int 1));
          prog = trip.prog;
          post = trip.post;
        }
  | Numeric (Var x) ->
      Var
        {
          pre = subs trip.post ET (Term (TVar (Var x)));
          prog = trip.prog;
          post = trip.post;
        }
  | Numeric (Plus (t1, t2)) ->
      let fresh = fresh_var trip.post in
      let right_hyp =
        build_wpc_proof
          {
            prog = Numeric t2;
            post = subs trip.post ET (Term (Plus (TVar fresh, TVar ET)));
          }
      in
      let left_hyp =
        build_wpc_proof
          {
            prog = Numeric t1;
            post = subs (get_conclusion right_hyp).pre fresh (Term (TVar ET));
          }
      in
      Plus
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Numeric (ITE (b, n1, n2)) ->
      let else_hyp = build_wpc_proof { prog = Numeric n2; post = trip.post } in
      let then_hyp = build_wpc_proof { prog = Numeric n1; post = trip.post } in
      let guard_hyp =
        build_wpc_proof
          {
            prog = Boolean b;
            post =
              And
                ( Implies (BVar BT, (get_conclusion then_hyp).pre),
                  Implies (Not (BVar BT), (get_conclusion else_hyp).pre) );
          }
      in
      ITE
        ( {
            pre = (get_conclusion guard_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          guard_hyp,
          then_hyp,
          else_hyp )
  | Numeric (NTerm nterm) ->
    (match nterm.strongest with
      None -> (* If non-recursive, apply GrmDisj *)
        (* Build a list of hypotheses *)
        let hypotheses =
          List.fold_left
            (fun pflist expansion ->
              List.cons
                (build_wpc_proof { prog = Numeric expansion; post = trip.post })
                pflist)
            [] (NonTerminal.expand nterm)
        in
        (* Assemble the grmdisj proof *)
        GrmDisj
          ( {
              pre =
                List.fold_left
                  (fun form hypothesis ->
                    (* "T \land" Could be better *)
                    Formula.And (form, (get_conclusion hypothesis).pre))
                  True hypotheses;
              prog = trip.prog;
              post = trip.post;
            },
            hypotheses )
    | Some (_, _) -> (* If triple in context, ApplyHP. Else, apply rule of adaptation -- adapt to conclusion, add strongest to context then apply GrmDisj. *)
        raise Subs_Type_Mismatch;)

  | Boolean True ->
      True
        {
          pre = subs trip.post BT (Boolean True);
          prog = trip.prog;
          post = trip.post;
        }
  | Boolean False ->
      False
        {
          pre = subs trip.post BT (Boolean False);
          prog = trip.prog;
          post = trip.post;
        }
  | Boolean (Not b) ->
      let hyp =
        build_wpc_proof
          {
            prog = Boolean b;
            post = subs trip.post BT (Boolean (Not (BVar BT)));
          }
      in
      let newPre = subs (get_conclusion hyp).pre BT (Boolean (Not (BVar BT))) in
      Not ({ pre = newPre; prog = trip.prog; post = trip.post }, hyp)
  | Boolean (And (b1, b2)) ->
      let fresh = fresh_var trip.post in
      let right_hyp =
        build_wpc_proof
          {
            prog = Boolean b2;
            post = subs trip.post BT (Boolean (And (BVar fresh, BVar BT)));
          }
      in
      let left_hyp =
        build_wpc_proof
          {
            prog = Boolean b1;
            post = subs (get_conclusion right_hyp).pre fresh (Boolean (BVar BT));
          }
      in
      And
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Boolean (Or (b1, b2)) ->
      let fresh = fresh_var trip.post in
      let right_hyp =
        build_wpc_proof
          {
            prog = Boolean b2;
            post = subs trip.post BT (Boolean (Or (BVar fresh, BVar BT)));
          }
      in
      let left_hyp =
        build_wpc_proof
          {
            prog = Boolean b1;
            post = subs (get_conclusion right_hyp).pre fresh (Boolean (BVar BT));
          }
      in
      Or
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Boolean (Equals (n1, n2)) ->
      let fresh = fresh_var trip.post in
      let right_hyp =
        build_wpc_proof
          {
            prog = Numeric n2;
            post = subs trip.post BT (Boolean (Equals (TVar fresh, TVar ET)));
          }
      in
      let left_hyp =
        build_wpc_proof
          {
            prog = Numeric n1;
            post = subs (get_conclusion right_hyp).pre fresh (Term (TVar ET));
          }
      in
      Equals
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Boolean (Less (n1, n2)) ->
      let fresh = fresh_var trip.post in
      let right_hyp =
        build_wpc_proof
          {
            prog = Numeric n2;
            post = subs trip.post BT (Boolean (Less (TVar fresh, TVar ET)));
          }
      in
      let left_hyp =
        build_wpc_proof
          {
            prog = Numeric n1;
            post = subs (get_conclusion right_hyp).pre fresh (Term (TVar ET));
          }
      in
      Less
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Stmt (Assign (v, n)) ->
      let hyp =
        build_wpc_proof
          { prog = Numeric n; post = subs trip.post (Var v) (Term (TVar ET)) }
      in
      Assign
        ( { pre = (get_conclusion hyp).pre; prog = trip.prog; post = trip.post },
          hyp )
  | Stmt (Seq (s1, s2)) ->
      let right_hyp = build_wpc_proof { prog = Stmt s2; post = trip.post } in
      let left_hyp =
        build_wpc_proof
          { prog = Stmt s1; post = (get_conclusion right_hyp).pre }
      in
      Seq
        ( {
            pre = (get_conclusion left_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          left_hyp,
          right_hyp )
  | Stmt (ITE (b, s1, s2)) ->
      let else_hyp = build_wpc_proof { prog = Stmt s2; post = trip.post } in
      let then_hyp = build_wpc_proof { prog = Stmt s1; post = trip.post } in
      let guard_hyp =
        build_wpc_proof
          {
            prog = Boolean b;
            post =
              And
                ( Implies (BVar BT, (get_conclusion then_hyp).pre),
                  Implies (Not (BVar BT), (get_conclusion else_hyp).pre) );
          }
      in
      ITE
        ( {
            pre = (get_conclusion guard_hyp).pre;
            prog = trip.prog;
            post = trip.post;
          },
          guard_hyp,
          then_hyp,
          else_hyp )
  | Stmt (While (b, inv, s)) ->
      let body_hyp = build_wpc_proof { prog = Stmt s; post = inv } in
      let guard_hyp_raw =
        build_wpc_proof
          {
            prog = Boolean b;
            post =
              Implies
                ( inv,
                  And
                    ( Implies (Not (BVar BT), trip.post),
                      Implies (BVar BT, (get_conclusion body_hyp).pre) ) );
          }
      in
      While
        ( { pre = inv; prog = trip.prog; post = trip.post },
          Weaken
            ( {
                pre = True;
                prog = Boolean b;
                post = (get_conclusion guard_hyp_raw).post;
              },
              guard_hyp_raw,
              implies True (get_conclusion guard_hyp_raw).pre ),
          body_hyp )
(* else raise (Weak_While_Invariant ((form_tostr inv), (form_tostr (get_conclusion guard_hyp_raw).pre))) *)

let prove (trip : triple) =
  let strongest = build_wpc_proof { prog = trip.prog; post = trip.post } in
  Weaken (trip, strongest, implies trip.pre (get_conclusion strongest).pre)
