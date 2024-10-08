open Logic.Formula
open Logic.Variable
open Programs.Program
open Programs.NonTerminal

exception Proof_Contents_Mismatch

type triple = { pre : formula; prog : program; post : formula }
type triple_no_pre = { prog : program; post : formula }
type contextualized_triple = { context : triple list; trip : triple }

type contextualized_triple_no_pre = {
  context : triple list;
  trip : triple_no_pre;
}

type ruleApp =
  | Const of contextualized_triple
  | True of contextualized_triple
  | False of contextualized_triple
  | Skip of contextualized_triple
  | Var of contextualized_triple
  | Not of contextualized_triple * ruleApp
  | UnApp of contextualized_triple * ruleApp
  | BinApp of contextualized_triple * ruleApp * ruleApp
  | Plus of contextualized_triple * ruleApp * ruleApp
  | UnaryMinus of contextualized_triple * ruleApp
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

(* Produces string [Grm] {triple} that can be read back in. *)
let trip_to_parseable_str (trip : triple) =
  let grm = get_nonterms trip.prog in
  Printf.sprintf "%s \n {|%s|} %s %s {|%s|}"
    (grammar_to_parseable_str grm)
    (form_to_parseable_str trip.pre)
    (match trip.prog with
    | Term (Numeric _) -> "Int"
    | Term (Bitvec _) -> raise Programs.Program.Unimplemented
    | Boolean _ -> "Bool"
    | Stmt _ -> "Stmt")
    (prog_to_parseable_str trip.prog)
    (form_to_parseable_str trip.post)

let ctrip_tostr (ctrip : contextualized_triple) =
  match ctrip.context with
  | [] -> trip_tostr ctrip.trip
  | _ ->
      Printf.sprintf "[%s] |- %s"
        (String.concat ", " (List.map trip_tostr ctrip.context))
        (trip_tostr ctrip.trip)

let get_conclusion rule =
  match rule with
  | Const ctrip -> ctrip
  | True ctrip -> ctrip
  | False ctrip -> ctrip
  | Skip ctrip -> ctrip
  | Var ctrip -> ctrip
  | Not (ctrip, _) -> ctrip
  | UnApp (ctrip, _) -> ctrip
  | BinApp (ctrip, _, _) -> ctrip
  | Plus (ctrip, _, _) -> ctrip
  | UnaryMinus (ctrip, _) -> ctrip
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
  | Const ctrip -> (
      match ctrip.trip.prog with
      | Term (Numeric _) -> Printf.sprintf "Int: -> %s" (ctrip_tostr ctrip)
      | Term (Bitvec _) -> Printf.sprintf "Bitv: -> %s" (ctrip_tostr ctrip)
      | _ -> raise Proof_Contents_Mismatch)
  | True ctrip -> Printf.sprintf "True: -> %s" (ctrip_tostr ctrip)
  | False ctrip -> Printf.sprintf "False: -> %s" (ctrip_tostr ctrip)
  | Skip ctrip -> Printf.sprintf "Skip: -> %s" (ctrip_tostr ctrip)
  | Var ctrip -> Printf.sprintf "Var: -> %s" (ctrip_tostr ctrip)
  | UnApp (conc, pf) -> (
      match conc.trip.prog with
      | Term (Bitvec (BitvUnApp (Minus, _))) ->
          Printf.sprintf "%s\nMinus: %s -> %s" (ruleApp_tostr pf)
            (ctrip_tostr (get_conclusion pf))
            (ctrip_tostr conc)
      | _ -> raise Proof_Contents_Mismatch)
  | BinApp (conc, lpf, rpf) -> (
      match conc.trip.prog with
      | Term (Bitvec (BinApp (Plus, _, _))) ->
          Printf.sprintf "%s\n%s\nBvAdd: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | Term (Bitvec (BinApp (Mult, _, _))) ->
          Printf.sprintf "%s\n%s\nBvMult: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | Term (Bitvec (BinApp (Sub, _, _))) ->
          Printf.sprintf "%s\n%s\nBvSub: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | Term (Bitvec (BinApp (Or, _, _))) ->
          Printf.sprintf "%s\n%s\nBvOr: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | Term (Bitvec (BinApp (Xor, _, _))) ->
          Printf.sprintf "%s\n%s\nBvXor: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | Term (Bitvec (BinApp (And, _, _))) ->
          Printf.sprintf "%s\n%s\nBvAnd: %s, %s -> %s" (ruleApp_tostr lpf)
            (ruleApp_tostr rpf)
            (ctrip_tostr (get_conclusion lpf))
            (ctrip_tostr (get_conclusion rpf))
            (ctrip_tostr conc)
      | _ -> raise Proof_Contents_Mismatch)
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
  | UnaryMinus (conc, pf) ->
      Printf.sprintf "%s\nPlus: %s -> %s" (ruleApp_tostr pf)
        (ctrip_tostr (get_conclusion pf))
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

let rec is_correct rule =
  match rule with
  | Const _ -> true
  | True _ -> true
  | False _ -> true
  | Skip _ -> true
  | Var _ -> true
  | UnApp (_, pf) -> is_correct pf
  | BinApp (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | Not (_, pf) -> is_correct pf
  | Plus (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | UnaryMinus (_, pf) -> is_correct pf
  | And (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | Or (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | Equals (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | Less (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | Assign (_, pf) -> is_correct pf
  | Seq (_, lpf, rpf) -> is_correct lpf && is_correct rpf
  | ITE (_, guardpf, thenpf, elsepf) ->
      is_correct guardpf && is_correct thenpf && is_correct elsepf
  | While (_, guardpf, bodypf) -> is_correct guardpf && is_correct bodypf
  | Weaken (_, pf, truth) -> Lazy.force truth && is_correct pf
  | GrmDisj (_, pfs) ->
      List.fold_left (fun bol pf -> bol && is_correct pf) true pfs
  | ApplyHP _ -> true
  | HP (_, pfs) -> List.fold_left (fun bol pf -> bol && is_correct pf) true pfs
  | Adapt (_, pf) -> is_correct pf

(* Substitutes holes for formulae. *)

let plug_holes_trip (trip : triple) (length : int)
    (hole_map : ((string * variable list) * formula) list) =
  match trip.prog with
  | Term (Numeric (NNTerm n)) ->
      {
        pre = sub_holes (bool_finite_vs_transformer length trip.pre) hole_map;
        prog =
          Term
            (Numeric
               (NNTerm (sub_hole_nterm (transform_int_nterm n length) hole_map)));
        post = sub_holes (bool_finite_vs_transformer length trip.post) hole_map;
      }
  | Term (Bitvec (BitvNTerm n)) ->
      {
        pre = sub_holes (bool_finite_vs_transformer length trip.pre) hole_map;
        prog =
          Term
            (Bitvec
               (BitvNTerm
                  (sub_hole_nterm (transform_bitv_nterm n length) hole_map)));
        post = sub_holes (bool_finite_vs_transformer length trip.post) hole_map;
      }
  | Boolean (BNTerm n) ->
      {
        pre = sub_holes (bool_finite_vs_transformer length trip.pre) hole_map;
        prog =
          Boolean
            (BNTerm (sub_hole_nterm (transform_bool_nterm n length) hole_map));
        post = sub_holes (bool_finite_vs_transformer length trip.post) hole_map;
      }
  | Stmt (SNTerm n) ->
      {
        pre = sub_holes (bool_finite_vs_transformer length trip.pre) hole_map;
        prog =
          Stmt
            (SNTerm (sub_hole_nterm (transform_stmt_nterm n length) hole_map));
        post = sub_holes (bool_finite_vs_transformer length trip.post) hole_map;
      }
  | _ ->
      {
        pre = sub_holes (bool_finite_vs_transformer length trip.pre) hole_map;
        prog = prog_finite_vs_transformer trip.prog length;
        post = sub_holes (bool_finite_vs_transformer length trip.post) hole_map;
      }

let plug_holes_ctrip (ctrip : contextualized_triple) (length : int)
    (hole_map : ((string * variable list) * formula) list) :
    contextualized_triple =
  {
    context =
      List.map (fun trip -> plug_holes_trip trip length hole_map) ctrip.context;
    trip = plug_holes_trip ctrip.trip length hole_map;
  }

let rec plug_holes (rule : ruleApp) (length : int)
    (hole_map : ((string * variable list) * formula) list) =
  match rule with
  | Const ctrip -> Const (plug_holes_ctrip ctrip length hole_map)
  | True ctrip -> True (plug_holes_ctrip ctrip length hole_map)
  | False ctrip -> False (plug_holes_ctrip ctrip length hole_map)
  | Skip ctrip -> Skip (plug_holes_ctrip ctrip length hole_map)
  | Var ctrip -> Var (plug_holes_ctrip ctrip length hole_map)
  | UnApp (ctrip, pf) ->
      UnApp
        (plug_holes_ctrip ctrip length hole_map, plug_holes pf length hole_map)
  | BinApp (ctrip, lpf, rpf) ->
      BinApp
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | Not (ctrip, pf) ->
      Not (plug_holes_ctrip ctrip length hole_map, plug_holes pf length hole_map)
  | Plus (ctrip, lpf, rpf) ->
      Plus
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | UnaryMinus (ctrip, pf) ->
      UnaryMinus
        (plug_holes_ctrip ctrip length hole_map, plug_holes pf length hole_map)
  | And (ctrip, lpf, rpf) ->
      And
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | Or (ctrip, lpf, rpf) ->
      Or
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | Equals (ctrip, lpf, rpf) ->
      Equals
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | Less (ctrip, lpf, rpf) ->
      Less
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | Assign (ctrip, pf) ->
      Assign
        (plug_holes_ctrip ctrip length hole_map, plug_holes pf length hole_map)
  | Seq (ctrip, lpf, rpf) ->
      Seq
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes lpf length hole_map,
          plug_holes rpf length hole_map )
  | ITE (ctrip, branch_pf, then_pf, else_pf) ->
      ITE
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes branch_pf length hole_map,
          plug_holes then_pf length hole_map,
          plug_holes else_pf length hole_map )
  | While (ctrip, guard_pf, body_pf) ->
      While
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes guard_pf length hole_map,
          plug_holes body_pf length hole_map )
  | Weaken (ctrip, pf, truth) ->
      Weaken
        ( plug_holes_ctrip ctrip length hole_map,
          plug_holes pf length hole_map,
          truth )
  | GrmDisj (ctrip, pfs) ->
      GrmDisj
        ( plug_holes_ctrip ctrip length hole_map,
          List.map (fun pf -> plug_holes pf length hole_map) pfs )
  | ApplyHP ctrip -> ApplyHP (plug_holes_ctrip ctrip length hole_map)
  | HP (ctrip, pfs) ->
      HP
        ( plug_holes_ctrip ctrip length hole_map,
          List.map (fun pf -> plug_holes pf length hole_map) pfs )
  | Adapt (ctrip, pf) ->
      Adapt
        (plug_holes_ctrip ctrip length hole_map, plug_holes pf length hole_map)
