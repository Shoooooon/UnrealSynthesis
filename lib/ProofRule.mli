open Logic.Formula
open Programs.Program

(* Represents a complete UL triple *)
type triple = { pre : formula; prog : program; post : formula }

(* Represents an incomplete UL triple *)
type triple_no_pre = { prog : program; post : formula }

(* Given a triple, converts it to a string *)
val trip_tostr : triple -> string

(* Represents a complete UL triple with associated context *)
type contextualized_triple = { context : triple list; trip : triple }

(* Represents an incomplete UL triple with associated context *)
type contextualized_triple_no_pre = {
  context : triple list;
  trip : triple_no_pre;
}

(* Represents a UL Proof *)
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

(* Given a proof, converts it to a string *)
val ruleApp_tostr : ruleApp -> string

(* Gets conclusion of a given proof rule. *)
val get_conclusion : ruleApp -> contextualized_triple

(* Given a proof and a list of ways to fill holes, fills the holes accordingly.*)
val plug_holes : ruleApp -> ((string * Logic.Variable.variable list) * formula) list -> ruleApp