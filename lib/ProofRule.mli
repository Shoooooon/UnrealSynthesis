open Formula
open Program

type proofMode = HOLE_SYNTH | INVS_SPECIFIED

(* Represents a complete UL triple *)
type triple = { pre : formula; prog : program; post : formula }

(* Represents a UL triple with associated context *)
type contextualized_triple = { context : triple list; trip : triple }

(* Represents a UL Proof *)
type ruleApp

(* Given a proof, converts it to a string *)
val ruleApp_tostr : ruleApp -> string

(* Given a UL triple and a mode indicating whether holes are present in the proof, reutrns a proof of the triple *)
val prove : triple -> proofMode -> ruleApp * (unit -> string)
