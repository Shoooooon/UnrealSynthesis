type proofMode = HOLE_SYNTH | INVS_SPECIFIED

(* Given a UL triple and a mode indicating whether holes are present in the proof, reutrns a proof of the triple *)
val prove : ProofRule.triple -> proofMode -> ProofRule.ruleApp
