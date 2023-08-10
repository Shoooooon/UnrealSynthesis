type synthMode = HOLE_SYNTH | INVS_SPECIFIED
type formMode = SIMPLE | VECTOR_STATE

(* Given a UL triple and a mode indicating whether holes are present in the proof, reutrns a proof of the triple *)
val prove : ProofRule.triple -> synthMode -> formMode -> ProofRule.ruleApp
