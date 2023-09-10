type synthMode = HOLE_SYNTH | INVS_SPECIFIED
type formMode = SIMPLE | FINITE_VECTOR_STATE | VECTOR_STATE

(* Given a UL triple and a mode indicating whether holes are present in the proof, reutrns a proof of the triple *)
val prove :
  Proofrules.ProofRule.triple ->
  synthMode ->
  formMode ->
  Proofrules.ProofRule.ruleApp
