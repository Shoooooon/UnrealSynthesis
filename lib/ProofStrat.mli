type synthMode = HOLE_SYNTH | INVS_SPECIFIED
type formMode = SIMPLE | FINITE_VECTOR_STATE | VECTOR_STATE
type holeGuideMode = NONE | BITVEC
type vcSimplificationMode = NO_SIMP | QUANTIFY_COLLECT
type expressionMode = STMTS | EXPRESSIONS_ONLY
(* Indicates whether to use the optimization for expressions and fixed examples. *)

(* Given a UL triple and a mode indicating whether holes are present in the proof, reutrns a proof of the triple *)
val prove :
Proofrules.ProofRule.triple list ->
  Proofrules.ProofRule.triple ->
  synthMode ->
  formMode ->
  holeGuideMode ->
  vcSimplificationMode ->
  expressionMode ->
  Proofrules.ProofRule.ruleApp
