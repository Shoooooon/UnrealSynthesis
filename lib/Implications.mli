open Logic.Formula
open Logic.Variable

(* We have many different implication handlers depending on the solver you want to use and the structure of your formula.
   The implies function registers and implication and returns a lazy bool telling you if the implication is true (or whether all implications registered so far are satisfiable when holes are involved).
   The get_hole_values is a lazy of a map from holes to synthesized values for successfully synthesized holes.*)
module type ImplicationHandler = sig
  val implies : formula -> formula -> bool Lazy.t
  val hole_values : ((string * variable list) * formula) list Lazy.t
end

(* Module for strategies for writing SyGuS grammars for the synthesis of hole values. *)
module type HoleSynthStrat = sig
  val bool_hole_to_sygus_grammar : string * variable list -> string
end

module type VCSimpStrat = sig
  val deconjunctivizer : formula -> formula -> (formula * VS.t) list
  val deconjunctivizer_rhs : formula -> VS.t -> (formula * VS.t) list * VS.t
end

(* Hole synthesis to sygus grammar options. *)
module BitvecGrammarStrat : HoleSynthStrat
module UnconstrainedGrammarStrat : HoleSynthStrat

(* VC simplification options. *)
module No_Simp : VCSimpStrat
module Quantify_Collect : VCSimpStrat

(* IMPLICATION MODULES *)
module NoHoleSimpleImplicatorZ3 (_ : VCSimpStrat) : ImplicationHandler

module HoleSynthSimpleImplicatorCVC5 (_ : HoleSynthStrat) (_ : VCSimpStrat) :
  ImplicationHandler

module NoHoleVectorStateImplicatorVampire (_ : VCSimpStrat) : ImplicationHandler

val finite_holes_implicator :
  int ->
  (string * variable list -> string) ->
  (formula -> VS.t -> (formula * VS.t) list * VS.t) ->
  (module ImplicationHandler)

val finite_holeless_implicator :
  int ->
  (formula -> formula -> (formula * VS.t) list) ->
  (module ImplicationHandler)
