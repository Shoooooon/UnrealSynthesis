open Logic.Formula
open Logic.Variable

(* We have many different implication handlers depending on the solver you want to use and the structure of your formula.
   The implies function registers and implication and returns a lazy bool telling you if the implication is true (or whether all implications registered so far are satisfiable when holes are involved).
   The get_hole_values is a lazy of a map from holes to synthesized values for successfully synthesized holes.*)
module type ImplicationHandler = sig
  val implies : formula -> formula -> bool Lazy.t
  val hole_values : ((string * variable list) * formula) list Lazy.t
end

(* IMPLICATION MODULES *)
module NoHoleSimpleImplicatorZ3 () : ImplicationHandler
module HoleSynthSimpleImplicatorCVC5 () : ImplicationHandler
