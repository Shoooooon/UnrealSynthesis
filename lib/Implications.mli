open Logic.Formula
open Logic.Variable

(* Returns a function that can be used to check implication whether or not holes are present.
   Allows separate instances for convenient memoization/maintaining state between invocations.
   This will help disambiguate holes when we synthesize MGFs/invariants.
   The first output is a function that takes (a,b) and checks if a->b lazily.
   The second output gives you the values to fill any holes. *)
val implicator_synth :
  unit ->
  (formula -> formula -> bool Lazy.t)
  * ((string * variable list) * formula) list Lazy.t
