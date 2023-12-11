# WULDO
Wuldo is a proof synthesizer for weakest-pre Unrealizability Logic. 
Given a grammar, an unrealizability triple, and some optional invariants, Wuldo can synthesize a proof of the triple over the grammar.

## How to run

To run, make sure z3, cvc5, and vampire are installed and callable from the command line as "z3", "cvc5", and "vampire" respectively. Install dune as well. Specify your UL query as in the benchmarks files. Then type the following:

> dune exec -- ULSynth \<filename\>

If you want to prove a triple over vector-states, set the -vectors flag before the filename:

> dune exec -- ULSynth -vectors \<filename\>

If you will need to synthesize holes (e.g., nonterminal summaries), set the -holes flag before the filename:

> dune exec -- ULSynth -holes \<filename\>

For help, type the following:

> dune exec -- ULSynth --help

Note the file passed should contain the triple you are trying to synthesize and the corresponding grammar. 

For example:

>> [] {|true|} Stmt (:= x 0) {|false|}

>> [Int N : [1] : None] {|true|} Int (+ 0 1) {|false|}

>> [Bool B : [(= x 1), (or Nonterm B (= x 0))] : Some ([(Int e_t, Int e_t_2) ; (Bool b_t, Bool b_t_2)] : (Hole : hole [Bool b_t, Int x]))] {|(= x 1)|} Bool Nonterm B {|b_t|}" would all be acceptable inputs.


Also, there are a lot of tests in the test directory that can be run with 

>dune test

