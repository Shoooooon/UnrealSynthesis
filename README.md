## How to run

To run, make sure z3 and cvc5 are installed and type the following:

> dune exec ULSynth \<filename\>

Note the file passed should contain the triple you are trying to synthesize and the corresponding grammar. 

For example:

>> [] {|true|} Stmt (:= x 0) {|false|}

>> [Int N : [1] : None] {|true|} Int (+ 0 1) {|false|}

>> [Bool B : [(= x 1), (or Nonterm B (= x 0))] : Some ([(Int e_t, Int e_t_2) ; (Bool b_t, Bool b_t_2)] : (Hole : hole [Bool b_t, Int x]))] {|(= x 1)|} Bool Nonterm B {|b_t|}" would all be acceptable inputs.


Also, there are a lot of tests in the test directory that can be run with 

>dune test

