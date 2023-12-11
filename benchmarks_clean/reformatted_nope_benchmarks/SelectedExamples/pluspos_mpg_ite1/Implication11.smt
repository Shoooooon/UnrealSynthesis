;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(assert
(not
(=> (and true (and true true)) true)
)
 )
(check-sat)
(exit)