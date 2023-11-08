;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(assert
(not
(=> true true)
)
 )
(check-sat)
(exit)