;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and (and (and true (= x_finitevscpy_1 12)) (= y_finitevscpy_1 18)) (= z_finitevscpy_1 (- 15))) true)
)
 )
(check-sat)
(exit)