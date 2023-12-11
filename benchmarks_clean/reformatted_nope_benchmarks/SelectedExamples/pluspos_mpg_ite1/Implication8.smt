;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> true (or (= 1 0) (or (= 1 1) (or (= 1 x_finitevscpy_1) (or (= 1 y_finitevscpy_1) (= 1 z_finitevscpy_1))))))
)
 )
(check-sat)
(exit)