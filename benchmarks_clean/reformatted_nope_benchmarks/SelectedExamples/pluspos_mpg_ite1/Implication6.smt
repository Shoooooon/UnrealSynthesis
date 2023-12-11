;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> true (or (= 0 0) (or (= 0 1) (or (= 0 x_finitevscpy_1) (or (= 0 y_finitevscpy_1) (= 0 z_finitevscpy_1))))))
)
 )
(check-sat)
(exit)