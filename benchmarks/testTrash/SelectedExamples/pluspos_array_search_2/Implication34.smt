;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_3 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const y_finitevscpy_3 Int)
(assert
(not
(=> true (or (= 1 0) (or (= 1 1) (or (= 1 x_finitevscpy_3) (or (= 1 y_finitevscpy_3) (= 1 k_finitevscpy_3))))))
)
 )
(check-sat)
(exit)