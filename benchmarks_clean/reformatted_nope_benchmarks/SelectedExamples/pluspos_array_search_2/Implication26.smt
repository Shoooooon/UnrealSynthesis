;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_3 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const y_finitevscpy_3 Int)
(assert
(not
(=> true (or (= 0 0) (or (= 0 1) (or (= 0 x_finitevscpy_3) (or (= 0 y_finitevscpy_3) (= 0 k_finitevscpy_3))))))
)
 )
(check-sat)
(exit)