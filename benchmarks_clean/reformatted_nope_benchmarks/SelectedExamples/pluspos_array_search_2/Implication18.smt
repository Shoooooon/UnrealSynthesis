;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_3 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const y_finitevscpy_3 Int)
(assert
(not
(=> true (or (= x_finitevscpy_3 0) (or (= x_finitevscpy_3 1) (or (= x_finitevscpy_3 x_finitevscpy_3) (or (= x_finitevscpy_3 y_finitevscpy_3) (= x_finitevscpy_3 k_finitevscpy_3))))))
)
 )
(check-sat)
(exit)