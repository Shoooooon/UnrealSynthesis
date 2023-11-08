;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_4 Int)
(declare-const x_finitevscpy_4 Int)
(declare-const y_finitevscpy_4 Int)
(assert
(not
(=> true (or (= x_finitevscpy_4 0) (or (= x_finitevscpy_4 1) (or (= x_finitevscpy_4 x_finitevscpy_4) (or (= x_finitevscpy_4 y_finitevscpy_4) (= x_finitevscpy_4 k_finitevscpy_4))))))
)
 )
(check-sat)
(exit)