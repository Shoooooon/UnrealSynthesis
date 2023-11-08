;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_2 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const y_finitevscpy_2 Int)
(assert
(not
(=> true (or (= k_finitevscpy_2 0) (or (= k_finitevscpy_2 1) (or (= k_finitevscpy_2 x_finitevscpy_2) (or (= k_finitevscpy_2 y_finitevscpy_2) (= k_finitevscpy_2 k_finitevscpy_2))))))
)
 )
(check-sat)
(exit)