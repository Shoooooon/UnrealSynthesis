;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const k_finitevscpy_2 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const y_finitevscpy_2 Int)
(assert
(not
(=> true (or (= 0 0) (or (= 0 1) (or (= 0 x_finitevscpy_2) (or (= 0 y_finitevscpy_2) (= 0 k_finitevscpy_2))))))
)
 )
(check-sat)
(exit)