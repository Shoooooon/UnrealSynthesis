;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(assert
(not
(=> (and true (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0))) (or (= (+ 1 1) 0) (< 1 (+ 1 1))))
)
 )
(check-sat)
(exit)