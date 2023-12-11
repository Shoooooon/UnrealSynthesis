;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Int)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(assert
(not
(=> (and true (and (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh1_finitevscpy_1 0) (< 1 fresh1_finitevscpy_1))) (and (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh2_finitevscpy_1 0) (< 1 fresh2_finitevscpy_1))) (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0))))) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) 0) (< 1 (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1))))
)
 )
(check-sat)
(exit)