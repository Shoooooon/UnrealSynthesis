;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and (and (and (and true (= x_finitevscpy_1 0)) (= y_finitevscpy_1 0)) (= z_finitevscpy_1 0)) (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh1_finitevscpy_1 0) (< 1 fresh1_finitevscpy_1)))) (not (and true (= fresh1_finitevscpy_1 1))))
)
 )
(check-sat)
(exit)