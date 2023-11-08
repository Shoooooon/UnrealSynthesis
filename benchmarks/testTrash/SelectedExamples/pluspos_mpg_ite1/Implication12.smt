;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Int)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and true (and (or (= fresh1_finitevscpy_1 0) (or (= fresh1_finitevscpy_1 1) (or (= fresh1_finitevscpy_1 x_finitevscpy_1) (or (= fresh1_finitevscpy_1 y_finitevscpy_1) (= fresh1_finitevscpy_1 z_finitevscpy_1))))) (or (= fresh2_finitevscpy_1 0) (or (= fresh2_finitevscpy_1 1) (or (= fresh2_finitevscpy_1 x_finitevscpy_1) (or (= fresh2_finitevscpy_1 y_finitevscpy_1) (= fresh2_finitevscpy_1 z_finitevscpy_1))))))) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ z_finitevscpy_1 z_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ z_finitevscpy_1 y_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ y_finitevscpy_1 y_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ z_finitevscpy_1 x_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ y_finitevscpy_1 x_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ x_finitevscpy_1 x_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ 1 z_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ 1 y_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) (+ 1 x_finitevscpy_1)) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) 2) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) z_finitevscpy_1) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) y_finitevscpy_1) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) x_finitevscpy_1) (or (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) 1) (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) 0))))))))))))))))
)
 )
(check-sat)
(exit)