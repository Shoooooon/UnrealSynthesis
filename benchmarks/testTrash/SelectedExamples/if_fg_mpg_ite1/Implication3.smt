;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const x_finitevscpy_4 Int)
(declare-const x_finitevscpy_5 Int)
(declare-const x_finitevscpy_6 Int)
(declare-const x_finitevscpy_7 Int)
(declare-const x_finitevscpy_8 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const y_finitevscpy_2 Int)
(declare-const y_finitevscpy_3 Int)
(declare-const y_finitevscpy_4 Int)
(declare-const y_finitevscpy_5 Int)
(declare-const y_finitevscpy_6 Int)
(declare-const y_finitevscpy_7 Int)
(declare-const y_finitevscpy_8 Int)
(declare-const z_finitevscpy_1 Int)
(declare-const z_finitevscpy_2 Int)
(declare-const z_finitevscpy_3 Int)
(declare-const z_finitevscpy_4 Int)
(declare-const z_finitevscpy_5 Int)
(declare-const z_finitevscpy_6 Int)
(declare-const z_finitevscpy_7 Int)
(declare-const z_finitevscpy_8 Int)
(assert
(not
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 0)) (= y_finitevscpy_1 0)) (= z_finitevscpy_1 0)) (= x_finitevscpy_2 (- 3))) (= y_finitevscpy_2 (- 6))) (= z_finitevscpy_2 (- 9))) (= x_finitevscpy_3 (- 1))) (= y_finitevscpy_3 0)) (= z_finitevscpy_3 0)) (= x_finitevscpy_4 (- 1))) (= y_finitevscpy_4 1)) (= z_finitevscpy_4 3)) (= x_finitevscpy_5 (- 1))) (= y_finitevscpy_5 3)) (= z_finitevscpy_5 1)) (= x_finitevscpy_6 1)) (= y_finitevscpy_6 (- 1))) (= z_finitevscpy_6 1)) (= x_finitevscpy_7 (- 3))) (= y_finitevscpy_7 0)) (= z_finitevscpy_7 (- 1))) (= x_finitevscpy_8 0)) (= y_finitevscpy_8 1)) (= z_finitevscpy_8 2)) (not (and (and (and (and (and (and (and (and true (= z_finitevscpy_1 1)) (= z_finitevscpy_2 0)) (= z_finitevscpy_3 1)) (= z_finitevscpy_4 4)) (= z_finitevscpy_5 4)) (= z_finitevscpy_6 2)) (= z_finitevscpy_7 0)) (= z_finitevscpy_8 1))))
)
 )
(check-sat)
(exit)