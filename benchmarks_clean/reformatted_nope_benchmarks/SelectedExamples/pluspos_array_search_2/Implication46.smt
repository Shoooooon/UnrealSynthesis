;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Int)
(declare-const fresh1_finitevscpy_2 Int)
(declare-const fresh1_finitevscpy_3 Int)
(declare-const fresh1_finitevscpy_4 Int)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const fresh2_finitevscpy_2 Int)
(declare-const fresh2_finitevscpy_3 Int)
(declare-const fresh2_finitevscpy_4 Int)
(declare-const k_finitevscpy_1 Int)
(declare-const k_finitevscpy_2 Int)
(declare-const k_finitevscpy_3 Int)
(declare-const k_finitevscpy_4 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const x_finitevscpy_4 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const y_finitevscpy_2 Int)
(declare-const y_finitevscpy_3 Int)
(declare-const y_finitevscpy_4 Int)
(assert
(not
(=> (and true (and (and (or (= fresh1_finitevscpy_1 0) (or (= fresh1_finitevscpy_1 1) (or (= fresh1_finitevscpy_1 x_finitevscpy_1) (or (= fresh1_finitevscpy_1 y_finitevscpy_1) (= fresh1_finitevscpy_1 k_finitevscpy_1))))) (and (or (= fresh1_finitevscpy_2 0) (or (= fresh1_finitevscpy_2 1) (or (= fresh1_finitevscpy_2 x_finitevscpy_2) (or (= fresh1_finitevscpy_2 y_finitevscpy_2) (= fresh1_finitevscpy_2 k_finitevscpy_2))))) (and (or (= fresh1_finitevscpy_3 0) (or (= fresh1_finitevscpy_3 1) (or (= fresh1_finitevscpy_3 x_finitevscpy_3) (or (= fresh1_finitevscpy_3 y_finitevscpy_3) (= fresh1_finitevscpy_3 k_finitevscpy_3))))) (or (= fresh1_finitevscpy_4 0) (or (= fresh1_finitevscpy_4 1) (or (= fresh1_finitevscpy_4 x_finitevscpy_4) (or (= fresh1_finitevscpy_4 y_finitevscpy_4) (= fresh1_finitevscpy_4 k_finitevscpy_4)))))))) (and (or (= fresh2_finitevscpy_1 0) (or (= fresh2_finitevscpy_1 1) (or (= fresh2_finitevscpy_1 x_finitevscpy_1) (or (= fresh2_finitevscpy_1 y_finitevscpy_1) (= fresh2_finitevscpy_1 k_finitevscpy_1))))) (and (or (= fresh2_finitevscpy_2 0) (or (= fresh2_finitevscpy_2 1) (or (= fresh2_finitevscpy_2 x_finitevscpy_2) (or (= fresh2_finitevscpy_2 y_finitevscpy_2) (= fresh2_finitevscpy_2 k_finitevscpy_2))))) (and (or (= fresh2_finitevscpy_3 0) (or (= fresh2_finitevscpy_3 1) (or (= fresh2_finitevscpy_3 x_finitevscpy_3) (or (= fresh2_finitevscpy_3 y_finitevscpy_3) (= fresh2_finitevscpy_3 k_finitevscpy_3))))) (or (= fresh2_finitevscpy_4 0) (or (= fresh2_finitevscpy_4 1) (or (= fresh2_finitevscpy_4 x_finitevscpy_4) (or (= fresh2_finitevscpy_4 y_finitevscpy_4) (= fresh2_finitevscpy_4 k_finitevscpy_4)))))))))) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ k_finitevscpy_3 k_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ k_finitevscpy_3 y_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ y_finitevscpy_3 y_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ k_finitevscpy_3 x_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ y_finitevscpy_3 x_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ x_finitevscpy_3 x_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ 1 k_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ 1 y_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) (+ 1 x_finitevscpy_3)) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) 2) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) k_finitevscpy_3) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) y_finitevscpy_3) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) x_finitevscpy_3) (or (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) 1) (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) 0))))))))))))))))
)
 )
(check-sat)
(exit)