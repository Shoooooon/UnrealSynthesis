;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh21 Int)
(declare-const fresh22 Int)
(declare-const fresh23 Int)
(declare-const fresh24 Int)
(declare-const fresh25 Int)
(declare-const fresh26 Int)
(declare-const fresh27 Int)
(declare-const fresh28 Int)
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
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 (- 1))) (= y_finitevscpy_1 (- 1))) (= k_finitevscpy_1 (- 2))) (= x_finitevscpy_2 0)) (= y_finitevscpy_2 2)) (= k_finitevscpy_2 1)) (= x_finitevscpy_3 (- 1))) (= y_finitevscpy_3 0)) (= k_finitevscpy_3 1)) (= x_finitevscpy_4 (- 2))) (= y_finitevscpy_4 (- 1))) (= k_finitevscpy_4 (- 3))) (and (and (or (= fresh24 0) (or (= fresh24 1) (or (= fresh24 x_finitevscpy_1) (or (= fresh24 y_finitevscpy_1) (= fresh24 k_finitevscpy_1))))) (and (or (= fresh23 0) (or (= fresh23 1) (or (= fresh23 x_finitevscpy_2) (or (= fresh23 y_finitevscpy_2) (= fresh23 k_finitevscpy_2))))) (and (or (= fresh22 0) (or (= fresh22 1) (or (= fresh22 x_finitevscpy_3) (or (= fresh22 y_finitevscpy_3) (= fresh22 k_finitevscpy_3))))) (or (= fresh21 0) (or (= fresh21 1) (or (= fresh21 x_finitevscpy_4) (or (= fresh21 y_finitevscpy_4) (= fresh21 k_finitevscpy_4)))))))) (and (or (= fresh28 0) (or (= fresh28 1) (or (= fresh28 x_finitevscpy_1) (or (= fresh28 y_finitevscpy_1) (= fresh28 k_finitevscpy_1))))) (and (or (= fresh27 0) (or (= fresh27 1) (or (= fresh27 x_finitevscpy_2) (or (= fresh27 y_finitevscpy_2) (= fresh27 k_finitevscpy_2))))) (and (or (= fresh26 0) (or (= fresh26 1) (or (= fresh26 x_finitevscpy_3) (or (= fresh26 y_finitevscpy_3) (= fresh26 k_finitevscpy_3))))) (or (= fresh25 0) (or (= fresh25 1) (or (= fresh25 x_finitevscpy_4) (or (= fresh25 y_finitevscpy_4) (= fresh25 k_finitevscpy_4)))))))))) (not (and (and (and (and true (= (+ fresh24 fresh28) 0)) (= (+ fresh23 fresh27) 2)) (= (+ fresh22 fresh26) 3)) (= (+ fresh21 fresh25) 1))))
)
 )
(check-sat)
(exit)