;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh10 Int)
(declare-const fresh11 Int)
(declare-const fresh12 Int)
(declare-const fresh13 Int)
(declare-const fresh14 Int)
(declare-const fresh15 Int)
(declare-const fresh16 Int)
(declare-const fresh17 Int)
(declare-const fresh18 Int)
(declare-const fresh19 Int)
(declare-const fresh20 Int)
(declare-const fresh5 Int)
(declare-const fresh6 Int)
(declare-const fresh7 Int)
(declare-const fresh8 Int)
(declare-const fresh9 Int)
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
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 (- 1))) (= y_finitevscpy_1 (- 1))) (= k_finitevscpy_1 (- 2))) (= x_finitevscpy_2 0)) (= y_finitevscpy_2 2)) (= k_finitevscpy_2 1)) (= x_finitevscpy_3 (- 1))) (= y_finitevscpy_3 0)) (= k_finitevscpy_3 1)) (= x_finitevscpy_4 (- 2))) (= y_finitevscpy_4 (- 1))) (= k_finitevscpy_4 (- 3))) (and (and (or (= fresh8 0) (or (= fresh8 1) (or (= fresh8 x_finitevscpy_1) (or (= fresh8 y_finitevscpy_1) (= fresh8 k_finitevscpy_1))))) (and (or (= fresh7 0) (or (= fresh7 1) (or (= fresh7 x_finitevscpy_2) (or (= fresh7 y_finitevscpy_2) (= fresh7 k_finitevscpy_2))))) (and (or (= fresh6 0) (or (= fresh6 1) (or (= fresh6 x_finitevscpy_3) (or (= fresh6 y_finitevscpy_3) (= fresh6 k_finitevscpy_3))))) (or (= fresh5 0) (or (= fresh5 1) (or (= fresh5 x_finitevscpy_4) (or (= fresh5 y_finitevscpy_4) (= fresh5 k_finitevscpy_4)))))))) (and (and (or (= fresh12 0) (or (= fresh12 1) (or (= fresh12 x_finitevscpy_1) (or (= fresh12 y_finitevscpy_1) (= fresh12 k_finitevscpy_1))))) (and (or (= fresh11 0) (or (= fresh11 1) (or (= fresh11 x_finitevscpy_2) (or (= fresh11 y_finitevscpy_2) (= fresh11 k_finitevscpy_2))))) (and (or (= fresh10 0) (or (= fresh10 1) (or (= fresh10 x_finitevscpy_3) (or (= fresh10 y_finitevscpy_3) (= fresh10 k_finitevscpy_3))))) (or (= fresh9 0) (or (= fresh9 1) (or (= fresh9 x_finitevscpy_4) (or (= fresh9 y_finitevscpy_4) (= fresh9 k_finitevscpy_4)))))))) (and (and (or (= fresh16 0) (or (= fresh16 1) (or (= fresh16 x_finitevscpy_1) (or (= fresh16 y_finitevscpy_1) (= fresh16 k_finitevscpy_1))))) (and (or (= fresh15 0) (or (= fresh15 1) (or (= fresh15 x_finitevscpy_2) (or (= fresh15 y_finitevscpy_2) (= fresh15 k_finitevscpy_2))))) (and (or (= fresh14 0) (or (= fresh14 1) (or (= fresh14 x_finitevscpy_3) (or (= fresh14 y_finitevscpy_3) (= fresh14 k_finitevscpy_3))))) (or (= fresh13 0) (or (= fresh13 1) (or (= fresh13 x_finitevscpy_4) (or (= fresh13 y_finitevscpy_4) (= fresh13 k_finitevscpy_4)))))))) (and (or (= fresh20 0) (or (= fresh20 1) (or (= fresh20 x_finitevscpy_1) (or (= fresh20 y_finitevscpy_1) (= fresh20 k_finitevscpy_1))))) (and (or (= fresh19 0) (or (= fresh19 1) (or (= fresh19 x_finitevscpy_2) (or (= fresh19 y_finitevscpy_2) (= fresh19 k_finitevscpy_2))))) (and (or (= fresh18 0) (or (= fresh18 1) (or (= fresh18 x_finitevscpy_3) (or (= fresh18 y_finitevscpy_3) (= fresh18 k_finitevscpy_3))))) (or (= fresh17 0) (or (= fresh17 1) (or (= fresh17 x_finitevscpy_4) (or (= fresh17 y_finitevscpy_4) (= fresh17 k_finitevscpy_4)))))))))))) (not (and (and (and (and true (or (or false (and (and (not (not (< fresh8 fresh12))) true) (= fresh20 0))) (and (and (not (< fresh8 fresh12)) true) (= fresh16 0)))) (or (or false (and (and (not (not (< fresh7 fresh11))) true) (= fresh19 2))) (and (and (not (< fresh7 fresh11)) true) (= fresh15 2)))) (or (or false (and (and (not (not (< fresh6 fresh10))) true) (= fresh18 3))) (and (and (not (< fresh6 fresh10)) true) (= fresh14 3)))) (or (or false (and (and (not (not (< fresh5 fresh9))) true) (= fresh17 1))) (and (and (not (< fresh5 fresh9)) true) (= fresh13 1))))))
)
 )
(check-sat)
(exit)