;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh29 Int)
(declare-const fresh30 Int)
(declare-const fresh31 Int)
(declare-const fresh32 Int)
(declare-const fresh33 Int)
(declare-const fresh34 Int)
(declare-const fresh35 Int)
(declare-const fresh36 Int)
(declare-const fresh37 Int)
(declare-const fresh38 Int)
(declare-const fresh39 Int)
(declare-const fresh40 Int)
(declare-const fresh41 Int)
(declare-const fresh42 Int)
(declare-const fresh43 Int)
(declare-const fresh44 Int)
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
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 (- 1))) (= y_finitevscpy_1 (- 1))) (= k_finitevscpy_1 (- 2))) (= x_finitevscpy_2 0)) (= y_finitevscpy_2 2)) (= k_finitevscpy_2 1)) (= x_finitevscpy_3 (- 1))) (= y_finitevscpy_3 0)) (= k_finitevscpy_3 1)) (= x_finitevscpy_4 (- 2))) (= y_finitevscpy_4 (- 1))) (= k_finitevscpy_4 (- 3))) (and (and (or (= fresh32 0) (or (= fresh32 1) (or (= fresh32 x_finitevscpy_1) (or (= fresh32 y_finitevscpy_1) (= fresh32 k_finitevscpy_1))))) (and (or (= fresh31 0) (or (= fresh31 1) (or (= fresh31 x_finitevscpy_2) (or (= fresh31 y_finitevscpy_2) (= fresh31 k_finitevscpy_2))))) (and (or (= fresh30 0) (or (= fresh30 1) (or (= fresh30 x_finitevscpy_3) (or (= fresh30 y_finitevscpy_3) (= fresh30 k_finitevscpy_3))))) (or (= fresh29 0) (or (= fresh29 1) (or (= fresh29 x_finitevscpy_4) (or (= fresh29 y_finitevscpy_4) (= fresh29 k_finitevscpy_4)))))))) (and (and (or (= fresh36 0) (or (= fresh36 1) (or (= fresh36 x_finitevscpy_1) (or (= fresh36 y_finitevscpy_1) (= fresh36 k_finitevscpy_1))))) (and (or (= fresh35 0) (or (= fresh35 1) (or (= fresh35 x_finitevscpy_2) (or (= fresh35 y_finitevscpy_2) (= fresh35 k_finitevscpy_2))))) (and (or (= fresh34 0) (or (= fresh34 1) (or (= fresh34 x_finitevscpy_3) (or (= fresh34 y_finitevscpy_3) (= fresh34 k_finitevscpy_3))))) (or (= fresh33 0) (or (= fresh33 1) (or (= fresh33 x_finitevscpy_4) (or (= fresh33 y_finitevscpy_4) (= fresh33 k_finitevscpy_4)))))))) (and (and (or (= fresh40 (+ k_finitevscpy_1 k_finitevscpy_1)) (or (= fresh40 (+ k_finitevscpy_1 y_finitevscpy_1)) (or (= fresh40 (+ y_finitevscpy_1 y_finitevscpy_1)) (or (= fresh40 (+ k_finitevscpy_1 x_finitevscpy_1)) (or (= fresh40 (+ y_finitevscpy_1 x_finitevscpy_1)) (or (= fresh40 (+ x_finitevscpy_1 x_finitevscpy_1)) (or (= fresh40 (+ 1 k_finitevscpy_1)) (or (= fresh40 (+ 1 y_finitevscpy_1)) (or (= fresh40 (+ 1 x_finitevscpy_1)) (or (= fresh40 2) (or (= fresh40 k_finitevscpy_1) (or (= fresh40 y_finitevscpy_1) (or (= fresh40 x_finitevscpy_1) (or (= fresh40 1) (= fresh40 0))))))))))))))) (and (or (= fresh39 (+ k_finitevscpy_2 k_finitevscpy_2)) (or (= fresh39 (+ k_finitevscpy_2 y_finitevscpy_2)) (or (= fresh39 (+ y_finitevscpy_2 y_finitevscpy_2)) (or (= fresh39 (+ k_finitevscpy_2 x_finitevscpy_2)) (or (= fresh39 (+ y_finitevscpy_2 x_finitevscpy_2)) (or (= fresh39 (+ x_finitevscpy_2 x_finitevscpy_2)) (or (= fresh39 (+ 1 k_finitevscpy_2)) (or (= fresh39 (+ 1 y_finitevscpy_2)) (or (= fresh39 (+ 1 x_finitevscpy_2)) (or (= fresh39 2) (or (= fresh39 k_finitevscpy_2) (or (= fresh39 y_finitevscpy_2) (or (= fresh39 x_finitevscpy_2) (or (= fresh39 1) (= fresh39 0))))))))))))))) (and (or (= fresh38 (+ k_finitevscpy_3 k_finitevscpy_3)) (or (= fresh38 (+ k_finitevscpy_3 y_finitevscpy_3)) (or (= fresh38 (+ y_finitevscpy_3 y_finitevscpy_3)) (or (= fresh38 (+ k_finitevscpy_3 x_finitevscpy_3)) (or (= fresh38 (+ y_finitevscpy_3 x_finitevscpy_3)) (or (= fresh38 (+ x_finitevscpy_3 x_finitevscpy_3)) (or (= fresh38 (+ 1 k_finitevscpy_3)) (or (= fresh38 (+ 1 y_finitevscpy_3)) (or (= fresh38 (+ 1 x_finitevscpy_3)) (or (= fresh38 2) (or (= fresh38 k_finitevscpy_3) (or (= fresh38 y_finitevscpy_3) (or (= fresh38 x_finitevscpy_3) (or (= fresh38 1) (= fresh38 0))))))))))))))) (or (= fresh37 (+ k_finitevscpy_4 k_finitevscpy_4)) (or (= fresh37 (+ k_finitevscpy_4 y_finitevscpy_4)) (or (= fresh37 (+ y_finitevscpy_4 y_finitevscpy_4)) (or (= fresh37 (+ k_finitevscpy_4 x_finitevscpy_4)) (or (= fresh37 (+ y_finitevscpy_4 x_finitevscpy_4)) (or (= fresh37 (+ x_finitevscpy_4 x_finitevscpy_4)) (or (= fresh37 (+ 1 k_finitevscpy_4)) (or (= fresh37 (+ 1 y_finitevscpy_4)) (or (= fresh37 (+ 1 x_finitevscpy_4)) (or (= fresh37 2) (or (= fresh37 k_finitevscpy_4) (or (= fresh37 y_finitevscpy_4) (or (= fresh37 x_finitevscpy_4) (or (= fresh37 1) (= fresh37 0)))))))))))))))))) (and (or (= fresh44 0) (or (= fresh44 1) (or (= fresh44 x_finitevscpy_1) (or (= fresh44 y_finitevscpy_1) (= fresh44 k_finitevscpy_1))))) (and (or (= fresh43 0) (or (= fresh43 1) (or (= fresh43 x_finitevscpy_2) (or (= fresh43 y_finitevscpy_2) (= fresh43 k_finitevscpy_2))))) (and (or (= fresh42 0) (or (= fresh42 1) (or (= fresh42 x_finitevscpy_3) (or (= fresh42 y_finitevscpy_3) (= fresh42 k_finitevscpy_3))))) (or (= fresh41 0) (or (= fresh41 1) (or (= fresh41 x_finitevscpy_4) (or (= fresh41 y_finitevscpy_4) (= fresh41 k_finitevscpy_4)))))))))))) (not (and (and (and (and true (or (or false (and (and (not (not (< fresh32 fresh36))) true) (= fresh44 0))) (and (and (not (< fresh32 fresh36)) true) (= fresh40 0)))) (or (or false (and (and (not (not (< fresh31 fresh35))) true) (= fresh43 2))) (and (and (not (< fresh31 fresh35)) true) (= fresh39 2)))) (or (or false (and (and (not (not (< fresh30 fresh34))) true) (= fresh42 3))) (and (and (not (< fresh30 fresh34)) true) (= fresh38 3)))) (or (or false (and (and (not (not (< fresh29 fresh33))) true) (= fresh41 1))) (and (and (not (< fresh29 fresh33)) true) (= fresh37 1))))))
)
 )
(check-sat)
(exit)