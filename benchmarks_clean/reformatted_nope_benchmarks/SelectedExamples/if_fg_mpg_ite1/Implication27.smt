;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh10 Bool)
(declare-const fresh11 Bool)
(declare-const fresh12 Bool)
(declare-const fresh13 Bool)
(declare-const fresh14 Bool)
(declare-const fresh7 Bool)
(declare-const fresh8 Bool)
(declare-const fresh9 Bool)
(declare-const fresh15 Int)
(declare-const fresh16 Int)
(declare-const fresh17 Int)
(declare-const fresh18 Int)
(declare-const fresh19 Int)
(declare-const fresh20 Int)
(declare-const fresh21 Int)
(declare-const fresh22 Int)
(declare-const fresh23 Int)
(declare-const fresh24 Int)
(declare-const fresh25 Int)
(declare-const fresh26 Int)
(declare-const fresh27 Int)
(declare-const fresh28 Int)
(declare-const fresh29 Int)
(declare-const fresh30 Int)
(declare-const fresh3_finitevscpy_1 Int)
(declare-const fresh3_finitevscpy_2 Int)
(declare-const fresh3_finitevscpy_3 Int)
(declare-const fresh3_finitevscpy_4 Int)
(declare-const fresh3_finitevscpy_5 Int)
(declare-const fresh3_finitevscpy_6 Int)
(declare-const fresh3_finitevscpy_7 Int)
(declare-const fresh3_finitevscpy_8 Int)
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
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 0)) (= y_finitevscpy_1 0)) (= z_finitevscpy_1 0)) (= x_finitevscpy_2 (- 3))) (= y_finitevscpy_2 (- 6))) (= z_finitevscpy_2 (- 9))) (= x_finitevscpy_3 (- 1))) (= y_finitevscpy_3 0)) (= z_finitevscpy_3 0)) (= x_finitevscpy_4 (- 1))) (= y_finitevscpy_4 1)) (= z_finitevscpy_4 3)) (= x_finitevscpy_5 (- 1))) (= y_finitevscpy_5 3)) (= z_finitevscpy_5 1)) (= x_finitevscpy_6 1)) (= y_finitevscpy_6 (- 1))) (= z_finitevscpy_6 1)) (= x_finitevscpy_7 (- 3))) (= y_finitevscpy_7 0)) (= z_finitevscpy_7 (- 1))) (= x_finitevscpy_8 0)) (= y_finitevscpy_8 1)) (= z_finitevscpy_8 2)) (and true (and (and (and (or (< 0 fresh26) (= 0 fresh26)) (and (or (< 0 fresh25) (= 0 fresh25)) (and (or (< 0 fresh24) (= 0 fresh24)) (or (< 0 fresh23) (= 0 fresh23))))) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_1) (+ (* fresh25 y_finitevscpy_1) (* fresh24 z_finitevscpy_1)))) fresh22) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_2) (+ (* fresh25 y_finitevscpy_2) (* fresh24 z_finitevscpy_2)))) fresh21) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_3) (+ (* fresh25 y_finitevscpy_3) (* fresh24 z_finitevscpy_3)))) fresh20) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_4) (+ (* fresh25 y_finitevscpy_4) (* fresh24 z_finitevscpy_4)))) fresh19) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_5) (+ (* fresh25 y_finitevscpy_5) (* fresh24 z_finitevscpy_5)))) fresh18) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_6) (+ (* fresh25 y_finitevscpy_6) (* fresh24 z_finitevscpy_6)))) fresh17) (and (= (+ fresh23 (+ (* fresh26 x_finitevscpy_7) (+ (* fresh25 y_finitevscpy_7) (* fresh24 z_finitevscpy_7)))) fresh16) (= (+ fresh23 (+ (* fresh26 x_finitevscpy_8) (+ (* fresh25 y_finitevscpy_8) (* fresh24 z_finitevscpy_8)))) fresh15))))))))) (and (and (or (< 0 fresh30) (= 0 fresh30)) (and (or (< 0 fresh29) (= 0 fresh29)) (and (or (< 0 fresh28) (= 0 fresh28)) (or (< 0 fresh27) (= 0 fresh27))))) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_1) (+ (* fresh29 y_finitevscpy_1) (* fresh28 z_finitevscpy_1)))) fresh3_finitevscpy_1) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_2) (+ (* fresh29 y_finitevscpy_2) (* fresh28 z_finitevscpy_2)))) fresh3_finitevscpy_2) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_3) (+ (* fresh29 y_finitevscpy_3) (* fresh28 z_finitevscpy_3)))) fresh3_finitevscpy_3) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_4) (+ (* fresh29 y_finitevscpy_4) (* fresh28 z_finitevscpy_4)))) fresh3_finitevscpy_4) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_5) (+ (* fresh29 y_finitevscpy_5) (* fresh28 z_finitevscpy_5)))) fresh3_finitevscpy_5) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_6) (+ (* fresh29 y_finitevscpy_6) (* fresh28 z_finitevscpy_6)))) fresh3_finitevscpy_6) (and (= (+ fresh27 (+ (* fresh30 x_finitevscpy_7) (+ (* fresh29 y_finitevscpy_7) (* fresh28 z_finitevscpy_7)))) fresh3_finitevscpy_7) (= (+ fresh27 (+ (* fresh30 x_finitevscpy_8) (+ (* fresh29 y_finitevscpy_8) (* fresh28 z_finitevscpy_8)))) fresh3_finitevscpy_8)))))))))))) (not (and (and (and (and (and (and (and (and true (or (or false (and (and (not fresh14) true) (= fresh3_finitevscpy_1 1))) (and (and fresh14 true) (= fresh22 1)))) (or (or false (and (and (not fresh13) true) (= fresh3_finitevscpy_2 0))) (and (and fresh13 true) (= fresh21 0)))) (or (or false (and (and (not fresh12) true) (= fresh3_finitevscpy_3 1))) (and (and fresh12 true) (= fresh20 1)))) (or (or false (and (and (not fresh11) true) (= fresh3_finitevscpy_4 4))) (and (and fresh11 true) (= fresh19 4)))) (or (or false (and (and (not fresh10) true) (= fresh3_finitevscpy_5 4))) (and (and fresh10 true) (= fresh18 4)))) (or (or false (and (and (not fresh9) true) (= fresh3_finitevscpy_6 2))) (and (and fresh9 true) (= fresh17 2)))) (or (or false (and (and (not fresh8) true) (= fresh3_finitevscpy_7 0))) (and (and fresh8 true) (= fresh16 0)))) (or (or false (and (and (not fresh7) true) (= fresh3_finitevscpy_8 1))) (and (and fresh7 true) (= fresh15 1))))))
)
 )
(check-sat)
(exit)