;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const a1 Int)
(declare-const a2 Int)
(declare-const b1 Int)
(declare-const b2 Int)
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const d1 Int)
(declare-const d2 Int)
(declare-const fresh69 Int)
(declare-const fresh70 Int)
(declare-const fresh71 Int)
(declare-const fresh72 Int)
(declare-const fresh73 Int)
(declare-const fresh74 Int)
(declare-const fresh75 Int)
(declare-const fresh76 Int)
(declare-const fresh77 Int)
(declare-const fresh78 Int)
(declare-const fresh79 Int)
(declare-const fresh80 Int)
(declare-const fresh81 Int)
(declare-const fresh82 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const x_finitevscpy_4 Int)
(declare-const x_finitevscpy_5 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const y_finitevscpy_2 Int)
(declare-const y_finitevscpy_3 Int)
(declare-const y_finitevscpy_4 Int)
(declare-const y_finitevscpy_5 Int)
(declare-const z_finitevscpy_1 Int)
(declare-const z_finitevscpy_2 Int)
(declare-const z_finitevscpy_3 Int)
(declare-const z_finitevscpy_4 Int)
(declare-const z_finitevscpy_5 Int)
(assert
(not
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x_finitevscpy_1 (- 1))) (= y_finitevscpy_1 1)) (= z_finitevscpy_1 0)) (= x_finitevscpy_2 (- 2))) (= y_finitevscpy_2 0)) (= z_finitevscpy_2 (- 1))) (= x_finitevscpy_3 0)) (= y_finitevscpy_3 1)) (= z_finitevscpy_3 (- 1))) (= x_finitevscpy_4 (- 1))) (= y_finitevscpy_4 0)) (= z_finitevscpy_4 1)) (= x_finitevscpy_5 1)) (= y_finitevscpy_5 2)) (= z_finitevscpy_5 3)) (and (and (and (or (< 0 a1) (= 0 a1)) (and (or (< 0 b1) (= 0 b1)) (and (or (< 0 c1) (= 0 c1)) (or (< 0 d1) (= 0 d1))))) (and (and (or (< 0 a2) (= 0 a2)) (and (or (< 0 b2) (= 0 b2)) (and (or (< 0 c2) (= 0 c2)) (or (< 0 d2) (= 0 d2))))) (and (or (= (+ d1 (+ (* a1 x_finitevscpy_1) (+ (* b1 y_finitevscpy_1) (* c1 z_finitevscpy_1)))) fresh73) (= (+ d2 (+ (* a2 x_finitevscpy_1) (+ (* b2 y_finitevscpy_1) (* c2 z_finitevscpy_1)))) fresh73)) (and (or (= (+ d1 (+ (* a1 x_finitevscpy_2) (+ (* b1 y_finitevscpy_2) (* c1 z_finitevscpy_2)))) fresh72) (= (+ d2 (+ (* a2 x_finitevscpy_2) (+ (* b2 y_finitevscpy_2) (* c2 z_finitevscpy_2)))) fresh72)) (and (or (= (+ d1 (+ (* a1 x_finitevscpy_3) (+ (* b1 y_finitevscpy_3) (* c1 z_finitevscpy_3)))) fresh71) (= (+ d2 (+ (* a2 x_finitevscpy_3) (+ (* b2 y_finitevscpy_3) (* c2 z_finitevscpy_3)))) fresh71)) (and (or (= (+ d1 (+ (* a1 x_finitevscpy_4) (+ (* b1 y_finitevscpy_4) (* c1 z_finitevscpy_4)))) fresh70) (= (+ d2 (+ (* a2 x_finitevscpy_4) (+ (* b2 y_finitevscpy_4) (* c2 z_finitevscpy_4)))) fresh70)) (or (= (+ d1 (+ (* a1 x_finitevscpy_5) (+ (* b1 y_finitevscpy_5) (* c1 z_finitevscpy_5)))) fresh69) (= (+ d2 (+ (* a2 x_finitevscpy_5) (+ (* b2 y_finitevscpy_5) (* c2 z_finitevscpy_5)))) fresh69)))))))) (and (and (or (< 0 fresh82) (= 0 fresh82)) (and (or (< 0 fresh81) (= 0 fresh81)) (and (or (< 0 fresh80) (= 0 fresh80)) (or (< 0 fresh79) (= 0 fresh79))))) (and (= (+ fresh79 (+ (* fresh82 x_finitevscpy_1) (+ (* fresh81 y_finitevscpy_1) (* fresh80 z_finitevscpy_1)))) fresh78) (and (= (+ fresh79 (+ (* fresh82 x_finitevscpy_2) (+ (* fresh81 y_finitevscpy_2) (* fresh80 z_finitevscpy_2)))) fresh77) (and (= (+ fresh79 (+ (* fresh82 x_finitevscpy_3) (+ (* fresh81 y_finitevscpy_3) (* fresh80 z_finitevscpy_3)))) fresh76) (and (= (+ fresh79 (+ (* fresh82 x_finitevscpy_4) (+ (* fresh81 y_finitevscpy_4) (* fresh80 z_finitevscpy_4)))) fresh75) (= (+ fresh79 (+ (* fresh82 x_finitevscpy_5) (+ (* fresh81 y_finitevscpy_5) (* fresh80 z_finitevscpy_5)))) fresh74)))))))) (not (and (and (and (and (and true (= (+ fresh73 fresh78) 1)) (= (+ fresh72 fresh77) 1)) (= (+ fresh71 fresh76) 0)) (= (+ fresh70 fresh75) 2)) (= (+ fresh69 fresh74) 2))))
)
 )
(check-sat)
(exit)