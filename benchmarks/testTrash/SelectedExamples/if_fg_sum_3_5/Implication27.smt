;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const fresh1_finitevscpy_1 Int)
(declare-const fresh1_finitevscpy_2 Int)
(declare-const fresh1_finitevscpy_3 Int)
(declare-const fresh1_finitevscpy_4 Int)
(declare-const fresh1_finitevscpy_5 Int)
(declare-const fresh1_finitevscpy_6 Int)
(declare-const fresh1_finitevscpy_7 Int)
(declare-const fresh1_finitevscpy_8 Int)
(declare-const fresh1_finitevscpy_9 Int)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const fresh2_finitevscpy_2 Int)
(declare-const fresh2_finitevscpy_3 Int)
(declare-const fresh2_finitevscpy_4 Int)
(declare-const fresh2_finitevscpy_5 Int)
(declare-const fresh2_finitevscpy_6 Int)
(declare-const fresh2_finitevscpy_7 Int)
(declare-const fresh2_finitevscpy_8 Int)
(declare-const fresh2_finitevscpy_9 Int)
(declare-const fresh3 Int)
(declare-const fresh4 Int)
(declare-const fresh5 Int)
(declare-const fresh6 Int)
(declare-const x1_finitevscpy_1 Int)
(declare-const x1_finitevscpy_2 Int)
(declare-const x1_finitevscpy_3 Int)
(declare-const x1_finitevscpy_4 Int)
(declare-const x1_finitevscpy_5 Int)
(declare-const x1_finitevscpy_6 Int)
(declare-const x1_finitevscpy_7 Int)
(declare-const x1_finitevscpy_8 Int)
(declare-const x1_finitevscpy_9 Int)
(declare-const x2_finitevscpy_1 Int)
(declare-const x2_finitevscpy_2 Int)
(declare-const x2_finitevscpy_3 Int)
(declare-const x2_finitevscpy_4 Int)
(declare-const x2_finitevscpy_5 Int)
(declare-const x2_finitevscpy_6 Int)
(declare-const x2_finitevscpy_7 Int)
(declare-const x2_finitevscpy_8 Int)
(declare-const x2_finitevscpy_9 Int)
(declare-const x3_finitevscpy_1 Int)
(declare-const x3_finitevscpy_2 Int)
(declare-const x3_finitevscpy_3 Int)
(declare-const x3_finitevscpy_4 Int)
(declare-const x3_finitevscpy_5 Int)
(declare-const x3_finitevscpy_6 Int)
(declare-const x3_finitevscpy_7 Int)
(declare-const x3_finitevscpy_8 Int)
(declare-const x3_finitevscpy_9 Int)
(assert
(not
(=> (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and true (= x1_finitevscpy_1 0)) (= x2_finitevscpy_1 0)) (= x3_finitevscpy_1 0)) (= x1_finitevscpy_2 (- 1))) (= x2_finitevscpy_2 0)) (= x3_finitevscpy_2 (- 1))) (= x1_finitevscpy_3 0)) (= x2_finitevscpy_3 (- 1))) (= x3_finitevscpy_3 0)) (= x1_finitevscpy_4 6)) (= x2_finitevscpy_4 0)) (= x3_finitevscpy_4 (- 1))) (= x1_finitevscpy_5 0)) (= x2_finitevscpy_5 1)) (= x3_finitevscpy_5 5)) (= x1_finitevscpy_6 4)) (= x2_finitevscpy_6 4)) (= x3_finitevscpy_6 2)) (= x1_finitevscpy_7 3)) (= x2_finitevscpy_7 4)) (= x3_finitevscpy_7 1)) (= x1_finitevscpy_8 4)) (= x2_finitevscpy_8 1)) (= x3_finitevscpy_8 2)) (= x1_finitevscpy_9 4)) (= x2_finitevscpy_9 4)) (= x3_finitevscpy_9 3)) (and (and (and (or (< 0 a) (= 0 a)) (and (or (< 0 b) (= 0 b)) (and (or (< 0 c) (= 0 c)) (or (< 0 d) (= 0 d))))) (and (= (+ d (+ (* a x1_finitevscpy_1) (+ (* b x2_finitevscpy_1) (* c x3_finitevscpy_1)))) fresh1_finitevscpy_1) (and (= (+ d (+ (* a x1_finitevscpy_2) (+ (* b x2_finitevscpy_2) (* c x3_finitevscpy_2)))) fresh1_finitevscpy_2) (and (= (+ d (+ (* a x1_finitevscpy_3) (+ (* b x2_finitevscpy_3) (* c x3_finitevscpy_3)))) fresh1_finitevscpy_3) (and (= (+ d (+ (* a x1_finitevscpy_4) (+ (* b x2_finitevscpy_4) (* c x3_finitevscpy_4)))) fresh1_finitevscpy_4) (and (= (+ d (+ (* a x1_finitevscpy_5) (+ (* b x2_finitevscpy_5) (* c x3_finitevscpy_5)))) fresh1_finitevscpy_5) (and (= (+ d (+ (* a x1_finitevscpy_6) (+ (* b x2_finitevscpy_6) (* c x3_finitevscpy_6)))) fresh1_finitevscpy_6) (and (= (+ d (+ (* a x1_finitevscpy_7) (+ (* b x2_finitevscpy_7) (* c x3_finitevscpy_7)))) fresh1_finitevscpy_7) (and (= (+ d (+ (* a x1_finitevscpy_8) (+ (* b x2_finitevscpy_8) (* c x3_finitevscpy_8)))) fresh1_finitevscpy_8) (= (+ d (+ (* a x1_finitevscpy_9) (+ (* b x2_finitevscpy_9) (* c x3_finitevscpy_9)))) fresh1_finitevscpy_9)))))))))) (and (and (or (< 0 fresh6) (= 0 fresh6)) (and (or (< 0 fresh5) (= 0 fresh5)) (and (or (< 0 fresh4) (= 0 fresh4)) (or (< 0 fresh3) (= 0 fresh3))))) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_1) (+ (* fresh5 x2_finitevscpy_1) (* fresh4 x3_finitevscpy_1)))) fresh2_finitevscpy_1) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_2) (+ (* fresh5 x2_finitevscpy_2) (* fresh4 x3_finitevscpy_2)))) fresh2_finitevscpy_2) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_3) (+ (* fresh5 x2_finitevscpy_3) (* fresh4 x3_finitevscpy_3)))) fresh2_finitevscpy_3) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_4) (+ (* fresh5 x2_finitevscpy_4) (* fresh4 x3_finitevscpy_4)))) fresh2_finitevscpy_4) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_5) (+ (* fresh5 x2_finitevscpy_5) (* fresh4 x3_finitevscpy_5)))) fresh2_finitevscpy_5) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_6) (+ (* fresh5 x2_finitevscpy_6) (* fresh4 x3_finitevscpy_6)))) fresh2_finitevscpy_6) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_7) (+ (* fresh5 x2_finitevscpy_7) (* fresh4 x3_finitevscpy_7)))) fresh2_finitevscpy_7) (and (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_8) (+ (* fresh5 x2_finitevscpy_8) (* fresh4 x3_finitevscpy_8)))) fresh2_finitevscpy_8) (= (+ fresh3 (+ (* fresh6 x1_finitevscpy_9) (+ (* fresh5 x2_finitevscpy_9) (* fresh4 x3_finitevscpy_9)))) fresh2_finitevscpy_9)))))))))))) (not (and (and (and (and (and (and (and (and (and true (= (+ fresh1_finitevscpy_1 fresh2_finitevscpy_1) 0)) (= (+ fresh1_finitevscpy_2 fresh2_finitevscpy_2) 0)) (= (+ fresh1_finitevscpy_3 fresh2_finitevscpy_3) 0)) (= (+ fresh1_finitevscpy_4 fresh2_finitevscpy_4) 6)) (= (+ fresh1_finitevscpy_5 fresh2_finitevscpy_5) 6)) (= (+ fresh1_finitevscpy_6 fresh2_finitevscpy_6) 6)) (= (+ fresh1_finitevscpy_7 fresh2_finitevscpy_7) 7)) (= (+ fresh1_finitevscpy_8 fresh2_finitevscpy_8) 0)) (= (+ fresh1_finitevscpy_9 fresh2_finitevscpy_9) 8))))
)
 )
(check-sat)
(exit)