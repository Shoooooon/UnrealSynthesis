;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Bool)
(declare-const fresh1_finitevscpy_2 Bool)
(declare-const fresh1_finitevscpy_3 Bool)
(declare-const fresh1_finitevscpy_4 Bool)
(declare-const fresh1_finitevscpy_5 Bool)
(declare-const fresh1_finitevscpy_6 Bool)
(declare-const fresh1_finitevscpy_7 Bool)
(declare-const fresh1_finitevscpy_8 Bool)
(declare-const fresh1_finitevscpy_9 Bool)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const fresh2_finitevscpy_2 Int)
(declare-const fresh2_finitevscpy_3 Int)
(declare-const fresh2_finitevscpy_4 Int)
(declare-const fresh2_finitevscpy_5 Int)
(declare-const fresh2_finitevscpy_6 Int)
(declare-const fresh2_finitevscpy_7 Int)
(declare-const fresh2_finitevscpy_8 Int)
(declare-const fresh2_finitevscpy_9 Int)
(declare-const fresh3_finitevscpy_1 Int)
(declare-const fresh3_finitevscpy_2 Int)
(declare-const fresh3_finitevscpy_3 Int)
(declare-const fresh3_finitevscpy_4 Int)
(declare-const fresh3_finitevscpy_5 Int)
(declare-const fresh3_finitevscpy_6 Int)
(declare-const fresh3_finitevscpy_7 Int)
(declare-const fresh3_finitevscpy_8 Int)
(declare-const fresh3_finitevscpy_9 Int)
(declare-const fresh4 Int)
(declare-const fresh5 Int)
(declare-const fresh6 Int)
(declare-const fresh7 Int)
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
(=> (and true (and true (and (and (and (or (< 0 a) (= 0 a)) (and (or (< 0 b) (= 0 b)) (and (or (< 0 c) (= 0 c)) (or (< 0 d) (= 0 d))))) (and (= (+ d (+ (* a x1_finitevscpy_1) (+ (* b x2_finitevscpy_1) (* c x3_finitevscpy_1)))) fresh2_finitevscpy_1) (and (= (+ d (+ (* a x1_finitevscpy_2) (+ (* b x2_finitevscpy_2) (* c x3_finitevscpy_2)))) fresh2_finitevscpy_2) (and (= (+ d (+ (* a x1_finitevscpy_3) (+ (* b x2_finitevscpy_3) (* c x3_finitevscpy_3)))) fresh2_finitevscpy_3) (and (= (+ d (+ (* a x1_finitevscpy_4) (+ (* b x2_finitevscpy_4) (* c x3_finitevscpy_4)))) fresh2_finitevscpy_4) (and (= (+ d (+ (* a x1_finitevscpy_5) (+ (* b x2_finitevscpy_5) (* c x3_finitevscpy_5)))) fresh2_finitevscpy_5) (and (= (+ d (+ (* a x1_finitevscpy_6) (+ (* b x2_finitevscpy_6) (* c x3_finitevscpy_6)))) fresh2_finitevscpy_6) (and (= (+ d (+ (* a x1_finitevscpy_7) (+ (* b x2_finitevscpy_7) (* c x3_finitevscpy_7)))) fresh2_finitevscpy_7) (and (= (+ d (+ (* a x1_finitevscpy_8) (+ (* b x2_finitevscpy_8) (* c x3_finitevscpy_8)))) fresh2_finitevscpy_8) (= (+ d (+ (* a x1_finitevscpy_9) (+ (* b x2_finitevscpy_9) (* c x3_finitevscpy_9)))) fresh2_finitevscpy_9)))))))))) (and (and (or (< 0 fresh7) (= 0 fresh7)) (and (or (< 0 fresh6) (= 0 fresh6)) (and (or (< 0 fresh5) (= 0 fresh5)) (or (< 0 fresh4) (= 0 fresh4))))) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_1) (+ (* fresh6 x2_finitevscpy_1) (* fresh5 x3_finitevscpy_1)))) fresh3_finitevscpy_1) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_2) (+ (* fresh6 x2_finitevscpy_2) (* fresh5 x3_finitevscpy_2)))) fresh3_finitevscpy_2) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_3) (+ (* fresh6 x2_finitevscpy_3) (* fresh5 x3_finitevscpy_3)))) fresh3_finitevscpy_3) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_4) (+ (* fresh6 x2_finitevscpy_4) (* fresh5 x3_finitevscpy_4)))) fresh3_finitevscpy_4) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_5) (+ (* fresh6 x2_finitevscpy_5) (* fresh5 x3_finitevscpy_5)))) fresh3_finitevscpy_5) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_6) (+ (* fresh6 x2_finitevscpy_6) (* fresh5 x3_finitevscpy_6)))) fresh3_finitevscpy_6) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_7) (+ (* fresh6 x2_finitevscpy_7) (* fresh5 x3_finitevscpy_7)))) fresh3_finitevscpy_7) (and (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_8) (+ (* fresh6 x2_finitevscpy_8) (* fresh5 x3_finitevscpy_8)))) fresh3_finitevscpy_8) (= (+ fresh4 (+ (* fresh7 x1_finitevscpy_9) (+ (* fresh6 x2_finitevscpy_9) (* fresh5 x3_finitevscpy_9)))) fresh3_finitevscpy_9))))))))))))) (exists ((d2 Int) ) (exists ((c2 Int) ) (exists ((b2 Int) ) (exists ((a2 Int) ) (exists ((d1 Int) ) (exists ((c1 Int) ) (exists ((b1 Int) ) (exists ((a1 Int) ) (and (and (or (or false (and true (< 0 a1))) (or false (and true (= 0 a1)))) (and (or (or false (and true (< 0 b1))) (or false (and true (= 0 b1)))) (and (or (or false (and true (< 0 c1))) (or false (and true (= 0 c1)))) (or (or false (and true (< 0 d1))) (or false (and true (= 0 d1))))))) (and (and (or (or false (and true (< 0 a2))) (or false (and true (= 0 a2)))) (and (or (or false (and true (< 0 b2))) (or false (and true (= 0 b2)))) (and (or (or false (and true (< 0 c2))) (or false (and true (= 0 c2)))) (or (or false (and true (< 0 d2))) (or false (and true (= 0 d2))))))) (and (or (or (or false (and (and (not fresh1_finitevscpy_1) true) (= (+ d1 (+ (* a1 x1_finitevscpy_1) (+ (* b1 x2_finitevscpy_1) (* c1 x3_finitevscpy_1)))) fresh3_finitevscpy_1))) (and (and fresh1_finitevscpy_1 true) (= (+ d1 (+ (* a1 x1_finitevscpy_1) (+ (* b1 x2_finitevscpy_1) (* c1 x3_finitevscpy_1)))) fresh2_finitevscpy_1))) (or (or false (and (and (not fresh1_finitevscpy_1) true) (= (+ d2 (+ (* a2 x1_finitevscpy_1) (+ (* b2 x2_finitevscpy_1) (* c2 x3_finitevscpy_1)))) fresh3_finitevscpy_1))) (and (and fresh1_finitevscpy_1 true) (= (+ d2 (+ (* a2 x1_finitevscpy_1) (+ (* b2 x2_finitevscpy_1) (* c2 x3_finitevscpy_1)))) fresh2_finitevscpy_1)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_2) true) (= (+ d1 (+ (* a1 x1_finitevscpy_2) (+ (* b1 x2_finitevscpy_2) (* c1 x3_finitevscpy_2)))) fresh3_finitevscpy_2))) (and (and fresh1_finitevscpy_2 true) (= (+ d1 (+ (* a1 x1_finitevscpy_2) (+ (* b1 x2_finitevscpy_2) (* c1 x3_finitevscpy_2)))) fresh2_finitevscpy_2))) (or (or false (and (and (not fresh1_finitevscpy_2) true) (= (+ d2 (+ (* a2 x1_finitevscpy_2) (+ (* b2 x2_finitevscpy_2) (* c2 x3_finitevscpy_2)))) fresh3_finitevscpy_2))) (and (and fresh1_finitevscpy_2 true) (= (+ d2 (+ (* a2 x1_finitevscpy_2) (+ (* b2 x2_finitevscpy_2) (* c2 x3_finitevscpy_2)))) fresh2_finitevscpy_2)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_3) true) (= (+ d1 (+ (* a1 x1_finitevscpy_3) (+ (* b1 x2_finitevscpy_3) (* c1 x3_finitevscpy_3)))) fresh3_finitevscpy_3))) (and (and fresh1_finitevscpy_3 true) (= (+ d1 (+ (* a1 x1_finitevscpy_3) (+ (* b1 x2_finitevscpy_3) (* c1 x3_finitevscpy_3)))) fresh2_finitevscpy_3))) (or (or false (and (and (not fresh1_finitevscpy_3) true) (= (+ d2 (+ (* a2 x1_finitevscpy_3) (+ (* b2 x2_finitevscpy_3) (* c2 x3_finitevscpy_3)))) fresh3_finitevscpy_3))) (and (and fresh1_finitevscpy_3 true) (= (+ d2 (+ (* a2 x1_finitevscpy_3) (+ (* b2 x2_finitevscpy_3) (* c2 x3_finitevscpy_3)))) fresh2_finitevscpy_3)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_4) true) (= (+ d1 (+ (* a1 x1_finitevscpy_4) (+ (* b1 x2_finitevscpy_4) (* c1 x3_finitevscpy_4)))) fresh3_finitevscpy_4))) (and (and fresh1_finitevscpy_4 true) (= (+ d1 (+ (* a1 x1_finitevscpy_4) (+ (* b1 x2_finitevscpy_4) (* c1 x3_finitevscpy_4)))) fresh2_finitevscpy_4))) (or (or false (and (and (not fresh1_finitevscpy_4) true) (= (+ d2 (+ (* a2 x1_finitevscpy_4) (+ (* b2 x2_finitevscpy_4) (* c2 x3_finitevscpy_4)))) fresh3_finitevscpy_4))) (and (and fresh1_finitevscpy_4 true) (= (+ d2 (+ (* a2 x1_finitevscpy_4) (+ (* b2 x2_finitevscpy_4) (* c2 x3_finitevscpy_4)))) fresh2_finitevscpy_4)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_5) true) (= (+ d1 (+ (* a1 x1_finitevscpy_5) (+ (* b1 x2_finitevscpy_5) (* c1 x3_finitevscpy_5)))) fresh3_finitevscpy_5))) (and (and fresh1_finitevscpy_5 true) (= (+ d1 (+ (* a1 x1_finitevscpy_5) (+ (* b1 x2_finitevscpy_5) (* c1 x3_finitevscpy_5)))) fresh2_finitevscpy_5))) (or (or false (and (and (not fresh1_finitevscpy_5) true) (= (+ d2 (+ (* a2 x1_finitevscpy_5) (+ (* b2 x2_finitevscpy_5) (* c2 x3_finitevscpy_5)))) fresh3_finitevscpy_5))) (and (and fresh1_finitevscpy_5 true) (= (+ d2 (+ (* a2 x1_finitevscpy_5) (+ (* b2 x2_finitevscpy_5) (* c2 x3_finitevscpy_5)))) fresh2_finitevscpy_5)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_6) true) (= (+ d1 (+ (* a1 x1_finitevscpy_6) (+ (* b1 x2_finitevscpy_6) (* c1 x3_finitevscpy_6)))) fresh3_finitevscpy_6))) (and (and fresh1_finitevscpy_6 true) (= (+ d1 (+ (* a1 x1_finitevscpy_6) (+ (* b1 x2_finitevscpy_6) (* c1 x3_finitevscpy_6)))) fresh2_finitevscpy_6))) (or (or false (and (and (not fresh1_finitevscpy_6) true) (= (+ d2 (+ (* a2 x1_finitevscpy_6) (+ (* b2 x2_finitevscpy_6) (* c2 x3_finitevscpy_6)))) fresh3_finitevscpy_6))) (and (and fresh1_finitevscpy_6 true) (= (+ d2 (+ (* a2 x1_finitevscpy_6) (+ (* b2 x2_finitevscpy_6) (* c2 x3_finitevscpy_6)))) fresh2_finitevscpy_6)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_7) true) (= (+ d1 (+ (* a1 x1_finitevscpy_7) (+ (* b1 x2_finitevscpy_7) (* c1 x3_finitevscpy_7)))) fresh3_finitevscpy_7))) (and (and fresh1_finitevscpy_7 true) (= (+ d1 (+ (* a1 x1_finitevscpy_7) (+ (* b1 x2_finitevscpy_7) (* c1 x3_finitevscpy_7)))) fresh2_finitevscpy_7))) (or (or false (and (and (not fresh1_finitevscpy_7) true) (= (+ d2 (+ (* a2 x1_finitevscpy_7) (+ (* b2 x2_finitevscpy_7) (* c2 x3_finitevscpy_7)))) fresh3_finitevscpy_7))) (and (and fresh1_finitevscpy_7 true) (= (+ d2 (+ (* a2 x1_finitevscpy_7) (+ (* b2 x2_finitevscpy_7) (* c2 x3_finitevscpy_7)))) fresh2_finitevscpy_7)))) (and (or (or (or false (and (and (not fresh1_finitevscpy_8) true) (= (+ d1 (+ (* a1 x1_finitevscpy_8) (+ (* b1 x2_finitevscpy_8) (* c1 x3_finitevscpy_8)))) fresh3_finitevscpy_8))) (and (and fresh1_finitevscpy_8 true) (= (+ d1 (+ (* a1 x1_finitevscpy_8) (+ (* b1 x2_finitevscpy_8) (* c1 x3_finitevscpy_8)))) fresh2_finitevscpy_8))) (or (or false (and (and (not fresh1_finitevscpy_8) true) (= (+ d2 (+ (* a2 x1_finitevscpy_8) (+ (* b2 x2_finitevscpy_8) (* c2 x3_finitevscpy_8)))) fresh3_finitevscpy_8))) (and (and fresh1_finitevscpy_8 true) (= (+ d2 (+ (* a2 x1_finitevscpy_8) (+ (* b2 x2_finitevscpy_8) (* c2 x3_finitevscpy_8)))) fresh2_finitevscpy_8)))) (or (or (or false (and (and (not fresh1_finitevscpy_9) true) (= (+ d1 (+ (* a1 x1_finitevscpy_9) (+ (* b1 x2_finitevscpy_9) (* c1 x3_finitevscpy_9)))) fresh3_finitevscpy_9))) (and (and fresh1_finitevscpy_9 true) (= (+ d1 (+ (* a1 x1_finitevscpy_9) (+ (* b1 x2_finitevscpy_9) (* c1 x3_finitevscpy_9)))) fresh2_finitevscpy_9))) (or (or false (and (and (not fresh1_finitevscpy_9) true) (= (+ d2 (+ (* a2 x1_finitevscpy_9) (+ (* b2 x2_finitevscpy_9) (* c2 x3_finitevscpy_9)))) fresh3_finitevscpy_9))) (and (and fresh1_finitevscpy_9 true) (= (+ d2 (+ (* a2 x1_finitevscpy_9) (+ (* b2 x2_finitevscpy_9) (* c2 x3_finitevscpy_9)))) fresh2_finitevscpy_9)))))))))))))))))))))))
)
 )
(check-sat)
(exit)