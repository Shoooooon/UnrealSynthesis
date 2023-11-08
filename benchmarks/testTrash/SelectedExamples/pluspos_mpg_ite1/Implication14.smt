;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh5 Bool)
(declare-const fresh6 Int)
(declare-const fresh7 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and true (and true (and (or (= fresh6 0) (or (= fresh6 1) (or (= fresh6 x_finitevscpy_1) (or (= fresh6 y_finitevscpy_1) (= fresh6 z_finitevscpy_1))))) (or (= fresh7 (+ z_finitevscpy_1 z_finitevscpy_1)) (or (= fresh7 (+ z_finitevscpy_1 y_finitevscpy_1)) (or (= fresh7 (+ y_finitevscpy_1 y_finitevscpy_1)) (or (= fresh7 (+ z_finitevscpy_1 x_finitevscpy_1)) (or (= fresh7 (+ y_finitevscpy_1 x_finitevscpy_1)) (or (= fresh7 (+ x_finitevscpy_1 x_finitevscpy_1)) (or (= fresh7 (+ 1 z_finitevscpy_1)) (or (= fresh7 (+ 1 y_finitevscpy_1)) (or (= fresh7 (+ 1 x_finitevscpy_1)) (or (= fresh7 2) (or (= fresh7 z_finitevscpy_1) (or (= fresh7 y_finitevscpy_1) (or (= fresh7 x_finitevscpy_1) (or (= fresh7 1) (= fresh7 0)))))))))))))))))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ z_finitevscpy_1 z_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ z_finitevscpy_1 z_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ z_finitevscpy_1 y_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ z_finitevscpy_1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ y_finitevscpy_1 y_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ y_finitevscpy_1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ z_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ z_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ y_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ y_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ x_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ x_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ 1 z_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ 1 z_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ 1 y_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ 1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 (+ 1 x_finitevscpy_1)))) (and (and fresh5 true) (= fresh6 (+ 1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh5) true) (= fresh7 2))) (and (and fresh5 true) (= fresh6 2))) (or (or (or false (and (and (not fresh5) true) (= fresh7 z_finitevscpy_1))) (and (and fresh5 true) (= fresh6 z_finitevscpy_1))) (or (or (or false (and (and (not fresh5) true) (= fresh7 y_finitevscpy_1))) (and (and fresh5 true) (= fresh6 y_finitevscpy_1))) (or (or (or false (and (and (not fresh5) true) (= fresh7 x_finitevscpy_1))) (and (and fresh5 true) (= fresh6 x_finitevscpy_1))) (or (or (or false (and (and (not fresh5) true) (= fresh7 1))) (and (and fresh5 true) (= fresh6 1))) (or (or false (and (and (not fresh5) true) (= fresh7 0))) (and (and fresh5 true) (= fresh6 0))))))))))))))))))
)
 )
(check-sat)
(exit)