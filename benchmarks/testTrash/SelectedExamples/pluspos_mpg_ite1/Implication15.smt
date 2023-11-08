;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh8 Bool)
(declare-const fresh10 Int)
(declare-const fresh9 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and true (and true (and (or (= fresh9 0) (or (= fresh9 1) (or (= fresh9 x_finitevscpy_1) (or (= fresh9 y_finitevscpy_1) (= fresh9 z_finitevscpy_1))))) (or (= fresh10 0) (or (= fresh10 1) (or (= fresh10 x_finitevscpy_1) (or (= fresh10 y_finitevscpy_1) (= fresh10 z_finitevscpy_1)))))))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ z_finitevscpy_1 z_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ z_finitevscpy_1 z_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ z_finitevscpy_1 y_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ z_finitevscpy_1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ y_finitevscpy_1 y_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ y_finitevscpy_1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ z_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ z_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ y_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ y_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ x_finitevscpy_1 x_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ x_finitevscpy_1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ 1 z_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ 1 z_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ 1 y_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ 1 y_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 (+ 1 x_finitevscpy_1)))) (and (and fresh8 true) (= fresh9 (+ 1 x_finitevscpy_1)))) (or (or (or false (and (and (not fresh8) true) (= fresh10 2))) (and (and fresh8 true) (= fresh9 2))) (or (or (or false (and (and (not fresh8) true) (= fresh10 z_finitevscpy_1))) (and (and fresh8 true) (= fresh9 z_finitevscpy_1))) (or (or (or false (and (and (not fresh8) true) (= fresh10 y_finitevscpy_1))) (and (and fresh8 true) (= fresh9 y_finitevscpy_1))) (or (or (or false (and (and (not fresh8) true) (= fresh10 x_finitevscpy_1))) (and (and fresh8 true) (= fresh9 x_finitevscpy_1))) (or (or (or false (and (and (not fresh8) true) (= fresh10 1))) (and (and fresh8 true) (= fresh9 1))) (or (or false (and (and (not fresh8) true) (= fresh10 0))) (and (and fresh8 true) (= fresh9 0))))))))))))))))))
)
 )
(check-sat)
(exit)