;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh2 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and (and (and (and true (= x_finitevscpy_1 12)) (= y_finitevscpy_1 18)) (= z_finitevscpy_1 (- 15))) (or (= fresh2 (+ z_finitevscpy_1 z_finitevscpy_1)) (or (= fresh2 (+ z_finitevscpy_1 y_finitevscpy_1)) (or (= fresh2 (+ y_finitevscpy_1 y_finitevscpy_1)) (or (= fresh2 (+ z_finitevscpy_1 x_finitevscpy_1)) (or (= fresh2 (+ y_finitevscpy_1 x_finitevscpy_1)) (or (= fresh2 (+ x_finitevscpy_1 x_finitevscpy_1)) (or (= fresh2 (+ 1 z_finitevscpy_1)) (or (= fresh2 (+ 1 y_finitevscpy_1)) (or (= fresh2 (+ 1 x_finitevscpy_1)) (or (= fresh2 2) (or (= fresh2 z_finitevscpy_1) (or (= fresh2 y_finitevscpy_1) (or (= fresh2 x_finitevscpy_1) (or (= fresh2 1) (= fresh2 0)))))))))))))))) (not (and true (= fresh2 20))))
)
 )
(check-sat)
(exit)