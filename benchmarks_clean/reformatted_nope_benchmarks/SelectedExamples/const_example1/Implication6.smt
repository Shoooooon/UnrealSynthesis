;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh3 Bool)
(declare-const fresh3_finitevscpy_1 Int)
(declare-const fresh4 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(assert
(not
(=> (and true (and true (and (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh4 0) (< 1 fresh4))) (and (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh3_finitevscpy_1 0) (< 1 fresh3_finitevscpy_1))) (and (or (or false (and (and (not fresh3) true) (= x_finitevscpy_1 0))) (and (and fresh3 true) (= x_finitevscpy_1 0))) (or (or false (and (and (not fresh3) true) (= y_finitevscpy_1 0))) (and (and fresh3 true) (= y_finitevscpy_1 0)))))))) (or (or (or false (and (and (not fresh3) true) (= fresh3_finitevscpy_1 0))) (and (and fresh3 true) (= fresh4 0))) (or (or false (and (and (not fresh3) true) (< 1 fresh3_finitevscpy_1))) (and (and fresh3 true) (< 1 fresh4)))))
)
 )
(check-sat)
(exit)