;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh1_finitevscpy_1 Bool)
(declare-const fresh2_finitevscpy_1 Int)
(declare-const fresh3_finitevscpy_1 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const z_finitevscpy_1 Int)
(assert
(not
(=> (and true (and true (and (or (= fresh2_finitevscpy_1 0) (or (= fresh2_finitevscpy_1 1) (or (= fresh2_finitevscpy_1 x_finitevscpy_1) (or (= fresh2_finitevscpy_1 y_finitevscpy_1) (= fresh2_finitevscpy_1 z_finitevscpy_1))))) (or (= fresh3_finitevscpy_1 0) (or (= fresh3_finitevscpy_1 1) (or (= fresh3_finitevscpy_1 x_finitevscpy_1) (or (= fresh3_finitevscpy_1 y_finitevscpy_1) (= fresh3_finitevscpy_1 z_finitevscpy_1)))))))) (or (or (or false (and (and (not fresh1_finitevscpy_1) true) (= fresh3_finitevscpy_1 0))) (and (and fresh1_finitevscpy_1 true) (= fresh2_finitevscpy_1 0))) (or (or (or false (and (and (not fresh1_finitevscpy_1) true) (= fresh3_finitevscpy_1 1))) (and (and fresh1_finitevscpy_1 true) (= fresh2_finitevscpy_1 1))) (or (or (or false (and (and (not fresh1_finitevscpy_1) true) (= fresh3_finitevscpy_1 x_finitevscpy_1))) (and (and fresh1_finitevscpy_1 true) (= fresh2_finitevscpy_1 x_finitevscpy_1))) (or (or (or false (and (and (not fresh1_finitevscpy_1) true) (= fresh3_finitevscpy_1 y_finitevscpy_1))) (and (and fresh1_finitevscpy_1 true) (= fresh2_finitevscpy_1 y_finitevscpy_1))) (or (or false (and (and (not fresh1_finitevscpy_1) true) (= fresh3_finitevscpy_1 z_finitevscpy_1))) (and (and fresh1_finitevscpy_1 true) (= fresh2_finitevscpy_1 z_finitevscpy_1))))))))
)
 )
(check-sat)
(exit)