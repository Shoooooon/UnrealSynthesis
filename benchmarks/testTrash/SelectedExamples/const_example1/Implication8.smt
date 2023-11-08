;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh3 Int)
(declare-const fresh4 Int)
(declare-const x_finitevscpy_1 Int)
(declare-const y_finitevscpy_1 Int)
(assert
(not
(=> (and true (and (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh3 0) (< 1 fresh3))) (=> (and (= x_finitevscpy_1 0) (= y_finitevscpy_1 0)) (or (= fresh4 0) (< 1 fresh4))))) true)
)
 )
(check-sat)
(exit)