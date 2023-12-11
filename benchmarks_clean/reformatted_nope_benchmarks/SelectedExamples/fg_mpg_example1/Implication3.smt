;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const x_finitevscpy_1 Int)
(declare-const x_finitevscpy_2 Int)
(declare-const x_finitevscpy_3 Int)
(declare-const y_finitevscpy_1 Int)
(declare-const y_finitevscpy_2 Int)
(declare-const y_finitevscpy_3 Int)
(assert
(not
(=> true (exists ((c Int) ) (exists ((b Int) ) (exists ((a Int) ) (and (and (or (< 0 a) (= 0 a)) (and (or (< 0 b) (= 0 b)) (or (< 0 c) (= 0 c)))) (and (= (+ c (+ (* a x_finitevscpy_1) (* b y_finitevscpy_1))) y_finitevscpy_1) (and (= (+ c (+ (* a x_finitevscpy_2) (* b y_finitevscpy_2))) y_finitevscpy_2) (= (+ c (+ (* a x_finitevscpy_3) (* b y_finitevscpy_3))) y_finitevscpy_3))))))))
)
 )
(check-sat)
(exit)