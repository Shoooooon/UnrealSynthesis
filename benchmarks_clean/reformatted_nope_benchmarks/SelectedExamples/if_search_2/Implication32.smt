;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
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
(=> true (exists ((d Int) ) (exists ((c Int) ) (exists ((b Int) ) (exists ((a Int) ) (and (and (or (< 0 a) (= 0 a)) (and (or (< 0 b) (= 0 b)) (and (or (< 0 c) (= 0 c)) (or (< 0 d) (= 0 d))))) (and (= (+ d (+ (* a x_finitevscpy_1) (+ (* b y_finitevscpy_1) (* c z_finitevscpy_1)))) 0) (and (= (+ d (+ (* a x_finitevscpy_2) (+ (* b y_finitevscpy_2) (* c z_finitevscpy_2)))) 0) (and (= (+ d (+ (* a x_finitevscpy_3) (+ (* b y_finitevscpy_3) (* c z_finitevscpy_3)))) 0) (and (= (+ d (+ (* a x_finitevscpy_4) (+ (* b y_finitevscpy_4) (* c z_finitevscpy_4)))) 0) (= (+ d (+ (* a x_finitevscpy_5) (+ (* b y_finitevscpy_5) (* c z_finitevscpy_5)))) 0)))))))))))
)
 )
(check-sat)
(exit)