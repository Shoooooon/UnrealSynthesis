;test
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(set-logic NIA)
(declare-const fresh42 Int)
(declare-const fresh43 Int)
(declare-const fresh44 Int)
(declare-const fresh45 Int)
(declare-const fresh46 Int)
(declare-const fresh47 Int)
(declare-const fresh48 Int)
(declare-const fresh49 Int)
(declare-const fresh50 Int)
(declare-const fresh51 Int)
(declare-const fresh52 Int)
(declare-const fresh53 Int)
(declare-const fresh55 Int)
(declare-const fresh56 Int)
(declare-const fresh57 Int)
(declare-const fresh58 Int)
(declare-const fresh59 Int)
(declare-const fresh60 Int)
(declare-const fresh61 Int)
(declare-const fresh62 Int)
(declare-const fresh63 Int)
(declare-const fresh64 Int)
(declare-const fresh65 Int)
(declare-const fresh66 Int)
(declare-const x1_finitevscpy_1 Int)
(declare-const x1_finitevscpy_2 Int)
(declare-const x1_finitevscpy_3 Int)
(declare-const x1_finitevscpy_4 Int)
(declare-const x1_finitevscpy_5 Int)
(declare-const x1_finitevscpy_6 Int)
(declare-const x1_finitevscpy_7 Int)
(declare-const x1_finitevscpy_8 Int)
(declare-const x2_finitevscpy_1 Int)
(declare-const x2_finitevscpy_2 Int)
(declare-const x2_finitevscpy_3 Int)
(declare-const x2_finitevscpy_4 Int)
(declare-const x2_finitevscpy_5 Int)
(declare-const x2_finitevscpy_6 Int)
(declare-const x2_finitevscpy_7 Int)
(declare-const x2_finitevscpy_8 Int)
(declare-const x3_finitevscpy_1 Int)
(declare-const x3_finitevscpy_2 Int)
(declare-const x3_finitevscpy_3 Int)
(declare-const x3_finitevscpy_4 Int)
(declare-const x3_finitevscpy_5 Int)
(declare-const x3_finitevscpy_6 Int)
(declare-const x3_finitevscpy_7 Int)
(declare-const x3_finitevscpy_8 Int)
(assert
(not
(=> (and true (and (and (and (or (< 0 fresh53) (= 0 fresh53)) (and (or (< 0 fresh52) (= 0 fresh52)) (and (or (< 0 fresh51) (= 0 fresh51)) (or (< 0 fresh50) (= 0 fresh50))))) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_1) (+ (* fresh52 x2_finitevscpy_1) (* fresh51 x3_finitevscpy_1)))) fresh49) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_2) (+ (* fresh52 x2_finitevscpy_2) (* fresh51 x3_finitevscpy_2)))) fresh48) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_3) (+ (* fresh52 x2_finitevscpy_3) (* fresh51 x3_finitevscpy_3)))) fresh47) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_4) (+ (* fresh52 x2_finitevscpy_4) (* fresh51 x3_finitevscpy_4)))) fresh46) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_5) (+ (* fresh52 x2_finitevscpy_5) (* fresh51 x3_finitevscpy_5)))) fresh45) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_6) (+ (* fresh52 x2_finitevscpy_6) (* fresh51 x3_finitevscpy_6)))) fresh44) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_7) (+ (* fresh52 x2_finitevscpy_7) (* fresh51 x3_finitevscpy_7)))) fresh43) (and (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_8) (+ (* fresh52 x2_finitevscpy_8) (* fresh51 x3_finitevscpy_8)))) fresh42) (= (+ fresh50 (+ (* fresh53 x1_finitevscpy_8) (+ (* fresh52 x2_finitevscpy_8) (* fresh51 x3_finitevscpy_8)))) fresh42)))))))))) (and (and (or (< 0 fresh66) (= 0 fresh66)) (and (or (< 0 fresh65) (= 0 fresh65)) (and (or (< 0 fresh64) (= 0 fresh64)) (or (< 0 fresh63) (= 0 fresh63))))) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_1) (+ (* fresh65 x2_finitevscpy_1) (* fresh64 x3_finitevscpy_1)))) fresh62) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_2) (+ (* fresh65 x2_finitevscpy_2) (* fresh64 x3_finitevscpy_2)))) fresh61) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_3) (+ (* fresh65 x2_finitevscpy_3) (* fresh64 x3_finitevscpy_3)))) fresh60) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_4) (+ (* fresh65 x2_finitevscpy_4) (* fresh64 x3_finitevscpy_4)))) fresh59) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_5) (+ (* fresh65 x2_finitevscpy_5) (* fresh64 x3_finitevscpy_5)))) fresh58) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_6) (+ (* fresh65 x2_finitevscpy_6) (* fresh64 x3_finitevscpy_6)))) fresh57) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_7) (+ (* fresh65 x2_finitevscpy_7) (* fresh64 x3_finitevscpy_7)))) fresh56) (and (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_8) (+ (* fresh65 x2_finitevscpy_8) (* fresh64 x3_finitevscpy_8)))) fresh55) (= (+ fresh63 (+ (* fresh66 x1_finitevscpy_8) (+ (* fresh65 x2_finitevscpy_8) (* fresh64 x3_finitevscpy_8)))) fresh55)))))))))))) true)
)
 )
(check-sat)
(exit)