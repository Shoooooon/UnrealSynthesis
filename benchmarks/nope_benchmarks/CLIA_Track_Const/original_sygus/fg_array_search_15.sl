(set-logic LIA)
(synth-fun findIdx ( (y1 Int) (y2 Int) (y3 Int) (y4 Int) (y5 Int) (y6 Int) (y7 Int) (y8 Int) (y9 Int) (y10 Int) (y11 Int) (y12 Int) (y13 Int) (y14 Int) (y15 Int) (k1 Int)) Int ((Start Int (  
    3 
		y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15
	k1
             (+ Start Start)
             (ite StartBool Start Start)))
 (StartBool Bool (           (not StartBool) (or StartBool)       (>= Start Start) (and StartBool StartBool) ))
))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var x11 Int)
(declare-var x12 Int)
(declare-var x13 Int)
(declare-var x14 Int)
(declare-var x15 Int)
(declare-var k Int)
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (< k x1) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 0))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (> k x15) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 15))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x1) (< k x2)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 1))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x2) (< k x3)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 2))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x3) (< k x4)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 3))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x4) (< k x5)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 4))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x5) (< k x6)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 5))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x6) (< k x7)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 6))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x7) (< k x8)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 7))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x8) (< k x9)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 8))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x9) (< k x10)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 9))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x10) (< k x11)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 10))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x11) (< k x12)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 11))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x12) (< k x13)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 12))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x13) (< k x14)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 13))))
(constraint (=> (and (< x1 x2) (and (< x2 x3) (and (< x3 x4) (and (< x4 x5) (and (< x5 x6) (and (< x6 x7) (and (< x7 x8) (and (< x8 x9) (and (< x9 x10) (and (< x10 x11) (and (< x11 x12) (and (< x12 x13) (and (< x13 x14) (< x14 x15)))))))))))))) (=> (and (> k x14) (< k x15)) (= (findIdx x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 k) 14))))
(check-synth)
