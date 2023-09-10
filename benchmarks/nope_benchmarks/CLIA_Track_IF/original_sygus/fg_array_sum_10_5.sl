(set-logic LIA)
( synth-fun findSum  (             ( x1  Int )  ( x2  Int )  ( x3  Int )  ( x4  Int )  ( x5  Int )  ( x6  Int )  ( x7  Int )  ( x8  Int )  ( x9  Int )  ( x10  Int ) )  Int (
	(Start  Int (		x1
		x2
		x3
		1
		x4
		x5
		x6
		x7
		x8
		x9
		x10
		0
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
		(+ NT4 NT4)
		(+ NT7 NT1)
		(ite NT5 NT4 NT1)
		(ite NT5 NT1 NT4)
		(ite NT2 NT8 NT1)
		(ite NT15 NT1 NT1)
		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT8 NT1)
		(+ NT9 NT1)
		(ite NT2 NT7 NT1)
		(ite NT6 NT4 NT1)
		(ite NT6 NT1 NT4)
		(ite NT12 NT1 NT1)
		(ite NT5 NT8 NT1)
		(+ NT10 NT1)
		(ite NT2 NT9 NT1)
		(ite NT5 NT4 NT4)
		(ite NT5 NT7 NT1)
		(ite NT6 NT8 NT1)
		(+ NT8 NT8)
		(ite NT16 NT1 NT1)
		(+ NT11 NT1)
		(ite NT2 NT10 NT1)
		(ite NT6 NT4 NT4)
		(ite NT6 NT7 NT1)
		(ite NT5 NT9 NT1)
		(ite NT17 NT1 NT1)
		(+ NT7 NT7)
		(ite NT2 NT11 NT1)
		(+ NT13 NT1)
		(ite NT6 NT9 NT1)
		(ite NT5 NT10 NT1)
		(ite NT18 NT1 NT1)
		(ite NT12 NT8 NT1)
		(ite NT12 NT1 NT8)
))
	(NT1  Int (		x1
		x2
		x3
		1
		x4
		x5
		x6
		x7
		x8
		x9
		x10
		0
		(+ NT1 NT1)
))
	(NT2  Bool (		(<= NT1 NT1)
		(not NT2)
		(and NT2 NT2)
		(or NT2 NT2)
))
	(NT3  Int (		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
))
	(NT4  Int (		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
))
	(NT5  Bool (		(<= NT3 NT1)
		(not NT5)
		(and NT5 NT2)
		(or NT5 NT2)
))
	(NT6  Bool (		(<= NT4 NT1)
		(<= NT3 NT3)
		(not NT6)
		(and NT6 NT2)
		(or NT6 NT2)
		(and NT5 NT5)
		(or NT5 NT5)
))
	(NT7  Int (		(+ NT4 NT4)
		(+ NT7 NT1)
		(ite NT5 NT4 NT1)
		(ite NT5 NT1 NT4)
		(ite NT2 NT8 NT1)
		(ite NT15 NT1 NT1)
))
	(NT8  Int (		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT8 NT1)
))
	(NT9  Int (		(+ NT9 NT1)
		(ite NT2 NT7 NT1)
		(ite NT6 NT4 NT1)
		(ite NT6 NT1 NT4)
		(ite NT12 NT1 NT1)
		(ite NT5 NT8 NT1)
))
	(NT10  Int (		(+ NT10 NT1)
		(ite NT2 NT9 NT1)
		(ite NT5 NT4 NT4)
		(ite NT5 NT7 NT1)
		(ite NT6 NT8 NT1)
		(+ NT8 NT8)
		(ite NT16 NT1 NT1)
))
	(NT11  Int (		(+ NT11 NT1)
		(ite NT2 NT10 NT1)
		(ite NT6 NT4 NT4)
		(ite NT6 NT7 NT1)
		(ite NT5 NT9 NT1)
		(ite NT17 NT1 NT1)
))
	(NT12  Bool (		(<= NT4 NT4)
		(<= NT7 NT1)
		(and NT6 NT6)
		(or NT6 NT6)
		(not NT12)
		(and NT12 NT2)
		(or NT12 NT2)
))
	(NT13  Int (		(+ NT7 NT7)
		(ite NT2 NT11 NT1)
		(+ NT13 NT1)
		(ite NT6 NT9 NT1)
		(ite NT5 NT10 NT1)
		(ite NT18 NT1 NT1)
		(ite NT12 NT8 NT1)
		(ite NT12 NT1 NT8)
))
	(NT15  Bool (		(<= NT8 NT1)
		(not NT15)
		(and NT15 NT2)
		(or NT15 NT2)
))
	(NT16  Bool (		(<= NT9 NT1)
		(not NT16)
		(and NT16 NT2)
		(or NT16 NT2)
))
	(NT17  Bool (		(<= NT10 NT1)
		(<= NT8 NT8)
		(not NT17)
		(and NT17 NT2)
		(or NT17 NT2)
		(and NT15 NT15)
		(or NT15 NT15)
))
	(NT18  Bool (		(<= NT11 NT1)
		(not NT18)
		(and NT18 NT2)
		(or NT18 NT2)
))
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
(constraint (=> (> (+ x1 x2) 5) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x1 x2))))
(constraint (=> (and (<= (+ x1 x2) 5) (> (+ x2 x3) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x2 x3))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (<= (+ x2 x3) 5)) (> (+ x3 x4) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x3 x4))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (<= (+ x3 x4) 5))) (> (+ x4 x5) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x4 x5))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (<= (+ x4 x5) 5)))) (> (+ x5 x6) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x5 x6))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (and (<= (+ x4 x5) 5) (<= (+ x5 x6) 5))))) (> (+ x6 x7) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x6 x7))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (and (<= (+ x4 x5) 5) (and (<= (+ x5 x6) 5) (<= (+ x6 x7) 5)))))) (> (+ x7 x8) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x7 x8))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (and (<= (+ x4 x5) 5) (and (<= (+ x5 x6) 5) (and (<= (+ x6 x7) 5) (<= (+ x7 x8) 5))))))) (> (+ x8 x9) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x8 x9))))
(constraint (=> (and (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (and (<= (+ x4 x5) 5) (and (<= (+ x5 x6) 5) (and (<= (+ x6 x7) 5) (and (<= (+ x7 x8) 5) (<= (+ x8 x9) 5)))))))) (> (+ x9 x10) 5)) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) (+ x9 x10))))
(constraint (=> (and (<= (+ x1 x2) 5) (and (<= (+ x2 x3) 5) (and (<= (+ x3 x4) 5) (and (<= (+ x4 x5) 5) (and (<= (+ x5 x6) 5) (and (<= (+ x6 x7) 5) (and (<= (+ x7 x8) 5) (and (<= (+ x8 x9) 5) (<= (+ x9 x10) 5))))))))) (= (findSum x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 ) 0)))
(check-synth)
