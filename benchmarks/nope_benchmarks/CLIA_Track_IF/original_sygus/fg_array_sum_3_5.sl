(set-logic LIA)
( synth-fun findSum  (      ( x1  Int )  ( x2  Int )  ( x3  Int ) )  Int (
	(Start  Int (		x1
		x2
		x3
		0
		1
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
))
	(NT1  Int (		x1
		x2
		x3
		0
		1
		(+ NT1 NT1)
))
	(NT2  Bool (		(<= NT1 NT1)
		(= NT1 NT1)
		(>= NT1 NT1)
		(not NT2)
		(and NT2 NT2)
		(or NT2 NT2)
))
	(NT3  Int (		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
))
))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(constraint (=> (> (+ x1 x2) 5) (= (findSum x1 x2 x3 ) (+ x1 x2))))
(constraint (=> (and (<= (+ x1 x2) 5) (> (+ x2 x3) 5)) (= (findSum x1 x2 x3 ) (+ x2 x3))))
(constraint (=> (and (<= (+ x1 x2) 5) (<= (+ x2 x3) 5)) (= (findSum x1 x2 x3 ) 0)))
(check-synth)
