(set-logic LIA)
(synth-fun findIdx ( (x1 Int) (x2 Int) (x3 Int) (k Int)) Int (
	(Start  Int (		NT1
		NT3
		NT5
))
	(NT1  Int (		x1
		x2
		0
		x3
        k
		1
		(ite NT4 NT1 NT1)
))
	(NT3  Int (		(+ NT1 NT1)
		(ite NT4 NT3 NT1)
		(ite NT4 NT1 NT3)
		(ite NT7 NT1 NT1)
))
	(NT4  Bool (		(>= NT1 NT1)
		(and NT4 NT4)
))
	(NT5  Int (		(+ NT3 NT1)
		(ite NT4 NT3 NT3)
		(ite NT8 NT1 NT1)
		(ite NT4 NT5 NT1)
))
	(NT7  Bool (		(>= NT3 NT1)
		(and NT7 NT4)
))
	(NT8  Bool (		(>= NT3 NT3)
		(>= NT5 NT1)
		(and NT8 NT4)
		(and NT7 NT7)
))
) )
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var k Int)
(constraint (= (findIdx x1 x2 x3 k) (ite (and (and (< x1 x2) (< x2 x3)) (< k x1)) 
					1
					(ite (and (and (< x1 x2) (< x2 x3)) (> k x3))
						4
						(ite (and (and (< x1 x2) (< x2 x3)) (and (< k x2) (> k  x1)))
							2 (ite (and (and (< x1 x2) (< x2 x3)) (and (< k x3) (> k  x2)))
							3 0)) ))))
(check-synth)
