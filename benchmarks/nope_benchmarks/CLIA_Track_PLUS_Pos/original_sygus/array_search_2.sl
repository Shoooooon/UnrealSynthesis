(set-logic LIA)
(synth-fun findIdx ( (x1 Int) (x2 Int) (k Int)) Int (
	(Start  Int (		NT1
		NT3
))
	(NT1  Int (		x1
		x2
		0
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
	
	(NT7  Bool (		(>= NT3 NT1)
		(and NT7 NT4)
))

))
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var k Int)
(constraint (= (findIdx x1 x2 k) (ite (and (< x1 x2) (< k x1)) 
					1
					(ite (and (< x1 x2) (> k x2))
						3
						(ite (and (< x1 x2) (and (< k x2) (> k  x1)))
							2 0) ))))
(check-synth)
