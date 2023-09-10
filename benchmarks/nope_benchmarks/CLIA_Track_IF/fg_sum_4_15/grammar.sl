( synth-fun findSum  (       ( x1  Int )  ( x2  Int )  ( x3  Int )  ( x4  Int ) )  Int (
	(Start  Int (		x1
		x2
		x3
		x4
		0
		1
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
))
	(NT1  Int (		x1
		x2
		x3
		x4
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
	(NT4  Int (		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
))
	(NT5  Bool (		(<= NT3 NT1)
		(= NT3 NT1)
		(>= NT3 NT1)
		(not NT5)
		(and NT5 NT2)
		(or NT5 NT2)
))
))
