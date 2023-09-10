( synth-fun max4  (       ( x  Int )  ( y  Int )  ( z  Int )  ( w  Int ) )  Int (
	(Start  Int (		x
		y
		z
		w
		0
		1
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT4 NT1)
		(ite NT3 NT5 NT1)
		(+ NT5 NT5)
		(ite NT3 NT1 NT1)
		(+ NT5 NT1)
))
	(NT1  Int (		x
		y
		z
		w
		0
		1
		(+ NT1 NT1)
))
	(NT2  Bool (		(<= NT1 NT1)
		(not NT2)
		(= NT5 NT1)
		(>= NT5 NT1)
))
	(NT3  Bool (		(= NT1 NT1)
		(>= NT1 NT1)
		(not NT3)
		(and NT3 NT3)
		(or NT3 NT3)
))
	(NT4  Int (		(ite NT2 NT1 NT1)
		(+ NT4 NT1)
		(ite NT3 NT5 NT1)
		(+ NT5 NT5)
))
	(NT5  Int (		(ite NT3 NT1 NT1)
		(+ NT5 NT1)
))
))
