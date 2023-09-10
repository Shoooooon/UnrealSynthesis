( synth-fun eq1  (      ( x  Int )  ( y  Int )  ( z  Int ) )  Int (
	(Start  Int (		x
		y
		z
		0
		1
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
))
	(NT1  Int (		x
		y
		z
		0
		1
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
))
