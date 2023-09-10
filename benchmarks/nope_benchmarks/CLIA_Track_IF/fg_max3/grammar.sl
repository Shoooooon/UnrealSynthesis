( synth-fun eq1  (      ( x  Int )  ( y  Int )  ( z  Int ) )  Int (
	(Start  Int (		x
		y
		0
		1
		z
		(+ NT1 NT1)
		(ite NT3 NT1 NT1)
		(+ NT4 NT1)
))	(NT1  Int (		x
		y
		0
		1
		z
		(+ NT1 NT1)
))
	(NT3  Bool (		(>= NT1 NT1)
		(<= NT1 NT1)
))
	(NT4  Int (		(ite NT3 NT1 NT1)
		(+ NT4 NT1)
))
))
