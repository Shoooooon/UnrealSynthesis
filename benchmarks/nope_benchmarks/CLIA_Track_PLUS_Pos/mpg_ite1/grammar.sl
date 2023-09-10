( synth-fun eq1  (      ( x  Int )  ( y  Int )  ( z  Int ) )  Int (
	(Start  Int (		NT1
		NT3
))
	(NT1  Int (		x
		y
		0
		z
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
