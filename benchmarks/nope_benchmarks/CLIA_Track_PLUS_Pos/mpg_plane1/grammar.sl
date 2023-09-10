
( synth-fun eq1  (     ( x  Int )  ( y  Int ) )  Int (
	(Start  Int (		x
		y
		0
		1
		(ite NT4 Start Start)
))
	(NT4  Bool (		(>= Start Start) (>= Start Start)
))
))
