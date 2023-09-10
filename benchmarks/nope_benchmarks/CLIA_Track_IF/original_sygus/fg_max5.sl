
(set-logic LIA)
( synth-fun max5  (        ( x  Int )  ( y  Int )  ( z  Int )  ( w  Int )  ( u  Int ) )  Int (
	(Start  Int (		x
		y
		z
		w
		u
		0
		1
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT7 NT1)
))
	(NT1  Int (		x
		y
		z
		w
		u
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
	(NT7  Int (		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT7 NT1)
))
))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)
(declare-var u Int)

(constraint (>= (max5 x y z w u) x))
(constraint (>= (max5 x y z w u) y))
(constraint (>= (max5 x y z w u) z))
(constraint (>= (max5 x y z w u) w))
(constraint (>= (max5 x y z w u) u))
(constraint (or (= x (max5 x y z w u))
            (or (= y (max5 x y z w u))
            (or (= z (max5 x y z w u))
            (or (= w (max5 x y z w u))
	        (= u (max5 x y z w u)))))))

(check-synth)


