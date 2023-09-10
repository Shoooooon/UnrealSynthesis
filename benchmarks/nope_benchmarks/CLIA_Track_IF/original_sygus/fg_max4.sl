(set-logic LIA)
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

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var w Int)

(constraint (>= (max4 x y z w) x))
(constraint (>= (max4 x y z w) y))
(constraint (>= (max4 x y z w) z))
(constraint (>= (max4 x y z w) w))
(constraint (or (= x (max4 x y z w))
            (or (= y (max4 x y z w))
            (or (= z (max4 x y z w))
	        (= w (max4 x y z w))))))

(check-synth)

