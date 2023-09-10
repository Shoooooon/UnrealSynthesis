(set-logic LIA)

( synth-fun max12  (               ( x1  Int )  ( x2  Int )  ( x3  Int )  ( x4  Int )  ( x5  Int )  ( x6  Int )  ( x7  Int )  ( x8  Int )  ( x9  Int )  ( x10  Int )  ( x11  Int )  ( x12  Int ) )  Int (
	(Start  Int (		x1
		x2
		x3
		x12
		x4
		x5
		0
		x6
		x7
		x8
		x9
		1
		x10
		x11
		(+ NT1 NT1)
		(ite NT2 NT1 NT1)
		(+ NT3 NT1)
		(+ NT4 NT1)
		(+ NT3 NT3)
		(ite NT2 NT3 NT1)
		(ite NT5 NT1 NT1)
		(+ NT4 NT4)
		(+ NT7 NT1)
		(ite NT5 NT4 NT1)
		(ite NT5 NT1 NT4)
		(ite NT2 NT8 NT1)
		(ite NT17 NT1 NT1)
		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT8 NT1)
		(+ NT10 NT1)
		(ite NT2 NT9 NT1)
		(ite NT5 NT4 NT4)
		(ite NT5 NT7 NT1)
		(ite NT6 NT8 NT1)
		(+ NT8 NT8)
		(ite NT18 NT1 NT1)
		(+ NT7 NT7)
		(ite NT2 NT11 NT1)
		(+ NT13 NT1)
		(ite NT6 NT9 NT1)
		(ite NT5 NT10 NT1)
		(ite NT12 NT8 NT1)
		(ite NT12 NT1 NT8)
		(ite NT20 NT1 NT1)
		(+ NT15 NT1)
		(ite NT2 NT13 NT1)
		(ite NT6 NT10 NT1)
		(ite NT5 NT11 NT1)
		(ite NT16 NT1 NT1)
		(ite NT12 NT7 NT1)
		(ite NT12 NT1 NT7)
		(+ NT9 NT1)
		(ite NT2 NT7 NT1)
		(ite NT6 NT4 NT1)
		(ite NT6 NT1 NT4)
		(ite NT12 NT1 NT1)
		(ite NT5 NT8 NT1)
		(+ NT11 NT1)
		(ite NT2 NT10 NT1)
		(ite NT6 NT4 NT4)
		(ite NT6 NT7 NT1)
		(ite NT5 NT9 NT1)
		(ite NT19 NT1 NT1)
		(+ NT14 NT1)
		(+ NT9 NT9)
		(ite NT6 NT11 NT1)
		(ite NT2 NT15 NT1)
		(ite NT5 NT13 NT1)
		(ite NT12 NT9 NT1)
		(ite NT12 NT1 NT9)
		(ite NT22 NT1 NT1)
))
	(NT1  Int (		x1
		x2
		x3
		x12
		x4
		x5
		0
		x6
		x7
		x8
		x9
		1
		x10
		x11
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
	(NT7  Int (		(+ NT4 NT4)
		(+ NT7 NT1)
		(ite NT5 NT4 NT1)
		(ite NT5 NT1 NT4)
		(ite NT2 NT8 NT1)
		(ite NT17 NT1 NT1)
))
	(NT8  Int (		(ite NT2 NT4 NT1)
		(ite NT6 NT1 NT1)
		(+ NT8 NT1)
))
	(NT9  Int (		(+ NT9 NT1)
		(ite NT2 NT7 NT1)
		(ite NT6 NT4 NT1)
		(ite NT6 NT1 NT4)
		(ite NT12 NT1 NT1)
		(ite NT5 NT8 NT1)
))
	(NT10  Int (		(+ NT10 NT1)
		(ite NT2 NT9 NT1)
		(ite NT5 NT4 NT4)
		(ite NT5 NT7 NT1)
		(ite NT6 NT8 NT1)
		(+ NT8 NT8)
		(ite NT18 NT1 NT1)
))
	(NT11  Int (		(+ NT11 NT1)
		(ite NT2 NT10 NT1)
		(ite NT6 NT4 NT4)
		(ite NT6 NT7 NT1)
		(ite NT5 NT9 NT1)
		(ite NT19 NT1 NT1)
))
	(NT12  Bool (		(<= NT4 NT4)
		(<= NT7 NT1)
		(and NT6 NT6)
		(or NT6 NT6)
		(not NT12)
		(and NT12 NT2)
		(or NT12 NT2)
))
	(NT13  Int (		(+ NT7 NT7)
		(ite NT2 NT11 NT1)
		(+ NT13 NT1)
		(ite NT6 NT9 NT1)
		(ite NT5 NT10 NT1)
		(ite NT12 NT8 NT1)
		(ite NT12 NT1 NT8)
		(ite NT20 NT1 NT1)
))
	(NT14  Int (		(+ NT14 NT1)
		(+ NT9 NT9)
		(ite NT6 NT11 NT1)
		(ite NT2 NT15 NT1)
		(ite NT5 NT13 NT1)
		(ite NT12 NT9 NT1)
		(ite NT12 NT1 NT9)
		(ite NT22 NT1 NT1)
))
	(NT15  Int (		(+ NT15 NT1)
		(ite NT2 NT13 NT1)
		(ite NT6 NT10 NT1)
		(ite NT5 NT11 NT1)
		(ite NT16 NT1 NT1)
		(ite NT12 NT7 NT1)
		(ite NT12 NT1 NT7)
))
	(NT16  Bool (		(<= NT7 NT7)
		(<= NT13 NT1)
		(not NT16)
		(and NT16 NT2)
		(or NT16 NT2)
		(and NT12 NT12)
		(or NT12 NT12)
))
	(NT17  Bool (		(<= NT8 NT1)
		(not NT17)
		(and NT17 NT2)
		(or NT17 NT2)
))
	(NT18  Bool (		(<= NT9 NT1)
		(not NT18)
		(and NT18 NT2)
		(or NT18 NT2)
))
	(NT19  Bool (		(<= NT10 NT1)
		(<= NT8 NT8)
		(not NT19)
		(and NT19 NT2)
		(or NT19 NT2)
		(and NT17 NT17)
		(or NT17 NT17)
))
	(NT20  Bool (		(<= NT11 NT1)
		(not NT20)
		(and NT20 NT2)
		(or NT20 NT2)
))
	(NT22  Bool (		(<= NT15 NT1)
		(not NT22)
		(and NT22 NT2)
		(or NT22 NT2)
))
))

(declare-var x1 Int)
(declare-var x2 Int)
(declare-var x3 Int)
(declare-var x4 Int)
(declare-var x5 Int)
(declare-var x6 Int)
(declare-var x7 Int)
(declare-var x8 Int)
(declare-var x9 Int)
(declare-var x10 Int)
(declare-var x11 Int)
(declare-var x12 Int)


(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x1))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x2))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x3))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x4))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x5))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x6))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x7))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x8))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x9))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x10))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x11))
(constraint (>= (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12) x12))


(constraint (or (= x1 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x2 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x3 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x4 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x5 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x6 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x7 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x8 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x9 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x10 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
            (or (= x11 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))
                (= x12 (max12 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12))))))))))))))

(check-synth)

