(set-logic LIA)
(synth-fun findSum ( (y1 Int) (y2 Int) )Int 
 ((Start Int (y1 y2  2
             (+ Start Start)
             (ite StartBool Start Start)))
 (StartBool Bool (           (not StartBool) (or StartBool)       (>= Start Start) (and StartBool StartBool) ))
))
(declare-var x1 Int)
(declare-var x2 Int)
(constraint (=> (> (+ x1 x2) 15) (= (findSum x1 x2 ) (+ x1 x2))))
(constraint (=> (<= (+ x1 x2) 15) (= (findSum x1 x2 ) 0)))
(check-synth)
