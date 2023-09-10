(synth-fun eq1 ( (x1 Int) (x2 Int) (x3 Int) (x4 Int) (z Int)) Int ((Start Int (  
    3 
		x1 x2 x3 x4 z
             (+ Start Start)
             (ite StartBool Start Start)))
 (StartBool Bool (        (>= Start Start)      (>= Start Start)  ))
))
