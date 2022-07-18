(let ([v (vector 1 2 3)])
	(let ([x (vector-set! v 0 5)])
		(begin
			(vector-set! v 1 42)
			(vector-ref v 1))))