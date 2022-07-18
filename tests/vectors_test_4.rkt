(let ([v (vector 0 1 2 3 4)])
	(begin
		(vector-set! v 2 5)
		(vector-set! v 1 2)
		(vector-ref v 1)))