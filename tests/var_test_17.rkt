(let ([ x
	(let ([x (read)]) (+ x 1))])
	(- (let ([x 41]) (+ x
		(let ([x (read)]) (- x
			(let ([x (read)]) (- x 2))))))
		(+ x 1)))