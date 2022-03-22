(let ([ x
	(let ([x 41]) (+ x 1))])
	(+ (let ([x 41])
		(+ x (let ([x 10]) (- x 1))))
	x))