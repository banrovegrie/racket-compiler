(let ([x (+ (read) 10)])
	(+ (read)
		(let ([y (- (read) 5)]) (- (+ x y)
			(read)))))