(let ([a 26])
	(let ([b (+ a 5)])
		(let ([c (+ a (- b 5))])
			(let ([d (- c b)])
				(let ([e (+ (- d 5) (+ c 5))])
					(+ e (- d (+ c (- b (+ a 5))))))))))