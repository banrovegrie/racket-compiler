(let ([v (vector 1 2 3 4 5)])
    (begin
        (vector-set! v 0 15)
        (vector-set! v 1 10)
        (vector-set! v 2 2)
        (vector-set! v 3 1)
        (vector-set! v 4 20)
        (+ (vector-ref v 0)
            (- (vector-ref v 1)
                (+ (vector-ref v 2)
                    (- (vector-ref v 3) (vector-ref v 4)))))))