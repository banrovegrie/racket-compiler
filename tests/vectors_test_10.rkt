(let ([v (vector 2 4 6 8 10 12)])
    (let ([i 0])
        (let ([ans 30])
            (begin
                (while (< i (vector-length v)) 
                    (begin
                        (set! ans (+ ans (vector-ref v 0)))
                        (set! i (+ i 1))
                    ) 
                )
                ans))))