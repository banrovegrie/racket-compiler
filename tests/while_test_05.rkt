(let ([x (read)])
  (let ([y (read)])
    (+ (+ (begin
            (set! y (read))
            x)
          (begin
            (set! x (read))
            y))
       (+ x y))))
