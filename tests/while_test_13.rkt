(let ([x 21])
  (if (eq? (begin
             (set! x 20)
             x)
           20)
      42
      0))
