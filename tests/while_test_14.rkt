(let ([x 20])
  (begin
    (while (<= x 40)
           (begin
             (set! x (+ x 2))
             x))
    x))
