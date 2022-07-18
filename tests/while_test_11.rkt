(let ([x 1])
  (begin
    (while (< x 10) (set! x (+ x 2)))
    (+ x 31)))
