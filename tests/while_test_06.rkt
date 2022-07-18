(let ([sum (read)])
  (let ([i (read)])
    (begin
      (while (>= i 1)
             (begin
               (set! sum (+ sum (read)))
               (set! i (- i 12))))
      sum)))
