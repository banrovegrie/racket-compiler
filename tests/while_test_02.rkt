(let ([sum 0])
  (let ([i 1])
    (begin
      (while (<= i 42)
             (begin
               (set! i (+ i 12))
               (set! sum (+ sum 1))
               (void)))
      sum)))
