(let ([sum 42])
(let ([n 12])
  (let ([i 1])
    (let ([ans 10])
      (begin
        (while (<= i n)
               (begin
                 (set! sum (+ sum i))
                 (set! i (+ i 1))))
        ans)))))
