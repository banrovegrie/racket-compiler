(let ([ans 0])
  (let ([cntr 7])
    (begin
      (while (> cntr 0)
             (begin
               (set! ans (+ ans 6))
               (set! cntr (- cntr 1))))
      ans)))
