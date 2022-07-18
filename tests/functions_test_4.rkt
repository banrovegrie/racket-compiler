(define (add [x1 : Integer] [x2 : Integer] [x3 : Integer] [x4 : Integer] [x5 : Integer]) : Integer 
  (+ x1 (+ x2 (+ x3 (+ x4 x5)))))

(add 1 2 3 4 32)
