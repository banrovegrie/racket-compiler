(define (answer [x : (Vector Integer)]) : Integer
  (begin
    (vector-set! x 0 42)
    (vector-ref x 0)))
    
(let ([v (vector 0)]) (answer v))