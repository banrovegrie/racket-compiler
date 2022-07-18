(define (double [x : (Vector Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer) 
    (vector (vector-ref x 0) (vector-ref x 1) (vector-ref x 2) (vector-ref x 0) (vector-ref x 1) (vector-ref x 2))
  )

(define (add1 [x : Integer]) : Integer
    (+ x 1))

(define (sub1 [x : Integer]) : Integer
    (- x 1))

(sub1 (add1 (vector-ref (double (vector 1 2 42)) 5)))