(define (len [x : (Vector Integer Integer Integer Integer Integer Integer)]): Integer
    (vector-length x)
  )
(+ 36 (len (vector 1 2 3 4 5 6)))
