(begin
  (while (and #t (< (read) 42)) (void))
  (if (eq? (read) (read)) 3 4)
)