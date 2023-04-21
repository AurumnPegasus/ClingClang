(define (fib [x : Integer]) : Integer
  (if (or (eq? x 1) (eq? x 0))
      1
      (+ (fib (- x 1)) (fib (- x 2)))))

(fib 7)
