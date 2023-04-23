(define (add [x : Integer]) : Integer (if (eq? x 0) 0 (+ x (add (- x 1)))))
(+ (add 6) (add 6))
