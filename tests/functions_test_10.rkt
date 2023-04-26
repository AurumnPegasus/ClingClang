(define (add [x : Integer] [x2 : Integer] [x3 : Integer] [x4 : Integer] [x5 : Integer] [x6 : Integer] [x7 : Integer] [x8 : Integer]) : Integer
  (+ x (+ x2 (+ x3 (+ x4 (+ x5 (+ x6 (+ x7 x8))))))))

(add 0 0 7 7 7 7 7 7)
