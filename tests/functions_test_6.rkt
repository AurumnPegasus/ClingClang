 (define (id1 [x : Integer] [y : Integer]) : Integer (+ x y))
 (define (id2 [x : Integer] [y : Integer]) : Integer (- x y))
 (+ (id1 4 2) (id2 4 2))
