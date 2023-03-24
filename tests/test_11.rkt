(let ([x 2]) (let ([y 3]) (let ([z 4]) (if (> x y) (if (> y z) 1 2) (if (not (eq? (+ x 7) z)) 3 4)))))
