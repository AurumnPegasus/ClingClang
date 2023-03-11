(if (or (< (let ([x 4]) (let ([x 3]) x)) (let ([x 10]) x)) #f) 42 0)
