(let ([x (> 5 3)]) (if (if (if (> 7 4) x (not x)) (eq? 6 7) (eq? 6 6)) 42 0)) 
