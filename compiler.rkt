#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require graph)
(provide (all-defined-out))

(define (insert-between v xs)
  (cond ((null? xs) xs)
        ((null? (cdr xs)) xs)
        (else (cons (car xs)
                    (cons v (insert-between v (cdr xs)))))))

(define (display-all . vs)
  (for-each display (insert-between " " vs)))

(define (is-atomic? e)
  (match e
    [(Int n) #t]
    [(Var x) #t]
    [_ #f]))

(define regmap (make-hash `(
                            (rax -1)
                            (rsp -2)
                            (rbp -3)
                            (r11 -4)
                            (r15 -5)
                            (rcx 0)
                            (rdx 1)
                            (rsi 2)
                            (rdi 3)
                            (r8 4)
                            (r9 5)
                            (r10 6)
                            (rbx 7)
                            (r12 8)
                            (r13 9)
                            (r14 10))))

(define (uniquify p)
  (define (uniquify-e e [ht (make-hash)])
    (match e
      [(Int n) (Int n)]
      [(Var x) (cond
                 [(hash-has-key? ht x) (Var (hash-ref ht x))]
                 [else (Var x)]
                 )]
      [(Let x exp body)
       (let ([exp_new (uniquify-e exp ht)] [x_new (gensym x)])
         (begin
           (hash-set! ht x x_new)
           (Let x_new exp_new (uniquify-e body ht))
           ))]
      [(Prim op es) (Prim op (for/list ([i es]) (uniquify-e i ht)))]
      [_ (error "Nothing matches")]))
  (match p
    [(Program info body)
     (Program info (uniquify-e body))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  
  (define (flatten e [varlst '()])
    ;;(display-all " e " e)
    (match e
      [(? is-atomic? i) (list i varlst)]
      [(Let x exp body) (list (let ([fb (flatten body)] [fe (flatten exp)])
                                (begin (set! varlst (append (cadr fe) (list (list x (car fe))) (cadr fb)))
                                       (car fb))) varlst)]
      [(Prim op es) (list (Prim op (for/list ([i es])
                                     (cond
                                       [(is-atomic? i) i]
                                       [else
                                        (let ([new_var (gensym 'g)] [ret_lst (flatten i)])
                                          (begin (set! varlst (append (cadr ret_lst) (list (list new_var (car ret_lst))) varlst ))
                                                 (Var new_var))
                                          )]))) varlst)]
      ))

  (define (final-flat e)
    (let ([fexpr (flatten e)])
      ;;(display-all " fexpr " fexpr)
      (define (final-flat-r lst)
        ;;(display-all " lst " lst)
        (cond
          [(null? lst) (car fexpr)]
          [else
           ;;(display-all "caar " (caar lst) " cadr " (cadr (car lst)))
           (Let (caar lst) (cadr (car lst)) (final-flat-r (cdr lst)))]))
      (final-flat-r (cadr fexpr))))

  (match p
    [(Program info body) (Program info (final-flat body))])
  )  

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (define (explicate-control-e e)
    (match e
      [(Let x exp body) (Seq (Assign (Var x) exp) (explicate-control-e body))]
      [_ (Return e)]
      )
    )
  (match p
    [(Program info body) (CProgram info `((start . , (explicate-control-e body))))])
  )

;; select-instructions
(define (select_instructions p)
  (define (convert e)
    ;(display-all " e " e)
    (match e
      [(Int n) (Imm n)]
      [(Var r) (Var r)]
      [(Seq exp tail) (append (convert exp) (convert tail))]
      [(Prim `read lst) (list (Callq `read_int 0))]
      [(Prim op es) (append 
                     (list (Instr `movq (list (convert (car es)) (Reg `rax))))
                     (cond
                       [(and (equal? `- op)(equal? (length es) 1)) (list (Instr `negq (list (Reg `rax))))]
                       [else `()]
                       )
                     (for/list ([i (cdr es)])
                       (cond
                         [(equal? '+ op) (Instr `addq (list (convert i) (Reg `rax)))]
                         [(equal? '- op) (Instr `subq (list (convert i) (Reg `rax)))])))]
      [(Assign x val) (cond [(is-atomic? val) (list (Instr `movq (list (convert val) (convert x))))]
                            [else (append (convert val) (list (Instr `movq (list (Reg `rax) x))))])]
      [(Return e) (cond
                    [(is-atomic? e) (list (Instr `movq (list (convert e) (Reg `rax))))]
                    [else
                     (convert e)])]))

  (match p
    [(CProgram info `((start . , body))) (X86Program info (hash 'start (Block '() (append (convert body) (list (Jmp `conclusion))))))])
  )

;; uncover live
(define (uncover_live p)

  (define gset set)

  (define (get-set read write prev_set)
   
    (let ([x (set-union (set-subtract prev_set write) read)])
      (set-remove (for/set ([i x])
                    (match i
                      [(Imm n) `()]
                      [_ i])) `()))
    )

  (define (calc instr prev_set)
    (match instr
      [(Instr 'movq lst) (get-set (set (car lst)) (set (cadr lst)) prev_set)]
      [(Instr 'addq lst) (get-set (set (car lst) (cadr lst)) (set (cadr lst)) prev_set)]
      [(Instr 'subq lst) (get-set (set (car lst) (cadr lst)) (set (cadr lst)) prev_set)]
      [(Instr 'negq lst) (get-set (set (car lst)) (set (car lst)) prev_set)]
      [(Jmp label) (get-set (set (Reg 'rax) (Reg 'rsp)) (set) (prev_set))]
      ))
  
  (define (aux b)
    (match b
      [(Block info body) (for/list ([instr (reverse body)]) (let ([lafter (calc instr gset)])
                                                              (begin
                                                                (set! gset lafter)
                                                                lafter)))]
      )
    )
  
  (match p
    [(X86Program info body) (let ([x (reverse (aux (hash-ref body `start)))] [ht (make-hash)])
                              (begin
                                (hash-set! ht 'live x)
                                (X86Program ht body)))])
  )


;; build interference
(define (build_interference p)

  (define g (undirected-graph '()))
  
  (define (add-edges write lafter)
    (for ([l (set-subtract lafter (set write))]) (add-edge! g write l))
    )

  (define (aux b l)
    (match b
      [(Block info body) (for ([instr body] [lafter l])
                           ;;(begin
                           ;;(display-all "Edges " (get-edges g) "Instr " instr)
                           (match instr
                             [(Instr `movq (list (Imm x) n)) (add-edges n lafter)]
                             [(Instr `movq (list m n)) (add-edges n (set-subtract lafter (set m)))]
                             [(Instr label lst) (add-edges (last lst) lafter)]
                             [(Jmp label) (add-edge! g (Reg 'rax) (Reg 'rsp))]
                             ))]
      ))
  
  
  (match p
    [(X86Program info body) (let ([x (aux (hash-ref body `start) (hash-ref info `live))])
                              (begin
                                (hash-set! info 'conflicts g)
                                (hash-set! info 'edges (get-edges g))
                                (X86Program info body)))])
  )

;;allocate registers
(define (allocate_registers p)

  (define (get-color s c)
    (cond
      [(set-member? s c) (get-color s (+ c 1))]
      [else c])
    )
  
  (define (color-graph pq colored neighbors graph)
    
    (cond
      [(equal? 0 (pqueue-count pq)) colored]
      [else (let ([x (cadr (pqueue-pop! pq))])
              
              (begin
                (cond
                  [(hash-has-key? colored x) `()]
                  [else
                   
                   (let ([c (get-color (hash-ref neighbors x) 0)])
                     
                     (begin
                       (hash-set! colored x c)
                       (for ([side (get-neighbors graph x)])
                         (cond
                           [(hash-has-key? colored side) `()]
                           [else (begin
                                   (hash-set! neighbors side (set-add (hash-ref neighbors side) c))
                                   (pqueue-push! pq (list (length (set->list (hash-ref neighbors side))) side)))])
                         )
                       ))])
                (color-graph pq colored neighbors graph)

                ))])
    )

  (define (init graph)

    (define pq (make-pqueue (lambda (x y) (>= (car x) (car y)))))
    (define colored (make-hash))
    (define neighbors (make-hash))


    (begin
      ;; coloring initialisation
      (for ([node (get-vertices graph)])
        (match node
          [(Reg r) (begin
                     ;; each register has color set
                     (hash-set! colored (Reg r) (hash-ref regmap r))

                     ;; each node has saturation set
                     (for ([side (get-neighbors graph (Reg r))])
                       (cond
                         [(hash-has-key? colored side) `()]
                         [(hash-has-key? neighbors side) (hash-set! neighbors side (set-add (hash-ref neighbors side) (hash-ref colored (Reg r))))]
                         [else
                          (hash-set! neighbors side (set (hash-ref colored (Reg r))))])))]
          [_ `()]))

      ; pqueue initialisation
      (for ([node (get-vertices graph)])
        (cond
          [(hash-has-key? colored node) `()]
          [else
           (begin
             (pqueue-push! pq (list (length (set->list (hash-ref neighbors node))) node))
             `())]))

      (color-graph pq colored neighbors graph)
      
      ))
  
  (match p
    [(X86Program info body) (let ([x (init (hash-ref info `conflicts))])
                              (display x))]))

;; assign homes
(define (assign_homes p)

  (define (replace e [ht (make-hash)])
    (match e
      [(Block info instr) (list
                           (for/list ([i instr])
                             (let ([x (replace i ht)])
                               (begin
                                 (set! ht (cadr x))
                                 (car x))))
                           ht)]
      [(Instr label lst) (list
                          (Instr label
                                 (for/list ([i lst])
                                   (match i
                                     [(Var x) (cond
                                                [(hash-has-key? ht i) (hash-ref ht i)]
                                                [else
                                                 (begin
                                                   (hash-set! ht i (Deref `rbp (* -8 (+ 1 (length (hash-keys ht))))))
                                                   (hash-ref ht i))])]
                                     [_ i])))
                          ht)]
      [(Callq label n) (list (Callq label n) ht)]
      [(Jmp label) (list (Jmp label) ht)]))
                           

  (match p
    [(X86Program info body) (let ([x (replace (hash-ref body `start))])
                              (begin
                                (hash-set! info 'stack-space (* (ceiling (/ (length (hash-keys (cadr x))) 2)) 16))
                                (X86Program info (hash `start (Block `() (car x))))))])
  )

;; patch instructions
(define (patch_instructions p)
  (define (patchify e [varlst '()])
    (match e
      [(Block info instr) (foldl (lambda (i l) (append l (patchify i))) `() instr)]
      [(Instr label lst) (cond
                           [(equal? 1 (length lst)) (list (Instr label lst))]
                           [else
                            (match lst
                              [(list (Deref reg1 val1) (Deref reg2 val2))
                               (list
                                (Instr 'movq (list (Deref reg1 val1) (Reg 'rcx)))
                                (Instr label (list (Reg 'rcx) (Deref reg2 val2)))
                                )]
                              [(list (Imm int1) (Deref reg1 val1)) (cond
                                                                     [(> int1 (expt 2 16))
                                                                      (list
                                                                       (Instr `movq (list (Imm int1) (Reg `rcx)))
                                                                       (Instr label (list (Reg `rcx) (Deref reg1 val1))))]
                                                                     [else (list (Instr label lst))])]
                              [_ (list (Instr label lst))])]
                           )]
      [(Callq label n) (list (Callq label n))]
      [(Jmp label) (list (Jmp label))])) 
  (match p
    [(X86Program info body) (X86Program info (hash 'start (Block '() (patchify (hash-ref body `start)))))])
  )

;; prelude and conclude
(define (prelude-and-conclusion p)
  (define (get-prelude sspace)
    (list
     (Instr `pushq (list (Reg `rbp)))
     (Instr `movq (list (Reg `rsp) (Reg `rbp)))
     (Instr `subq (list (Imm sspace) (Reg `rsp)))
     (Jmp `start)
     ))

  (define (get-conclusion sspace)
    (list
     (Instr `addq (list (Imm sspace) (Reg `rsp)))
     (Instr `popq (list (Reg `rbp)))
     (Retq)))

  (match p
    [(X86Program info body) (X86Program info (hash `start (hash-ref body `start)
                                                   `main (Block `() (get-prelude (hash-ref info `stack-space)))
                                                   `conclusion (Block `() (get-conclusion (hash-ref info `stack-space)))))])
  )
  
;; Define the compiler passes to be used by interp-tests and they grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection", select_instructions, interp-pseudo-x86-0)
    ("uncover life", uncover_live, interp-x86-0)
    ("build interference", build_interference, interp-x86-0)
    ("allocate registers", allocate_registers, interp-x86-0)
    ;("assign homes", assign_homes, interp-x86-0)
    ;("patch instructions", patch_instructions, interp-x86-0)
    ;("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
    ))
