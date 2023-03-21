#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
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
    [(Bool b) #t]
    [_ #f]))

(define regmap (make-hash `(
                            (rax -1)
                            (-1 rax)
                            (rsp -2)
                            (-2 rsp)
                            (rbp -3)
                            (-3 rbp)
                            (r11 -4)
                            (-4 r11)
                            (r15 -5)
                            (-5 r15)
                            (rcx -6)
                            (-6 rcx)
                            (r14 0)
                            (0 r14)
                            (rdx 1)
                            (1 rdx)
                            (rsi 2)
                            (2 rsi)
                            (rdi 3)
                            (3 rdi)
                            (r8 4)
                            (4 r8)
                            (r9 5)
                            (5 r9)
                            (r10 6)
                            (6 r10)
                            (rbx 7)
                            (7 rbx)
                            (r12 8)
                            (8 r12)
                            (r13 9)
                            (9 r13)
                            )))
(define numpos 10)


(define caller-reg (set `rax `rcx `rdx `rsi `rdi `r8 `r9 `r10 `r11))
(define callee-reg (set `rsp `rbp `rbx `r12 `r13 `r14 `r15))

(define (shrink p)
  (define (shrink-e e)
    ;(display-all " e " e)
    (match e
      [(Prim `and (list e1 e2)) (If (shrink-e e1) (shrink-e e2) (Bool #f))]
      [(Prim `or (list e1 e2)) (If (shrink-e e1) (Bool #t) (shrink-e e2))]
      [(Prim op es) (Prim op (for/list ([i es]) (shrink-e i)))]
      [(If cnd thn els) (If (shrink-e cnd) (shrink-e thn) (shrink-e els))]
      [(Let x exp body) (Let x (shrink-e exp) (shrink-e body))]
      [_ e])
    )
  (match p
    [(Program info body) (Program info (shrink-e body))]))


(define (uniquify p)
  (define (uniquify-e e [ht (make-hash)])
    (match e
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
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
      [(If cnd thn els) (If (uniquify-e cnd ht) (uniquify-e thn ht) (uniquify-e els ht))]
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
      [(If cnd thn els) (list (let ([fcnd (flatten cnd)] [fthn (flatten thn)] [fels (flatten els)])
                                (begin (set! varlst (append (cadr fcnd) (cadr fthn) (cadr fels)))
                                       (If (car fcnd) (car fthn) (car fels)))) varlst)]
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
      ;(display-all " fexpr " fexpr)
      (define (final-flat-r lst)
        ;(display-all " lst " lst)
        (cond
          [(null? lst) (car fexpr)]
          [else     
           (Let (caar lst) (cadr (car lst)) (final-flat-r (cdr lst)))]))
      (final-flat-r (cadr fexpr))))

  (match p
    [(Program info body) (Program info (final-flat body))])
  )  

;; explicate-control : R1 -> C0
(define (explicate-control p)

  (define all-blocks (make-hash))
  
  (define (create-block b)
    (cond
      [(hash-has-key? all-blocks b)]
      [else (hash-set! all-blocks b null)]
      ))
  
  (define (explicate-control-e e block [control '()])
    ;(display-all "e: " e "start: " (hash-ref all-blocks 'start))
    (match e
      [(Let x exp body) (begin (hash-set! all-blocks block
                                          (append (hash-ref all-blocks block)
                                                  (list (Assign (Var x) exp))))
                               (explicate-control-e body block))]

      [(If cnd thn els) (let ([bthn (gensym 'block)] [bels (gensym 'block)])
                          (match cnd
                            [(Var x) (begin
                                       (create-block bthn)
                                       (create-block bels)
                                       (explicate-control-e thn bthn control)
                                       (explicate-control-e els bels control)
                                       (hash-set! all-blocks block
                                                  (append
                                                   (hash-ref all-blocks block)
                                                   (list (IfStmt (Prim 'eq? (list cnd (Bool #t))) (Goto bthn) (Goto bels))))))]
                            [(Bool b) (begin
                                        (create-block bthn)
                                        (create-block bels)
                                        (explicate-control-e thn bthn control)
                                        (explicate-control-e els bels control)
                                        (hash-set! all-blocks block
                                                   (append
                                                    (hash-ref all-blocks block)
                                                    (list (IfStmt (Prim 'eq? (list cnd (Bool #t))) (Goto bthn) (Goto bels))))))]
                            [(Prim op es) (begin
                                            (create-block bthn)
                                            (create-block bels)
                                            (explicate-control-e thn bthn control)
                                            (explicate-control-e els bels control)
                                            (hash-set! all-blocks block
                                                       (append
                                                        (hash-ref all-blocks block)
                                                        (list (match cnd
                                                                [(Prim 'not es) (IfStmt (Prim 'eq? (list (car es) (Bool #f))) (Goto bthn) (Goto bels))]
                                                                [_ (IfStmt cnd (Goto bthn) (Goto bels))])))))]

                            [(If cnd1 thn1 els1) (begin
                                                   (create-block bthn)
                                                   (create-block bels)
                                                   (explicate-control-e thn bthn control)
                                                   (explicate-control-e els bels control)
                                                   (explicate-control-e cnd block (list bthn bels)))]

                             
                            )
                          )]
      [_ (cond
           [(eq? control '()) (hash-set! all-blocks block
                                         (append (hash-ref all-blocks block)
                                                 (list (Return e))))]
           [else (hash-set! all-blocks block
                            (append (hash-ref all-blocks block)
                                    (list
                                     (match e
                                       [(Var x) (IfStmt (Prim 'eq? (list e (Bool #t))) (Goto (car control)) (Goto (cadr control)))]
                                       [(Prim 'not es) (IfStmt (Prim 'eq? (list (car es) (Bool #f))) (Goto (car control)) (Goto (cadr control)))]
                                       [(Prim op es) (IfStmt e (Goto (car control)) (Goto (cadr control)))]
                                       [(Bool b) (IfStmt (Prim 'eq? (list e (Bool #t))) (Goto (car control)) (Goto (cadr control)))])
                                     )))])]
      ))

  (define (getSeqGo e)
    (cond
      [(equal? 1 (length e)) (car e)]
      [else
       (Seq (car e) (getSeqGo (cdr e)))]))
  
  (match p
    [(Program info body) (CProgram info
                                   (begin
                                     (create-block 'start)
                                     (explicate-control-e body 'start)
                                     (let ([block-keys (hash-keys all-blocks)])
                                       (for ([key block-keys])
                                         (hash-set! all-blocks key (getSeqGo (hash-ref all-blocks key)))))
                                     all-blocks
                                     )
                                   )]
    )
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
    (set! write (for/set ([w write]) (cond
                                       [(set-member? caller-reg w) (Reg w)]
                                       [else w])))
    
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
      [(Callq label n) (get-set (set) caller-reg prev_set)]
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
                             [(Callq label n) (for ([w caller-reg]) (add-edges (Reg w) lafter))]
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
                     (hash-set! colored (Reg r) (car (hash-ref regmap r)))

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
                              (begin
                                (hash-set! info `colors x)
                                (hash-set! info `callee-saved (foldr (lambda (v l) (append (cond
                                                                                             [(and (hash-has-key? regmap v) (set-member? callee-reg (hash-ref regmap v))) (list (hash-ref regmap v))]
                                                                                             [else `()]) l)) `() (hash-values x) ))
                                (X86Program info body)))])
  )

;; assign homes
(define (assign_homes p)

  (define (replace e colors num_callee [updated_instrs (list)] [caller-saved (mutable-set)])
    (match e
      [(Block info instr) (begin (for ([i instr])
                                   (let ([x (replace i colors num_callee updated_instrs caller-saved)])
                                     (begin
                                       (set! caller-saved (cadr x))
                                       (set! updated_instrs (append updated_instrs (car x)))))) updated_instrs)]
      
      [(Instr label lst) (list (list (Instr label
                                            (for/list ([i lst])
                                              (match i
                                                [(Var x) (let ([c (hash-ref colors i)])
                                                           (cond
                                                             [(< c numpos) (let ([y (hash-ref regmap c)])
                                                                             (begin
                                                                               (cond
                                                                                 [(set-member? caller-reg (car y)) (set-add! caller-saved (car y))])
                                                                               (Reg
                                                                                (car y))
                                                                               ))]
                                                             [else (Deref `rbp (* -8 (+ (+ 1 (- c numpos)) num_callee)))]))]
                                                    
                                                [_ i])))) caller-saved)]
      [(Callq label n) (let ([cs-list (set->list caller-saved)])
                         (list (append 
                                (for/list ([r cs-list]) (Instr 'pushq (list (Reg r))))
                                (list (Callq label n))
                                (for/list ([r (reverse cs-list)]) (Instr 'popq (list (Reg r))))
                                ) caller-saved))]

      [(Jmp label) (list (list (Jmp label)) caller-saved)])
    )

  (define (max-element x y) (if (> x y) x y))

  (define (max-list ls)
    (if (null? (cdr ls))
        (car ls)
        (max-element (car ls) (max-list (cdr ls)))))

  (define (max-proper-list col)
    (max-list (for/list ([x (hash-keys col)]) (match x
                                                [(Reg r) -1]
                                                [_ (hash-ref col x)]))))


  (define (align num)
    (* (ceiling (/ num 16) ) 16)
    )
                           
  (match p
    [(X86Program info body) (let ([x (replace (hash-ref body `start) (hash-ref info `colors) (length (hash-ref info `callee-saved)))] [max-val (max-proper-list (hash-ref info `colors))])
                              (begin
                                ;(display-all " max-val " max-val " numpos " numpos " callee saved" (hash-ref info `callee-saved) " len " (length (hash-ref info `callee-saved)))
                                (cond
                                  [(>= max-val numpos) (hash-set! info 'stack-space (- (align (* 8 (+ (+ (- max-val numpos) 1) (length (hash-ref info `callee-saved))))) (* 8 (length (hash-ref info `callee-saved)))))]
                                  [else (hash-set! info 'stack-space (- (align (length (hash-ref info `callee-saved))) (* 8 (length (hash-ref info `callee-saved)))))])
                                (X86Program info (hash `start (Block `() x)))))])
  )

;; patch instructions
(define (patch_instructions p)
  (define (patchify e [varlst '()])
    (match e
      [(Block info instr) (foldl (lambda (i l) (append l (patchify i))) `() instr)]
      [(Instr `movq (list a a)) `()]
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
  (define (get-prelude sspace callee-saved)
    (append
     (list (Instr `pushq (list (Reg `rbp))))
     (list (Instr `movq (list (Reg `rsp) (Reg `rbp))))
     (for/list ([c callee-saved]) (Instr 'pushq (list (Reg c))))
     (list (Instr `subq (list (Imm sspace) (Reg `rsp))))
     (list (Jmp `start))
     ))

  (define (get-conclusion sspace callee-saved)
    (append
     (list (Instr `addq (list (Imm sspace) (Reg `rsp))))
     (for/list ([c callee-saved]) (Instr 'popq (list (Reg c))))
     (list (Instr `popq (list (Reg `rbp))))
     (list (Retq))))

  (match p
    [(X86Program info body) (X86Program info (hash `start (hash-ref body `start)
                                                   `main (Block `() (get-prelude (hash-ref info `stack-space) (hash-ref info `callee-saved)))
                                                   `conclusion (Block `() (get-conclusion (hash-ref info `stack-space) (hash-ref info `callee-saved)))))])
  )
  
;; Define the compiler passes to be used by interp-tests and they grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("shrink", shrink, interp-Lif, type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ;("instruction selection", select_instructions, interp-pseudo-x86-0)
    ;("uncover life", uncover_live, interp-x86-0)
    ;("build interference", build_interference, interp-x86-0)
    ;("allocate registers", allocate_registers, interp-x86-0)
    ;("assign homes", assign_homes, interp-x86-0)
    ;("patch instructions", patch_instructions, interp-x86-0)
    ;("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
    ))
