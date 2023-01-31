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
      [(Jmp label) (list (Jmp label) ht)]))
                           

  (match p
    [(X86Program info body) (let ([x (replace (hash-ref body `start))] [ht (make-hash)])
                              (begin
                                ;(display-all "x " (length (hash-keys (cadr x))))
                                (hash-set! ht 'stack-space (* (ceiling (/ (length (hash-keys (cadr x))) 2)) 16))
                                (X86Program ht (hash `start (Block `() (car x))))))])
  )

;; patch instructions
(define (patch_instructions p)
  (define (patchify e [varlst '()])
    (match e
      ;[(Block info instr) (for/list ([i instr])
      ;                      (patchify i))]
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
                              [_ (list (Instr label lst))])]
                           )]
      [(Jmp label) (list (Jmp label))])) 
    (match p
      [(X86Program info body) (X86Program info (hash 'start (Block '() (patchify (hash-ref body `start)))))])
      ;;[(X86Program info body) (display-all (patchify (hash-ref body `start)))])
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
      ("assign homes", assign_homes, interp-x86-0)
      ("patch instructions", patch_instructions, interp-x86-0)
      ))
  