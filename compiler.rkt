#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
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
  (define (is-atomic? e)
    (match e
      [(Int n) #t]
      [(Var x) #t]
      [_ #f]))
  
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

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ))
