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

;; uniquify : R1 -> R1

;; 
;; maintain a hash-table for env
;; env - e0
;; Let x exp body
;; Uniquify exp using e0
;; create e1 by adding x->x' to e0; change x->x'
;; uniquify body with environment e1

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

  (define varlst `())

  (define (flatten e)
    (match e
      [(Prim op es) (Prim op (for/list ([i es])
                               (cond
                                 [(is-atomic? i) i]
                                 [else
                                  (append varlst (list (gensym `g) (flatten i)))])))]
      ))

  (define (final-flat e)
    (let ([fexpr (flatten e)])
      (define (final-flat-r lst)
        (cond
          [(null? e) fexpr]
          [else
           (Let (car (car varlst)) (car (cdr (car varlst))) (final-flat-r (cdr varlst)))]))
      (final-flat-r varlst)))

  (match p
    [(Program info body) (Program info (final-flat body))])
)
  

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
    ;; ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ;; ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ))
