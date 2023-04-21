#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp-Lfun.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
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

(define (is-atomic? a)
  (match a
    [(Var x) #t]
    [(Int n) #t]
    [(Bool b) #t]
    [_ #f]))

;;shrink
(define (shrink p)
  (match p
    [(Prim `and (list e1 e2)) (If (shrink e1) (shrink e2) (Bool #f))]
    [(Prim `or (list e1 e2)) (If (shrink e1) (Bool #t) (shrink e2))]
    [(Prim op es) (Prim op (for/list ([i es]) (shrink i)))]
    [(If cnd thn els) (If (shrink cnd) (shrink thn) (shrink els))]
    [(Let x exp body) (Let x (shrink exp) (shrink body))]
    [(ProgramDefsExp info defs exp) (ProgramDefs info
                                                 (append (for/list ([def defs]) (shrink def))
                                                         (list (Def `main `() `Integer `() (shrink exp)))))]
    [(Apply fun exps) (Apply (shrink fun) (for/list ([exp exps]) (shrink exp)))]
    [(Def name params rty info body) (Def name params rty info (shrink body))]
    [(Program info body) (Program info (shrink body))]
    [_ p]))
    
;;uniquify

(define ht-fun (make-hash))
(define ht-fun-len (make-hash))

(define (uniquify p [ht (make-hash)] )
  ;(display-all "p: " p)
  (match p
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (cond
               [(hash-has-key? ht x) (Var (hash-ref ht x))]
               [else (Var x)]
               )]
    [(Let x exp body)
     (let ([exp_new (uniquify exp ht)] [x_new (gensym x)])
       (begin
         (hash-set! ht x x_new)
         (Let x_new exp_new (uniquify body ht))
         ))]
    [(If cnd thn els) (If (uniquify cnd ht) (uniquify thn ht) (uniquify els ht))]
    [(Prim op es) (Prim op (for/list ([i es]) (uniquify i ht)))]
    [(Apply fun exps) (Apply (uniquify fun ht-fun) (for/list ([e exps]) (uniquify e ht)))]
    [(Program info body) (Program info (uniquify body ht))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs]) (uniquify e ht)))]
    [(Def name params rty info body) (let ([name_new (gensym name)]
                                           [params_new (for/list ([param params])
                                                         (begin
                                                           (hash-set! ht (car param) (gensym (car param)))
                                                           (cons (hash-ref ht (car param)) (cdr param))))])
                                       (begin
                                         (hash-set! ht-fun name name_new)
                                         ;(display-all " fun " (list->set (hash-values ht-fun)))
                                         (hash-set! ht-fun-len name_new (length params))
                                         (Def name_new params_new rty info (uniquify body ht))
                                         ))]
    [_ (error "Nothing matches")]))

;(define func_names (list->set(hash-values ht-fun)))

;;reveal-functions
(define (reveal-functions p)
  (define func_names (list->set(hash-values ht-fun)))
  (match p
    [(Var x) (cond
               [(set-member? func_names x) (FunRef x (hash-ref ht-fun-len x))]
               [else (Var x)]
               )]
    [(Let x e body) (Let x (reveal-functions e) (reveal-functions body))]
    [(If cnd thn els) (If (reveal-functions cnd) (reveal-functions thn) (reveal-functions els))]
    [(Prim op es) (Prim op (for/list ([e es]) (reveal-functions e)))]
    [(Apply (Var fun) exps) (Apply (FunRef fun (length exps)) (for/list ([e exps]) (reveal-functions e)))]
    [(Def name params rty info body) (Def name params rty info (reveal-functions body))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs]) (reveal-functions e)))]
    [_ p]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  
  (define (flatten e [varlst '()])

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
      [(Apply fun exps) (list (let ([fn (gensym 'g)])
                                (begin
                                  (set! varlst (append (list (list fn fun)) varlst))
                                  (Apply (Var fn) (for/list ([i exps])
                                                    (cond
                                                      [(is-atomic? i) i]
                                                      [else
                                                       (let ([new_var (gensym 'g)] [ret_lst (flatten i)])
                                                         (begin (set! varlst (append (cadr ret_lst) (list (list new_var (car ret_lst))) varlst ))
                                                                (Var new_var))
                                                         )])))         
                                  )) varlst)]
      [(Def name params rty info body)  (list (let ([fbody (flatten body)])
                                                (begin
                                                  (set! varlst (append (cadr fbody)))
                                                  (Def name params rty info (car fbody)))) varlst)]
      ))

  (define (final-flat e)
    (let ([fexpr (flatten e)])
      (define (final-flat-r lst)
        ;(display-all "fexpr" fexpr)
        (cond
          [(null? lst) (car fexpr)]
          [else     
           (Let (caar lst) (cadr (car lst)) (final-flat-r (cdr lst)))]))
      (final-flat-r (cadr fexpr))))

  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs]) (match e
                                                                      [(Def name params rty info body) (Def name params rty info (final-flat body))])))]
    ;[(Program info body) (Program info (final-flat body))]
    )
  )
    
;; Define the compiler passes to be used by interp-tests and they grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("shrink", shrink, interp-Lfun, type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ("reveal-functions" ,reveal-functions ,interp-Lfun ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun ,type-check-Lfun)
    ;("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
    ;("instruction selection", select_instructions, interp-pseudo-x86-0)
    ;("uncover life", uncover_live, interp-x86-0)
    ;("build interference", build_interference, interp-x86-0)
    ;("allocate registers", allocate_registers, interp-x86-0)
    ;("assign homes", assign_homes, interp-x86-0)
    ;("patch instructions", patch_instructions, interp-x86-0)
    ;("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
    ))