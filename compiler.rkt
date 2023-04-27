#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lfun.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require "interp-Lfun.rkt")

(require "interp-Cfun.rkt")

(require "interp-Lfun-prime.rkt")

(require "type-check-Lfun.rkt")

(require "type-check-Cfun.rkt")

(require graph)
(provide (all-defined-out))

(define (insert-between v xs)
  (cond ((null? xs) xs)
        ((null? (cdr xs)) xs)
        (else (cons (car xs)
                    (cons v (insert-between v (cdr xs)))))))

(define (display-all . vs)
  (for-each display (insert-between " " vs)))

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

;;shrink
(define (shrink p)
  (match p
    [(Prim `and (list e1 e2)) (If (shrink e1) (shrink e2) (Bool #f))]
    [(Prim `or (list e1 e2)) (If (shrink e1) (Bool #t) (shrink e2))]
    [(Prim op es) (Prim op (for/list ([i es]) (shrink i)))]
    [(If cnd thn els) (If (shrink cnd) (shrink thn) (shrink els))]
    [(Let x exp body) (Let x (shrink exp) (shrink body))]
    [(Begin es body) (Begin (for/list ([e es]) (shrink e)) (shrink body))]
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

(define (uniquify p [ht (make-hash)] [flag 0])
  (match p
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (cond
               [(equal? flag 1) (cond
                                  [(hash-has-key? ht-fun x) (Var (hash-ref ht-fun x))]
                                  [(hash-has-key? ht x) (Var (hash-ref ht x))]
                                  [else (Var x)])]
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
    [(Begin es body) (Begin (for/list ([i es]) (uniquify i ht)) (uniquify body ht))]
    [(HasType exp type) (HasType (uniquify exp ht) type)]
    [(Begin es body) (Begin (for/list ([e es]) (uniquify e ht)) (uniquify body ht))]
    [(Apply fun exps) (Apply (uniquify fun ht 1) (for/list ([e exps]) (uniquify e ht 1)))]
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

(define (uq p)
  ;(display-all (uniquify p))
  (uniquify p)
  )

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
    [(Begin es body) (Begin (for/list ([e es]) (reveal-functions e)) (reveal-functions body))]
    [(Apply (Var fun) exps) (Apply (FunRef fun (length exps)) (for/list ([e exps]) (reveal-functions e)))]
    [(Def name params rty info body) (Def name params rty info (reveal-functions body))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs]) (reveal-functions e)))]
    [_ p]))

;; limit functions
(define (limit-functions p)
  
  (define (get-rest lst)
    (cdr (cdr (cdr (cdr (cdr lst))))))


  (define (convert-exp e ht)
    (match e
      [(Var x) (cond
                 [(hash-has-key? ht x) (hash-ref ht x)]
                 [else (Var x)])]
      [(If cnd thn els) (If (convert-exp cnd ht) (convert-exp thn ht) (convert-exp els ht))]
      [(Let x exp body) (Let x (convert-exp exp ht) (convert-exp body ht))]
      [(HasType exp type) (HasType (convert-exp exp ht) type)]
      [(Prim op es) (Prim op (for/list ([e es]) (convert-exp e ht)))]
      [(Apply fun exps) (Apply (convert-exp fun ht) (for/list ([e exps]) (convert-exp e ht)))]
      [_ e]))

  (define (get-convert-dict params [ht (make-hash)] )
    (let ([cnt 0])
      (begin
        (for ([p params])
          (begin
            (cond
              [(>= cnt 5) (hash-set! ht (first p) (Prim `vector-ref (list (Var `tup) (Int (- cnt 5)))))])
            (set! cnt (+ cnt 1))))
        ht)))
  
  (match p
    [(Let x exp body) (Let x (limit-functions exp) (limit-functions body))]
    [(Prim op es) (Prim op (for/list ([e es]) (limit-functions e)))]
    [(If cnd thn els) (If (limit-functions cnd) (limit-functions thn) (limit-functions els))]
    [(Begin es body) (Begin (for/list ([e es]) (limit-functions e)) (limit-functions body))]
    [(HasType exp type) (HasType (limit-functions exp) type)]
    [(Apply fun exps) (Apply (limit-functions fun) (cond
                                                     [(<= (length exps) 6) exps]
                                                     [else
                                                      (append (take exps 5) (list (Prim `vector (get-rest exps))))]))]
    [(Def name params rty info body)
     (let ([nparams (cond
                      [(<= (length params) 6) params]
                      [else
                       (append (take params 5) (list (append `(tup : ) (list (append `(Vector) (map third (get-rest params)))))))])])
       (let ([cdict (get-convert-dict params)])
         (let ([nbody (convert-exp body cdict)])
           (Def name nparams rty info (limit-functions nbody)))))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (limit-functions def)))]
    [_ p]
    ))

;; expose-allocation

(define (expose-allocation p)
  (match p
    [(If cnd thn els) (If (expose-allocation cnd) (expose-allocation thn) (expose-allocation els))]
    [(Let x exp body) (Let x (expose-allocation exp) (expose-allocation body))]
    [(Begin es body) (Begin (for/list ([e es]) (expose-allocation e)) (expose-allocation body))]
    [(Prim op es) (Prim op (for/list ([e es]) (expose-allocation e)))]
    [(HasType exp type) (let ([exps (Prim-arg* exp)])
                          (let ([nexps (for/list ([e exps]) (expose-allocation e))] [n (length exps)])
                            (let ([asize (* 8 (+ 1 n))])
                              (let ([arg1 (Prim `+ (list (GlobalValue `free_ptr) (Int asize)))] [arg2 (GlobalValue `fromspace_end)])
                                (let ([if_cond (If (Prim `< (list arg1 arg2)) (Void) (Collect (Int asize)))] [vec-sym (gensym `v)] [allocate (Allocate n type)])
                                  (let ([cnt 0])
                                    (let ([initialize_eles
                                           (begin
                                             (for/list ([an_exp nexps])
                                               (define ele (Prim 'vector-set! (list (Var vec-sym) (Int cnt) an_exp)))
                                               (set! cnt (+ 1 cnt))
                                               ele))])
                                      (let ([vector-declaration (Let vec-sym allocate (Begin initialize_eles (Var vec-sym)))])
                                        (Begin (list if_cond) vector-declaration)))))))))]
                                                             
                            
    [(Apply fun exps) (Apply (expose-allocation fun) (for/list ([e exps]) (expose-allocation e)))]
    [(Def name params rty info body) (Def name params rty info (expose-allocation body))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (expose-allocation def)))]
    [_ p]
    ))

;; remove-complex-opera
(define (is-atomic? a)
  (match a
    [(Var x) #t]
    [(Int n) #t]
    [(Bool b) #t]
    [(Void) #t]
    [_ #f]))

(define (rco-atom e)
  (match e
    [(? is-atomic?) (cons e `())]
    [(Let x exp body) (let ([ng (gensym `g)])
                        (cons (Var ng) (append (list (cons x (remove-complex-opera exp))) (list (cons ng (remove-complex-opera body))))))]
    [(If cnd thn els) (let ([ng (gensym `g)])
                        (cons (Var ng) (list (cons ng (If (remove-complex-opera cnd) (remove-complex-opera thn) (remove-complex-opera els))))))]
    [(Allocate n type) (let ([ng (gensym `g)]) (cons (Var ng) (list (cons ng (Allocate n type)))))]
    [(GlobalValue n) (let ([ng (gensym `g)]) (cons (Var ng) (list (cons ng (GlobalValue n)))))]
    [(Begin es body) (let ([ng (gensym `g)]) (cons (Var ng) (list (cons ng (Begin
                                                                            (for/list ([e es]) (remove-complex-opera e))
                                                                            (remove-complex-opera body))))))]
    [(FunRef fn es) (let ([ng (gensym `g)]) (cons (Var ng) (list (cons ng (FunRef fn es)))))]
    [(Apply fn es) (let ([ng (gensym `g)])
                     (let ([exps (for/list ([e es]) (rco-atom e))] [fexp (rco-atom fn)])
                       (cons (Var ng) (append (foldr append `() (append (for/list ([e exps]) (cdr e)) (list (cdr fexp))))
                                              (list (cons ng (Apply (car fexp) (for/list ([e exps]) (car e)))))))))]
    [(Prim op es) (let ([ng (gensym `g)])
                    (let ([exps (for/list ([e es]) (rco-atom e))])
                      (cons (Var ng) (append (foldr append `() (for/list ([e exps]) (cdr e)))
                                             (list (cons ng (Prim op (for/list ([e exps]) (car e)))))))))]
    ))

(define (gen-lets lst)
  (cond
    [(= 1 (length lst)) (cdar lst)]
    [else (Let (caar lst) (cdar lst) (gen-lets (rest lst)))]))

(define (remove-complex-opera p)
  (match p
    [(? is-atomic?) p]
    [(Let x exp body) (Let x (remove-complex-opera exp) (remove-complex-opera body))]
    [(If cnd thn els) (If (remove-complex-opera cnd) (remove-complex-opera thn) (remove-complex-opera els))]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([def defs]) (remove-complex-opera def) ))]
    [(Begin es body) (Begin (for/list ([e es]) (remove-complex-opera e)) (remove-complex-opera body))]
    [(Def name params rty info body) (Def name params rty info (remove-complex-opera body))]
    [(Prim op es) (gen-lets (cdr (rco-atom (Prim op es))))]
    [(Apply fun exps) (gen-lets (cdr (rco-atom (Apply fun exps))))]
    [_ p]
    ))

;; explicate control
(define (explicate-control p)

  (define all-blocks (make-hash))

  (define (create-block b)
    (cond
      [(hash-has-key? all-blocks b)]
      [else (hash-set! all-blocks b null)]
      ))

  (define (add_to blk instr)
    ;(display-all instr)
    (begin
      (hash-set! all-blocks blk (append (hash-ref all-blocks blk) (list instr)))
      instr)
    )
    
  (define (explicate-control-e e blk)
    (match e
      [(Int n) (add_to blk (Return e))]
      [(Var x) (add_to blk (Return e))]
      [(Bool b) (add_to blk (Return e))]
      [(Prim op es) (add_to blk (Return e))]
      [(Let x exp body)
       (begin
         (explicate-control-f exp x null blk)
         (explicate-control-e body blk))]
      [(If cnd thn els) (let ([bthn (gensym 'block)] [bels (gensym 'block)])
                          (begin
                            (create-block bthn)
                            (create-block bels)
                            (explicate-control-e thn bthn)
                            (explicate-control-e els bels)
                            (explicate-control-g cnd null null blk bthn bels)
                            ))]
      [(Apply fun exps) (add_to blk (TailCall fun exps))]
      [_ (add_to blk (Return e))]))
  
  (define (explicate-control-f e x body blk)
    (match e
      [(Apply fun exps) (add_to blk (Assign (Var x) (Call fun exps)))]
      [(If cnd thn els) (let ([bthn (gensym 'block)] [bels (gensym 'block)])
                          (begin
                            (create-block bthn)
                            (create-block bels)
                            (explicate-control-f thn x body bthn)
                            (explicate-control-f els x body bels)
                            (explicate-control-g cnd null null blk bthn bels)
                            ))]
      [_ (cond
           [(null? x) e]
           [(null? body) (add_to blk (Assign (Var x) e))]
           [else (add_to blk (Assign (Var x) e))])]))

  (define (explicate-control-g cnd thn els blk blkthn blkels)
    (match cnd
      [(Bool #t) (add_to blk (IfStmt (Prim 'eq? (list cnd cnd)) (Goto blkthn) (Goto blkels)))]
      [(Bool #f) (add_to blk (IfStmt (Prim 'eq? (list cnd cnd)) (Goto blkthn) (Goto blkels)))]
      [(Prim 'not e1) (add_to blk (IfStmt (Prim 'eq? (list cnd (Bool #f))) (Goto blkthn) (Goto blkels)))]
      [(Var x) (add_to blk (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (Goto blkthn) (Goto blkels)))]
      [(Let x exp body) 
       (let ([rbody (explicate-control-g body null null blk blkthn blkels)])
         (let ([rexp (explicate-control-f exp x rbody blk)]) rexp))] 
      [(If cnd1 thn1 els1)
       (let ([bthn1 (gensym 'block)]
             [bels1 (gensym 'block)])
         (begin
           (create-block bthn1)
           (create-block bels1)
           (explicate-control-g thn1 null null bthn1 blkthn blkels)
           (explicate-control-g els1 null null bels1 blkthn blkels)
           (explicate-control-g cnd1 null null blk bthn1 bels1) 
           ))]
      [(Apply fun exps) (add_to blk (IfStmt (Call fun exps) (Goto blkthn) (Goto blkels)))]
      [_ (add_to blk (IfStmt cnd (Goto blkthn) (Goto blkels)))])
    )

  (define (getSeqGo e)
    (cond
      [(equal? 1 (length e)) (car e)]
      [else
       (Seq (car e) (getSeqGo (cdr e)))]))
  
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs])
                                                 (match e
                                                   [(Def name params rty info1 body)
                                                    (begin
                                                      (set! all-blocks (make-hash))
                                                      (create-block (string->symbol
                                                                     (string-append
                                                                      (symbol->string name) (symbol->string 'start))))
                                                      (explicate-control-e body (string->symbol
                                                                                 (string-append
                                                                                  (symbol->string name) (symbol->string 'start))))
                                                      (let ([block-keys (hash-keys all-blocks)])
                                                        (for ([key block-keys])
                                                          (hash-set! all-blocks key (getSeqGo (hash-ref all-blocks key)))))
                                                      ;(display-all all-blocks)
                                                      (Def name params rty info1 all-blocks))])))]
    [(Program info body) (CProgram info
                                   (begin
                                     (create-block 'start)
                                     (explicate-control-e body 'start)
                                     (let ([block-keys (hash-keys all-blocks)])
                                       (for ([key block-keys])
                                         (hash-set! all-blocks key (getSeqGo (hash-ref all-blocks key)))))
                                     all-blocks))]
    ))

;; select-instructions
(define (select_instructions p)
  (define (convert e)
    ;(display-all "e " e)
    (match e
      [(Int n) (Imm n)]
      [(Var r) (Var r)]
      [(Bool b) (match b
                  ['#t (Imm 1)]
                  ['#f (Imm 0)])]
      [(GlobalValue x) (Global x)]
      [(Seq exp tail) (append (convert exp) (convert tail))]
      [(Prim `read lst) (list (Callq `read_int 0))]
      [(Prim 'eq? es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (Instr 'sete (list (Reg `rax))))]
      [(Prim '> es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (Instr 'setg (list (Reg `rax))))]
      [(Prim '< es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (Instr 'setl (list (Reg `rax))))]
      [(Prim '<= es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (Instr 'setle (list (Reg `rax))))]
      [(Prim '>= es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (Instr 'setge (list (Reg `rax))))]
      [(Prim op es) (append 
                     (list (Instr `movq (list (convert (car es)) (Reg `rax))))
                     (cond
                       [(and (equal? `- op)(equal? (length es) 1)) (list (Instr `negq (list (Reg `rax))))]
                       [(and (equal? `not op)(equal? (length es) 1)) (list (Instr `xor (list (Imm 1) (Reg `rax))))]
                       [else `()]
                       )
                     (for/list ([i (cdr es)])
                       (cond
                         [(equal? '+ op) (Instr `addq (list (convert i) (Reg `rax)))]
                         [(equal? '- op) (Instr `subq (list (convert i) (Reg `rax)))])))]
      [(Assign x (FunRef label n)) (list (Instr 'leaq (list (Global label) x)))]
      [(Assign x (Call fun args)) (begin
                                    ;(display-all "here")
                                    (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
                                    (define instrs_mov_args
                                      (for/list ([arg args] [reg regs])
                                        (Instr 'movq (list (convert arg) reg))))
                                    (define call_instr (list (IndirectCallq fun (length args))))
                                    (define res_move (list (Instr 'movq (list (Reg 'rax) x))))
                                    (append instrs_mov_args call_instr res_move))]
      [(Assign x val) (cond [(is-atomic? val) (list (Instr `movq (list (convert val) (convert x))))]
                            [else (append (convert val) (list (Instr `movq (list (Reg `rax) x))))])]
      [(IfStmt cnd (Goto bthn) (Goto bels)) (match cnd
                                              [(Prim 'eq? es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (JmpIf 'e bthn) (Jmp bels)) ]
                                              [(Prim '> es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (JmpIf 'g bthn) (Jmp bels))]
                                              [(Prim '< es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (JmpIf 'l bthn) (Jmp bels))]
                                              [(Prim '>= es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (JmpIf 'ge bthn) (Jmp bels))]
                                              [(Prim '<= es) (list (Instr `cmpq (list (convert (car es)) (convert (cadr es)))) (JmpIf 'le bthn) (Jmp bels))]
                                              )]
      [(Call fun args) (begin
                         (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
                         (define instrs_mov_args
                           (for/list ([arg args] [reg regs])
                             (Instr 'movq (list (convert arg) reg))))
                         (define call_instr (list (IndirectCallq fun (length args))))
                         (append instrs_mov_args call_instr))]
      [(TailCall fun args) (begin
                             (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
                             (define instrs_mov_args
                               (for/list ([arg args] [reg regs])
                                 (Instr 'movq (list (convert arg) reg))))
                             (define call_instr (list (TailJmp fun (length args))))
                             (append instrs_mov_args call_instr))]
      [(Return e) (cond
                    [(is-atomic? e) (list (Instr `movq (list (convert e) (Reg `rax))) (Jmp 'conclusion))]
                    [else
                     (append (convert e) (list (Jmp 'conclusion)))])]))

  (match p
    [(CProgram info all-blocks) (X86Program info
                                            (begin
                                              (display-all "here")
                                              (let ([block-keys (hash-keys all-blocks)])
                                                (for ([key block-keys])
                                                  (hash-set! all-blocks key (Block '() (convert (hash-ref all-blocks key))))
                                                  ))
                                              all-blocks)
                                            )]
    [(ProgramDefs info defs) (ProgramDefs info (for/list ([e defs])
                                                 (match e
                                                   [(Def name params rty info1 all-blocks)
                                                    (begin
                                                      (let ([block-keys (hash-keys all-blocks)])
                                                        (for ([key block-keys])
                                                          (hash-set! all-blocks key (Block '() (convert (hash-ref all-blocks key))))
                                                          ))
                                                      (Def name params rty info1 all-blocks)
                                                      )]
                                                   )))]
    )
  )

(define (uncover_live p)

  (define block-graph (make-multigraph `()))
  
  (define (get-graph all-blocks)
    ;(display-all "get-graph")
    (define (recurse node-label)
      (match (hash-ref all-blocks node-label)
        [(Block info body) (begin
                             ( for ([instr body]) (match instr
                                                    [(Jmp label) (begin
                                                                   (add-vertex! block-graph node-label)
                                                                   (add-vertex! block-graph label)
                                                                   (add-directed-edge! block-graph node-label label))]
                                                    [(TailJmp x y) (begin
                                                                     (add-vertex! block-graph node-label)
                                                                     (add-vertex! block-graph 'conclusion)
                                                                     (add-directed-edge! block-graph node-label 'conclusion))]
                                                    [(JmpIf cc label) (begin
                                                                        (add-vertex! block-graph node-label)
                                                                        (add-vertex! block-graph label)
                                                                        (add-directed-edge! block-graph node-label label))]
                                                    [_ `()]
                                                    ))

                             )]))
    
    (for ([key (hash-keys all-blocks)]) (recurse key))
    )

  (define lbefore-set (make-hash))
  (define lafter-set (make-hash))
  (define lall-set (make-hash))

  (define (get-set read write prev_set)
    ;(display-all "get-set")
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
    ;(display-all "calc")
    (match instr
      [(Instr 'movq lst) (get-set (set (car lst)) (set (cadr lst)) prev_set)]
      [(Instr 'addq lst) (get-set (set (car lst) (cadr lst)) (set (cadr lst)) prev_set)]
      [(Instr 'subq lst) (get-set (set (car lst) (cadr lst)) (set (cadr lst)) prev_set)]
      [(Instr 'negq lst) (get-set (set (car lst)) (set (car lst)) prev_set)]
      [(Instr 'cmpq lst) (get-set (set (car lst) (cadr lst)) `() prev_set)]
      [(Instr 'xorq lst) (get-set (set (cadr lst) (cadr lst)) `() prev_set)]
      [(Instr 'leaq lst) (get-set (set '()) (set (cadr lst)) prev_set)]
      [(JmpIf cc label) prev_set]
      [(Jmp label) prev_set]
      [(Callq x y) (get-set
                    (set (take (map Reg '(rdi rsi rdx rcx r8 r9)) y))
                    (set (map Reg '(rcx rdx rsi rdi r8 r9 r10 r11)))
                    prev_set)]
      [(IndirectCallq x y) (let ([read_set (set (take (map Reg '(rdi rsi rdx rcx r8 r9)) y))])
                             (begin
                               (set-add read_set x)
                               (get-set read_set (set (map Reg '(rcx rdx rsi rdi r8 r9 r10 r11))) prev_set)))]
      [(TailJmp x y) (let ([read_set (set (take (map Reg '(rdi rsi rdx rcx r8 r9)) y))])
                       (begin
                         (set-add read_set x)
                         (set-add read_set (Reg 'rax))
                         (set-add read_set (Reg 'rsp))
                         (get-set read_set (set (map Reg '(rcx rdx rsi rdi r8 r9 r10 r11))) (set (Reg `rax) (Reg `rsp)))))]
      [_ prev_set]
      ))

  (define (aux node-label b lbefore r-graph)
    ;(display-all "aux")
    (define gset lbefore)
    (match b
      [(Block info body) (begin
                           (hash-set! lall-set node-label (reverse
                                                           (for/list ([instr (reverse body)])
                                                             (let ([lafter (calc instr gset)])
                                                               (begin
                                                                 (set! gset lafter)
                                                                 lafter)))))

                           (for ([node (get-neighbors r-graph node-label)])
                             (hash-set! lbefore-set node (set-union (hash-ref lbefore-set node) gset)))
                           (hash-set! lafter-set node-label gset))]
      [_ (for ([node (get-neighbors r-graph node-label)])
           (hash-set! lbefore-set node
                      (set-union (hash-ref lbefore-set node) lbefore)))]
      )
    )

  (define ht (make-hash))
  (match p
    [(X86Program info body) (begin
                              (get-graph body)
                              (for ([node (get-vertices block-graph)]) (begin
                                                                         (hash-set! lafter-set node (set))
                                                                         (hash-set! lbefore-set node (set))))

                              (let ([r-graph (transpose block-graph)] [temp-body body])
                                (begin
                                  (hash-set! temp-body `conclusion `())
                                  (hash-set! lbefore-set `conclusion (set (Reg `rax) (Reg `rsp)))
                                  (hash-set! lafter-set `conclusion (set (Reg `rax) (Reg `rsp)))
                                  (for ([node-label (tsort r-graph)])
                                    (aux node-label (hash-ref temp-body node-label) (hash-ref lbefore-set node-label) r-graph))))
                              (hash-set! ht `live lall-set)
                              (hash-remove! body `conclusion)
                              (X86Program ht body)
                              )]
    
    [(ProgramDefs info defs) (ProgramDefs info
                                          (for/list ([b defs])
                                            (set! block-graph (make-multigraph `()))
                                            (set! lbefore-set (make-hash))
                                            (set! lafter-set (make-hash))
                                            (set! lall-set (make-hash))
                                            (set! ht (make-hash))
                                            (match b
                                              [(Def name params rty info1 body)
                                               (begin
                                                 (get-graph body)
                                                 (for ([node (get-vertices block-graph)])
                                                   (begin
                                                     (hash-set! lafter-set node (set))
                                                     (hash-set! lbefore-set node (set))))
                                                 (let ([r-graph (transpose block-graph)] [temp-body body])
                                                   (begin
                                                     (hash-set! temp-body `conclusion `())
                                                     (hash-set! lbefore-set `conclusion (set (Reg `rax) (Reg `rsp)))
                                                     (hash-set! lafter-set `conclusion (set (Reg `rax) (Reg `rsp)))
                                                     (for ([node-label (tsort r-graph)])
                                                       (aux node-label (hash-ref temp-body node-label) (hash-ref lbefore-set node-label) r-graph))))
                                                 (hash-set! ht `live lall-set)
                                                 (hash-remove! body `conclusion)
                                                 (Def name params rty ht body))]
                                              )))]
    )

  )

(define (build_interference p)
  
  (define g (undirected-graph '()))

  (define (add-edges write lafter)
    (for ([l (set-subtract lafter (set write))]) (add-edge! g write l))
    )
  
  (define (aux b l)
    ;(display-all b)
    (match b
      [(Block info body) (for ([instr body] [lafter l])
                           ;;(begin
                           ;;(display-all "Edges " (get-edges g) "Instr " instr)
                           (match instr
                             [(Instr `movq (list (Imm x) n)) (add-edges n lafter)]
                             [(Instr `movq (list m n)) (add-edges m (set-subtract lafter (set n)))]
                             [(Instr `movzbq (list m n)) (add-edges m (set-subtract lafter (set n)))]
                             [(Instr `cmpq (list m n)) `()]
                             [(Instr 'sete r) '()]
                             [(Instr 'setg r) '()]
                             [(Instr 'setge r) '()]
                             [(Instr 'setl r) '()]
                             [(Instr 'setle r) '()]
                             [(Instr label lst) (add-edges (last lst) lafter)]
                             [(Jmp 'conclusion) (add-edge! g (Reg 'rax) (Reg 'rsp))]
                             [(TailJmp fun args) (begin (add-edge! g (Reg 'rax) (Reg 'rsp)) (for ([w caller-reg]) (add-edges (Reg w) lafter)))]
                             [(Callq label n) (for ([w caller-reg]) (add-edges (Reg w) lafter))]
                             [(IndirectCallq label n) (for ([w caller-reg]) (add-edges (Reg w) lafter))]
                             [_ '()]))]))
  
  (match p
    [(X86Program info body) (begin
                              (for ([key (hash-keys body)])
                                (let ([x (aux (hash-ref body key) (hash-ref (hash-ref info `live) key))])
                                  (begin
                                    (hash-set! info 'conflicts g)
                                    (hash-set! info 'edges (get-edges g)))))
                              (X86Program info body))]
    [(ProgramDefs info1 defs) (ProgramDefs info1
                                           (for/list ([b defs])
                                             (set! g (undirected-graph '()))
                                             (match b
                                               [(Def name params rty info body)
                                                (begin
                                                  (for ([key (hash-keys body)])
                                                    (let ([x (aux (hash-ref body key) (hash-ref (hash-ref info `live) key))])
                                                      (begin
                                                        (hash-set! info 'conflicts g)
                                                        (hash-set! info 'edges (get-edges g)))))
                                                  (Def name params rty info body))])))]))

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
                           [(not (hash-has-key? neighbors side)) '()]
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
                     (hash-set! colored (Reg r) (car (hash-ref regmap r)))
                     (for ([side (get-neighbors graph (Reg r))])
                       (cond
                         [(hash-has-key? colored side) `()]
                         [(hash-has-key? neighbors side) (hash-set! neighbors side (set-add (hash-ref neighbors side) (hash-ref colored (Reg r))))]
                         [else
                          (hash-set! neighbors side (set (hash-ref colored (Reg r))))]))
                     )]

          [_ `()]))

      ; pqueue initialisation
      ;(display-all (get-vertices graph))

      (for ([node (get-vertices graph)])
        ;(display-all node)
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

                                (X86Program info body)))]
    [(ProgramDefs info1 defs) (ProgramDefs info1
                                           (for/list ([b defs])
                                             (match b
                                               [(Def name params rty info body)
                                                (display-all name)
                                                (let ([x (init (hash-ref info `conflicts))])
                                                  (begin
                                                    (hash-set! info `colors x)
                                                    (hash-set! info `callee-saved (foldr (lambda (v l) (append (cond
                                                                                                                 [(and (hash-has-key? regmap v) (set-member? callee-reg (hash-ref regmap v))) (list (hash-ref regmap v))]
                                                                                                                 [else `()]) l)) `() (hash-values x) ))

                                                    (Def name params rty info body)))
                                                ])))]))

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

      [(IndirectCallq label n) (let ([cs-list (set->list caller-saved)])
                                 (list (append 
                                        (for/list ([r cs-list]) (Instr 'pushq (list (Reg r))))
                                        (list (IndirectCallq label n))
                                        (for/list ([r (reverse cs-list)]) (Instr 'popq (list (Reg r))))
                                        ) caller-saved))]
      
      [(Jmp label) (list (list (Jmp label)) caller-saved)]

      [(TailJmp x y) (list (list (TailJmp x y)) caller-saved)]

      [(JmpIf cc label) (list (list (JmpIf cc label)) caller-saved)]

      )
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

    [(X86Program info body)
     (begin
       (for ([key (hash-keys body)])
         (let ([x (replace (hash-ref body key) (hash-ref info `colors) (length (hash-ref info `callee-saved)))] [max-val (max-proper-list (hash-ref info `colors))])
           (begin
             (cond
               [(>= max-val numpos) (hash-set! info 'stack-space (- (align (* 8 (+ (+ (- max-val numpos) 1) (length (hash-ref info `callee-saved))))) (* 8 (length (hash-ref info `callee-saved)))))]
               [else (hash-set! info 'stack-space (- (align (length (hash-ref info `callee-saved))) (* 8 (length (hash-ref info `callee-saved)))))])

             (hash-set! body key (Block `() x)))))

       (X86Program info body))]

    [(ProgramDefs info1 defs) (ProgramDefs info1
                                           (for/list ([b defs])
                                             (match b
                                               [(Def name params rty info body)
                                                (begin
                                                  (for ([key (hash-keys body)])
                                                    (let ([x (replace (hash-ref body key) (hash-ref info `colors) (length (hash-ref info `callee-saved)))] [max-val (max-proper-list (hash-ref info `colors))])
                                                      (begin
                                                        (cond
                                                          [(>= max-val numpos) (hash-set! info 'stack-space (- (align (* 8 (+ (+ (- max-val numpos) 1) (length (hash-ref info `callee-saved))))) (* 8 (length (hash-ref info `callee-saved)))))]
                                                          [else (hash-set! info 'stack-space (- (align (length (hash-ref info `callee-saved))) (* 8 (length (hash-ref info `callee-saved)))))])

                                                        (hash-set! body key (Block `() x)))))

                                                  (Def name params rty info body))])))]
    )
  )

;; patch instructions

(define (patch_instructions p)

  (define (patchify e [varlst '()])

    (match e
      [(Block info instr) (foldl (lambda (i l) (append l (patchify i))) `() instr)]
      [(Instr `movq (list a a)) `()]
      [(Instr `movzbq (list (Reg r) (Deref reg1 val1))) (list
                                                         (Instr `movzbq (list (Reg r) (Reg `rcx)))
                                                         (Instr `movq (list (Reg `rcx) (Deref reg1 val1))))]
      [(Instr `leaq (list x (Deref reg1 val1))) (list
                                                 (Instr `leaq (list x (Reg `rcx)))
                                                 (Instr `movq (list (Reg `rcx) (Deref reg1 val1))))]
      [(Instr `cmpq (list a (Imm n))) (list
                                       (Instr `movq (list (Imm n) (Reg `rcx)))
                                       (Instr `cmpq (list a (Reg `rcx))))]
      [(Instr `cmpq (list (Deref reg1 val1) (Deref reg2 val2))) (list
                                                                 (Instr `movq (list (Deref reg1 val1) (Reg `rcx)))
                                                                 (Instr `cmpq (list (Reg `rcx) (Deref reg2 val2))))]
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
      [(IndirectCallq label n) (list (IndirectCallq label n))]
      [(JmpIf cc label) (list (JmpIf cc label))]
      [(Jmp label) (list (Jmp label))]
      [(TailJmp x y) (list (TailJmp x y))]
      ))
  
  (match p
    [(X86Program info body) (begin
                              (for ([key (hash-keys body)])
                                (hash-set! body key (Block '() (patchify (hash-ref body key)))))
                              (X86Program info body))]
    [(ProgramDefs info1 defs) (ProgramDefs info1
                                           (for/list ([b defs])
                                             (match b
                                               [(Def name params rty info body)
                                                (begin
                                                  (for ([key (hash-keys body)])
                                                    (hash-set! body key (Block '() (patchify (hash-ref body key)))))
                                                  (Def name params rty info body))]
                                               )))]))

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

    [(X86Program info body) (begin
                              (hash-set! body `main (Block `() (get-prelude (hash-ref info `stack-space) (hash-ref info `callee-saved))))
                              (hash-set! body `conclusion (Block `() (get-conclusion (hash-ref info `stack-space) (hash-ref info `callee-saved))))
                              (X86Program info body))])

  )
    
;; Define the compiler passes to be used by interp-tests and they grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( 
    ;; Uncomment the following passes as you finish them.
    ("shrink", shrink, interp-Lfun, type-check-Lfun)
    ("uniquify" ,uq ,interp-Lfun ,type-check-Lfun)
    ("reveal_functions" ,reveal-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("limit_functions" ,limit-functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose_allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera" ,remove-complex-opera ,interp-Lfun-prime, type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ;("instruction selection", select_instructions, interp-pseudo-x86-0)
    ;("uncover life", uncover_live, interp-x86-0)
    ;("build interference", build_interference, interp-x86-0)
    ;("allocate registers", allocate_registers, interp-x86-0)
    ;("assign homes", assign_homes, interp-x86-0)
    ;("patch instructions", patch_instructions, interp-x86-0)
    ;("prelude and conclusion", prelude-and-conclusion, interp-x86-0)
    ))