#lang racket
(require racket/set
         racket/stream)

(require racket/dict)
(require racket/fixnum)
(require graph)
(require racket/trace)

(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")

(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")

(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")

(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cwhile.rkt")


(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))

;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shrink pass: Lif -> Lif

(define (shrink p)
  (match p
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (Var x)]
    [(Let var e body) (Let var (shrink e) (shrink body))]
    [(Prim 'and (list exp1 exp2)) (If (shrink exp1) (shrink exp2) (Bool #f))]
    [(Prim 'or (list exp1 exp2)) (If (shrink exp1) (Bool #t) (shrink exp2))]
    [(Prim op es) (Prim op (map shrink es))]
    [(If cond exp1 exp2) (If (shrink cond) (shrink exp1) (shrink exp2))]
    [(Program info e) (Program info (shrink e))]
    [else
     error
     ("Invalid match at shrink.")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uniquify pass (updated till Lif)


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Var x) (Var (hash-ref env x))]
      [(Let var e body) (let* ([new_var (gensym var)]
                               [e ((uniquify-exp env) e)]
                               [new_env (hash-set env var new_var)]
                               [body ((uniquify-exp new_env) body)])
                          (Let new_var e body))]
      [(Prim op es) (Prim op
                          (for/list ([e es])
                            ((uniquify-exp env) e)))]
      [(If cond exp1 exp2) (let* ([new_cond ((uniquify-exp env) cond)]
                                  [new_exp1 ((uniquify-exp env) exp1)]
                                  [new_exp2 ((uniquify-exp env) exp2)])
                             (If new_cond new_exp1 new_exp2))]
      [else
       error
       ("Invalid match at uniquify-exp.")])))

;; uniquify : Lif -> Lif
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp (hash)) e))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; remove complex opera* pass (updated till Lif)

;; Returns: (atom, (list (cons variables expression))).
(define (rco-atom e)
  (match e
    [(Int x) (cons (Int x) (list))]
    [(Bool b) (cons (Bool b) (list))]
    [(Var var) (cons (Var var) (list))]
    [(Prim op es) (let* ([new_sym (gensym 'new)]
                         [new_var (Var new_sym)]
                         [pairs (map rco-atom es)]
                         [atoms (map car pairs)]
                         [lists (map cdr pairs)]
                         [combined_lists (foldr append (list) lists)]
                         [combined_lists (append combined_lists
                                                 (list (cons new_sym (Prim op atoms))))])
                    (cons new_var combined_lists))]
    [(Let x e body) (let* ([new_sym (gensym 'new)]
                           [new_var (Var new_sym)]
                           [list_e (cons x (rco-exp e))]
                           [list_body (cons new_sym (rco-exp body))]
                           [list_combined (append (list list_e) (list list_body))])
                      (cons new_var list_combined))]
    [(If cond exp1 exp2)
     (let* ([new_sym (gensym 'new)]
            [new_var (Var new_sym)]
            [list_e (cons new_sym (If (rco-exp cond) (rco-exp exp1) (rco-exp exp2)))])
       (cons new_var (list list_e)))]
    [else
     error
     ("Invalid match in rco-atom.")]))

;; Returns: (list (exp))
(define (generate-lets lst)
  (match lst
    [(list (cons x y)) y]
    [(cons (cons x y) z) (Let x y (generate-lets z))]
    [else
     error
     ("Invalid match in generate-lets.")]))

;; Returns: (expression)
(define (rco-exp e)
  (match e
    [(Int x) (Int x)]
    [(Bool b) (Bool b)]
    [(Var var) (Var var)]
    [(Prim 'read (list)) (Prim 'read (list))]
    [(Prim op es) (generate-lets (cdr (rco-atom (Prim op es))))]
    [(Let var e body) (Let var (rco-exp e) (rco-exp body))]
    [(If cond exp1 exp2) (If (rco-exp cond) (rco-exp exp1) (rco-exp exp2))]
    [else
     error
     ("Invalid match in rco-exp.")]))

;; remove-complex-opera* : Lif -> Lif
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Explicate control pass (updated till Lif)

(define CFG (make-hash))

(define (add-to-cfg block)
  (match block
    [(Goto label) (Goto label)]
    [else (let* ([label (gensym 'label)] [_ (hash-set! CFG label block)]) (Goto label))]))

(define (explicate-pred pred exp1 exp2)
  (match pred
    [(Bool #t) exp1]
    [(Bool #f) exp2]
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(Let var e body) (explicate-assign e var (explicate-pred body exp1 exp2))]
    [(Prim cmp (list x y)) (IfStmt (Prim cmp (list x y)) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(Prim 'not (list x)) (IfStmt (Prim 'eq? (list x (Bool #f))) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(If cond a b) (let* ([x (add-to-cfg exp1)] [y (add-to-cfg exp2)])
                     (explicate-pred cond (explicate-pred a x y) (explicate-pred b x y)))]
    [else (error "explicate-pred unhandled case" pred)]))

;; Returns: (expression)
(define (explicate-tail e)
  (match e
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Var var) (Return (Var var))]
    [(Let x assign_val return_val) (let* ([tail (explicate-tail return_val)])
                                     (explicate-assign assign_val x tail))]
    [(Prim op es) (Return (Prim op es))]
    [(If cond exp1 exp2) (explicate-pred cond (explicate-tail exp1) (explicate-tail exp2))]
    [else (error "Invalid match in explicate-tail.")]))

;; Returns: (Sequence)
(define (explicate-assign e x tail)
  (match e
    [(Int n) (Seq (Assign (Var x) (Int n)) tail)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) tail)]
    [(Var y) (Seq (Assign (Var x) (Var y)) tail)]
    [(Let y assign_val return_val) (let* ([tail (explicate-assign return_val x tail)])
                                     (explicate-assign assign_val y tail))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) tail)]
    [(If cond exp1 exp2) (let* ([new_tail (add-to-cfg tail)]
                                [tail1 (explicate-assign exp1 x new_tail)]
                                [tail2 (explicate-assign exp2 x new_tail)])
                           (explicate-pred cond tail1 tail2))]
    [else (error "Invalid match in explicate-assign.")]))

;; explicate-control : Lif -> C1
(define (explicate-control p)
  (set! CFG (make-hash))
  (match p
    [(Program info body) (let* ([_ (dict-set! CFG 'start (explicate-tail body))])
                           (CProgram info CFG))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Select instructions pass
;; Returns: (x86 expression)
;; Remeber, that arguments are flipped in cmpq
(define (select-instructions-exp p)
  (match p
    ;; Comparators
    ['> 'g]
    ['< 'l]
    ['>= 'ge]
    ['<= 'le]
    ['eq? 'e]
    ;; Atoms
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Int x) (Imm x)]
    [(Var x) (Var x)]
    ;; Block
    [(cons label cmds) (cons label (Block '() (select-instructions-exp cmds)))]
    ;; Sequence
    [(Seq x y) (append (select-instructions-exp x) (select-instructions-exp y))]
    ;; Assign(s)
    [(Assign x (Prim 'read '())) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
    [(Assign x (Prim '+ (list exp1 exp2)))
     (list (Instr 'movq (list (select-instructions-exp exp1) x))
           (Instr 'addq (list (select-instructions-exp exp2) x)))]
    [(Assign x (Prim '- (list exp1)))
     (list (Instr 'movq (list (select-instructions-exp exp1) x)) (Instr 'negq (list x)))]
    [(Assign x (Prim '- (list exp1 exp2)))
     (list (Instr 'movq (list (select-instructions-exp exp1) x))
           (Instr 'subq (list (select-instructions-exp exp2) x)))]
    [(Assign x (Prim 'not (list exp1)))
     (list (Instr 'movq (list (select-instructions-exp exp1) x)) (Instr 'xorq (list (Imm 1) x)))]
    [(Assign x (Prim cmp (list exp1 exp2)))
     (list (Instr 'cmpq (list (select-instructions-exp exp2) (select-instructions-exp exp1)))
           (Instr 'set (list (select-instructions-exp cmp) (Reg 'al)))
           (Instr 'movzbq (list (Reg 'al) x)))]
    [(Assign x y) (list (Instr 'movq (list (select-instructions-exp y) x)))]
    ;; If statement
    [(IfStmt (Prim cmp (list exp1 exp2)) (Goto label1) (Goto label2))
     (list (Instr 'cmpq (list (select-instructions-exp exp2) (select-instructions-exp exp1)))
           (JmpIf (select-instructions-exp cmp) label1)
           (Jmp label2))]
    ;; Goto
    [(Goto label) (list (Jmp label))]
    ;; Return
    [(Return exp) (append (select-instructions-exp (Assign (Reg 'rax) exp))
                          (list (Jmp 'conclusion)))]))

;; select-instructions : C1 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info CFG) (X86Program info (map select-instructions-exp (hash->list CFG)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assign homes is no longer required, hence has been removed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Patch instructions pass.

(define (fix-instr instr)
  (match instr
    [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
     (list (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
           (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
    [(Instr 'movq (list arg arg)) (list)]
    [(Instr 'movzbq (list arg1 (Deref reg1 off1)))
     (list (Instr 'movq (list (Deref reg1 off1) (Reg 'rax))) (Instr 'movzbq (list arg1 (Reg 'rax))))]
    [(Instr 'cmpq (list arg1 (Imm x))) (list (Instr 'movq (list (Imm x) (Reg 'rax)))
                                             (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [else (list instr)]))

(define (fix-instrs instr_list)
  (foldr append (list) (map fix-instr instr_list)))

(define (patch-blk blk)
  (match blk
    [(cons label (Block info instr_list)) (cons label (Block info (fix-instrs instr_list)))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks) (X86Program info (map patch-blk blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prelude-and-conclusion : x86 -> x86
;; The stackspace must be aligned to avoid callq problems.
(define (align-stack-space num_vars)
  (let* ([stackspace (* 1 num_vars)] [stackspace (align stackspace 16)]) stackspace))

(define (get-stack-space info)
  (let* ([local_types (length (dict-keys (dict-ref info 'locals-types)))]
         [local_var_size (* 1 (dict-ref info 'num_spilled))]
         [callee-size (* 8 (length (dict-ref info 'used_callee)))]
         #| [_ (print (local_types local_var_size callee-size))] |#
         [stacksize (+ (* 8 local_types) (+ (* 1 callee-size) (* 8 local_var_size)))]
         #| [_ (print stacksize)] |#
         [stacksize (* 1 stacksize)]
         [stacksize (align-stack-space stacksize)]
         [stacksize (- stacksize callee-size)])
    stacksize))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (X86Program
      info
      (let* ([callee-saved (dict-ref info 'used_callee)]
             [stacksize (get-stack-space info)]
             [instr-callee-push (for/list ([reg callee-saved])
                                  (Instr 'pushq (list reg)))]
             [instr-callee-pop (for/list ([reg callee-saved])
                                 (Instr 'popq (list reg)))]
             [main_block (Block empty
                                (flatten (list (Instr 'pushq (list (Reg 'rbp)))
                                               (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                               instr-callee-push
                                               (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))
                                               (Jmp 'start))))]
             [conclusion_block (Block empty
                                      (flatten (list (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))
                                                     instr-callee-pop
                                                     (Instr 'popq (list (Reg 'rbp)))
                                                     (Retq))))]
             [blocks (dict-set* blocks 'main main_block 'conclusion conclusion_block)])
        blocks))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; uncover_live pass

(define label->live (make-hash))
(define caller-saved '(rax rcx rdx rsi rdi r8 r9 r10 r11))
(define callee-saved '(rdi rsi rdx rcx r8 r9))
(define remaining-reg '(rbx r12 r13 r14 r15))
(define offset 8)

(define (filter-var-reg-list lst)
  (filter (lambda (x) (or (Var? x) (Reg? x))) lst))

(define (filter-var-reg lst)
  (list->set (filter-var-reg-list lst)))

(define (instr-location-read instr)
  (let* ([live_list (match instr
                      [(Instr 'movq (list arg1 arg2)) (list arg1)]
                      [(Instr 'movzbq (list arg1 arg2)) (list arg1)]
                      [(Instr 'set (list cc arg)) (list)]
                      [(Instr op args) args]
                      [(Callq x y) (map Reg (take callee-saved y))]
                      [(JmpIf cc label) (list)]
                      [(Jmp label) (list)]
                      [else (error "Invalid instruction at instr-location-read." instr)])])
    (filter-var-reg live_list)))

(define (instr-location-written instr)
  (let* ([live_list (match instr
                      [(Instr 'cmpq es) empty]
                      [(Instr 'set (list cc arg)) (list (Reg 'rax))]
                      [(Instr op es) (list (last es))]
                      [(Callq x y) (map Reg caller-saved)]
                      [(Jmp label) (list)]
                      [(JmpIf cc label) (list)]
                      [else (error "Invalid instruction at instr-location-written." instr)])])
    (filter-var-reg live_list)))

(define (uncover-live-instrs instrs prev_liveness)
  (match instrs
    [(list) (list)]
    [(cons instr rest_instrs)
     (let* ([locations_written (instr-location-written instr)]
            [locations_read (instr-location-read instr)]
            [prev_liveness (match instr
                             [(Jmp label) (dict-ref label->live label)]
                             [(JmpIf cc label) (set-union (dict-ref label->live label) prev_liveness)]
                             [else prev_liveness])]
            [new_liveness (set-union (set-subtract prev_liveness locations_written) locations_read)])
       (append (uncover-live-instrs rest_instrs new_liveness) (list new_liveness)))]))

(define (uncover-live-block blocks label)
  (match (dict-ref blocks label)
    [(Block info instrs) (let* ([liveness-set (uncover-live-instrs (reverse instrs) (list (set)))]
                                [info (dict-set info 'liveness liveness-set)]
                                [_ (dict-set! label->live label (car liveness-set))])
                           (cons label (Block info instrs)))]))

(define (get-topo-sorted-cfg blocks)
  (let* ([cfg (multigraph (make-hash))]
         [_ (for ([blok blocks])
              (for ([instr (Block-instr* (cdr blok))])
                (match instr
                  [(Jmp label_to) (add-directed-edge! cfg (car blok) label_to)]
                  [(JmpIf cc label_to) (add-directed-edge! cfg (car blok) label_to)]
                  [else 0])))])
    (cdr (tsort (transpose cfg))))) ;; Last block is conclusion.

(define (uncover_live p)
  (match p
    [(X86Program info blocks)
     (let* ([toposorted-cfg (get-topo-sorted-cfg blocks)]
            [info (dict-set info 'topo-sorted toposorted-cfg)] ;; For checking.
            [_ (dict-set! label->live
                          'conclusion
                          (set (Reg 'rax) (Reg 'rsp)))] ;; Conclusion block is always the same.
            [new_blocks (map (lambda (x) (uncover-live-block blocks x)) toposorted-cfg)])
       (X86Program info new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-interference-edges instrs liveness_after)
  (let* ([var_written (match instrs
                        [(Instr 'movzbq es) (filter-var-reg es)]
                        [(Instr 'movq es) (filter-var-reg es)]
                        [else (instr-location-written instrs)])]
         [liveness_rem (set->list (set-subtract liveness_after var_written))]
         [var_written_list (match instrs
                             [(Instr 'movq es) (list (last es))]
                             [(Instr 'movzbq es) (list (last es))]
                             [else (set->list var_written)])])
    (cartesian-product var_written_list liveness_rem)))

(define (flatten-shallow lst)
  (foldr append '() lst))

(define (get-liveness-from-block info)
  (let* ([liveness (dict-ref info 'liveness)] [liveness (append (cdr liveness) (list (set)))])
    liveness))

(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (let* ([all_instrs (flatten-shallow (map (lambda (blok) (Block-instr* (cdr blok))) blocks))]
            [liveness (flatten-shallow
                       (map (lambda (blok) (get-liveness-from-block (Block-info (cdr blok))))
                            blocks))]
            [edges (map get-interference-edges all_instrs liveness)]
            [graph (undirected-graph (flatten-shallow edges))]
            [info (dict-set info 'conflicts graph)])
       (X86Program info blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (update-saturation handle color pq)
  (let* ([var (car (node-key handle))]
         [saturation (cdr (node-key handle))]
         [new-sat (set-union saturation (set color))])
    (set-node-key! handle (cons var new-sat))
    (pqueue-decrease-key! pq handle)))

(define (update-saturations graph handles var color pq)
  (let* ([req_neighbours (filter Var? (sequence->list (in-neighbors graph var)))]
         [_ (for ([neighbour req_neighbours])
              (let* ([handle (dict-ref handles (Var-name neighbour) #f)]
                     [_ (cond
                          [handle (update-saturation handle color pq)]
                          [else 0])])
                0))])
    0))

(define (get_greedy_color sat_popped num)
  (cond
    [(set-member? sat_popped num) (get_greedy_color sat_popped (+ num 1))]
    [else num]))

(define (loop i graph handles pq)
  (cond
    [(= i 0) (list)]
    [else (let* ([top_node (pqueue-pop! pq)]
                 [_ (dict-remove! handles (car top_node))]
                 [reqd_color (get_greedy_color (cdr top_node) 0)]
                 [color_pair (cons (Var (car top_node)) reqd_color)]
                 [_ (update-saturations graph handles (Var (car top_node)) reqd_color pq)]
                 [lst (append (list color_pair) (loop (- i 1) graph handles pq))])
            lst)]))

(define (saturation-cmp x y)
  (> (set-count (cdr x)) (set-count (cdr y))))

(define (color_graph vars graph)
  (let* ([vertices (get-vertices graph)]
         [registers-used (filter Reg? vertices)]
         [var_color (list)]
         [pq (make-pqueue saturation-cmp)]
         [handles (make-hash)]
         [_ (for ([var vars])
              (let* ([handle (pqueue-push! pq (cons var (set)))] [_ (dict-set! handles var handle)])
                0))]
         [_ (for ([reg registers-used])
              (let* ([reg_name (Reg-name reg)]
                     [_ (set! var_color
                              (append var_color (list (cons reg (register->color reg_name)))))]
                     [_ (update-saturations graph handles reg (register->color reg_name) pq)])
                0))]
         [vars (loop (pqueue-count pq) graph handles pq)])
    (append var_color vars)))

(define (get-color-to-home color max_register used_callee_count)
  (cond
    [(< color max_register) (cons color (Reg (color->register color)))]
    [else (let* ([total_offset (- (* offset (+ 1 (+ used_callee_count (- color max_register)))))])
            (cons color (Deref 'rbp total_offset)))]))

(define (get-colors-to-home colors used_callee_count)
  (let* ([max_register (num-registers-for-alloc)])
    (for/list ([color colors])
      (get-color-to-home color max_register used_callee_count))))

(define (allocate-register-arg arg var-to-color color-to-home)
  (match arg
    [(Var v)
     (let* ([color (dict-ref var-to-color (Var v))] [home (dict-ref color-to-home color)]) home)]
    [else arg]))

(define (allocate-register-instr instr var-to-color color-to-home)
  (match instr
    [(Instr op args) (Instr op
                            (for/list ([arg args])
                              (allocate-register-arg arg var-to-color color-to-home)))]
    [else instr]))

(define (allocate-register-instrs instrs var-to-color color-to-home)
  (map (lambda (instr) (allocate-register-instr instr var-to-color color-to-home)) instrs))

(define (allocate-register-block cur_block var-to-color color-to-home)
  (match cur_block
    [(cons label (Block info instrs))
     (cons label (Block info (allocate-register-instrs instrs var-to-color color-to-home)))]))

(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (let* ([used_callee (map Reg remaining-reg)]
            [info (dict-set info 'used_callee used_callee)]
            [used_callee_count (set-count used_callee)]
            [var-to-color (color_graph (dict-keys (dict-ref info 'locals-types))
                                       (dict-ref info 'conflicts))]
            [colors (list->set (filter (lambda (x) (>= x 0)) (map cdr var-to-color)))]
            [color-to-home (get-colors-to-home colors used_callee_count)]
            [num_spilled (length (filter (lambda (x) (Deref? (cdr x))) color-to-home))]
            [info (dict-set info 'num_spilled num_spilled)]
            [new_blocks
             (map (lambda (x) (allocate-register-block x var-to-color color-to-home)) blocks)])
       (X86Program info new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; ("partial evaluation" ,pe-Lvar ,interp-Lvar)
  `(("shrink" ,shrink ,interp-Lif ,type-check-Lif)
    ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
    ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cwhile)
    ("instruction selection" ,select-instructions ,interp-x86-1)
    ("liveness analysis" ,uncover_live ,interp-x86-1)
    ("build interference" ,build-interference ,interp-x86-1)
    ("allocate registers" ,allocate-registers ,interp-x86-1)
    ("patch instructions" ,patch-instructions ,interp-x86-1)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)))
    