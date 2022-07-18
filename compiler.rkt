#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require data/queue)
(require graph)
(require "interp.rkt")

(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Partial evaluation for Lvar language
;; Bonus question pass
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (make-inert ex)
  (match ex
    [(Int n) (cons n '())]
    ;;[(Let x e body) (cons 0 (Let x (pe-exp e) (pe-exp body)))]
    [(Prim '+ (list ex1 ex2)) (let* ([pair_data_1 (make-inert ex1)]
                                     [pair_data_2 (make-inert ex2)]
                                     [ex3 (cdr pair_data_1)]
                                     [ex4 (cdr pair_data_2)]
                                     [n_f (fx+ (car pair_data_1) (car pair_data_2))]
                                     [exp_f (cond
                                              [(and (empty? ex3) (empty? ex4)) empty]
                                              [(empty? ex4) ex3]
                                              [(empty? ex3) ex4]
                                              [else (Prim '+ (list ex3 ex4))])])
                                (cons n_f exp_f))]
    [else (cons 0 ex)]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(exp1 exp2) (let* ([data (make-inert (Prim '+ (list exp1 exp2)))]
                        [exp_f (cdr data)]
                        [ret (cond
                               [(= 0 (car data)) exp_f]
                               [(empty? exp_f) (Int (car data))]
                               [else (Prim '+ (list (Int (car data)) (cdr data)))])])
                   ret)]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Let x e body) (Let x (pe-exp e) (pe-exp body))]))

(define (pe-Lvar p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shrink Lvec -> Lvec
(define (shrink p)
  (match p
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (Var x)]
    [(Let var e body) (Let var (shrink e) (shrink body))]
    [(Prim 'and (list exp1 exp2)) (If (shrink exp1) (shrink exp2) (Bool #f))]
    [(Prim 'or (list exp1 exp2)) (If (shrink exp1) (Bool #t) (shrink exp2))]
    [(Prim op es) (Prim op (map shrink es))]
    [(If cond exp1 exp2) (If (shrink cond) (shrink exp1) (shrink exp2))]
    [(Begin e body) (Begin (map shrink e) (shrink body))]
    [(SetBang var rhs) (SetBang var (shrink rhs))]
    [(WhileLoop cnd body) (WhileLoop (shrink cnd) (shrink body))]
    [(HasType ex type) (HasType (shrink ex) type)]
    [(ProgramDefsExp info defs exp)
     (ProgramDefs info
                  (append (map shrink defs )(list (Def 'main empty 'Integer empty (shrink exp))) ))]
    [(Apply fun exps) (Apply (shrink fun) (map shrink exps))]
    [(Def name params rtype info body) (Def name params rtype info (shrink body))]
    [else
     error
     ("Invalid match at shrink.")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define fnames (make-hash))
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Void) (Void)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Var x) (Var (dict-ref env x))]
      [(Let var e body)
       (let* ([new_var (gensym var)]
              [e ((uniquify-exp env) e)]
              [new_env (dict-set env var new_var)]
              [body ((uniquify-exp new_env) body)])
         (Let new_var e body))]
      [(Prim op es)
       (Prim op
             (for/list ([e es])
               ((uniquify-exp env) e)))]
      [(If cond exp1 exp2)
       (let* ([new_cond ((uniquify-exp env) cond)]
              [new_exp1 ((uniquify-exp env) exp1)]
              [new_exp2 ((uniquify-exp env) exp2)])
         (If new_cond new_exp1 new_exp2))]
      [(Begin es body) (Begin (map (uniquify-exp env) es) ((uniquify-exp env) body))]
      [(SetBang var_sym rhs) (SetBang (dict-ref env var_sym) ((uniquify-exp env) rhs))]
      [(WhileLoop cnd body) (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(HasType exp type) (HasType ((uniquify-exp env) exp) type)]
      [(Apply fun exps) (Apply ((uniquify-exp env) fun) (map (uniquify-exp env) exps))]
      [(Def name params rty info body)
       (dict-set! fnames name (length params))
       (set! env (dict-set env name name))
       (define new_params
         (for/list ([param params])
           (define new_name (gensym (car param)))
           (set! env (dict-set env (car param) new_name))
           (cons new_name (cdr param))))
       (Def name new_params rty info ((uniquify-exp env) body))]
      [else (error "Invalid match at uniquify-exp.")])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
     (set! fnames (make-hash))
     (ProgramDefs info (map (uniquify-exp '()) defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (reveal_functions e)
  (match e
    [(ProgramDefs info defs) (ProgramDefs info (map reveal_functions defs))]
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Var x) (if (dict-ref fnames x #f) (FunRef x (dict-ref fnames x #f)) (Var x))]
    [(Bool b) (Bool b)]
      [(If cond exp1 exp2)
       (let* ([new_cond (reveal_functions cond)]
              [new_exp1 (reveal_functions exp1)]
              [new_exp2 (reveal_functions exp2)])
         (If new_cond new_exp1 new_exp2))]
     [(Let var e body)
       (let* ([e (reveal_functions e)]
              [body (reveal_functions body)])
         (Let var e body))]
    [(Begin exps body) (Begin (map reveal_functions exps) (reveal_functions body))]
    [(SetBang var_sym rhs) (SetBang var_sym (reveal_functions rhs))]
    [(WhileLoop cnd body) (WhileLoop (reveal_functions cnd) (reveal_functions body))]
    [(HasType exp type) (HasType (reveal_functions exp) type)]
    [(Prim op exps) (Prim op (map reveal_functions exps))]
    [(Apply fun exps) (Apply (reveal_functions fun) (map reveal_functions exps))]
    [(Def name params rtype info body) (Def name params rtype info (reveal_functions body))]
    [else (error "Invalid match at reveal_functions")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; get all accept first pos ones.
(define (get-other ls pos)
  (cond
    [(= pos 0) ls]
    [else (get-other (cdr ls) (- pos 1))]))

(define (limit-params params)
  (cond
    [(> (length params) 6)
     (append (take params 5)
             (list (append '(tup :) (list (append '(Vector) (map third (get-other params 5)))))))]
    [else params]))

(define (limit-args args)
  (cond
    [(> (length args) 6) (append (take args 5) (list (Prim 'vector (get-other args 5))))]
    [else args]))

(define (get-convert-dict params)
  (define ans_dict (make-hash))
  (define i 0)
  (for ([param params])
    (cond
      [(>= i 5)
       (dict-set! ans_dict (first param) (Prim 'vector-ref (list (Var 'tup) (Int (- i 5)))))])
    (set! i (+ i 1)))
  ans_dict)

(define (convert-exp env)
  (lambda (e)
    (match e
      [(Void) (Void)]
      [(Int n) (Int n)]
      [(Var x) (dict-ref! env x (Var x))]
      [(Bool b) (Bool b)]
      [(If cond exp1 exp2) 
           (If 
             ((convert-exp env) cond) 
             ((convert-exp env) exp1) 
             ((convert-exp env) exp2))]
      [(Let var e body) 
           (Let var 
                ((convert-exp env) e) 
                ((convert-exp env) body))]
      [(Begin es body) 
           (Begin 
             (map (convert-exp env) es) 
             ((convert-exp env) body))]
      [(SetBang var_sym rhs) 
           (SetBang var_sym ((convert-exp env) rhs))]
      [(WhileLoop cnd body) 
           (WhileLoop ((convert-exp env) cnd) ((convert-exp env) body))]
      [(HasType exp type) 
           (HasType ((convert-exp env) exp) type)]
      [(Prim op es) 
           (Prim op (map (convert-exp env) es))]
      [(Apply fun exps) 
           (Apply ((convert-exp env) fun) (map (convert-exp env) exps))]
      [(FunRef x n) (FunRef x n)]
      [else (error "Invalid match at convert-exp")])))

(define (limit_functions e)
  (match e
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [(FunRef x n) (FunRef x n)]
    [(If e1 e2 e3) 
         (If 
           (limit_functions e1) 
           (limit_functions e2) 
           (limit_functions e3))]
    [(Let var e body) 
         (Let var 
              (limit_functions e) 
              (limit_functions body))]
    [(Begin es body) 
         (Begin (map limit_functions es) (limit_functions body))]
    [(SetBang var_sym rhs) (SetBang var_sym (limit_functions rhs))]
    [(WhileLoop cnd body) (WhileLoop (limit_functions cnd) (limit_functions body))]
    [(HasType exp type) (HasType (limit_functions exp) type)]
    [(Prim op es) (Prim op (map limit_functions es))]
    [(Apply fun exps) (Apply (limit_functions fun) (limit-args exps))]
    [(Def name params rtype info body)
     (define new_params (limit-params params))
     (define new_body ((convert-exp (get-convert-dict params)) body))
     (Def name new_params rtype info (limit_functions new_body))]
    [(ProgramDefs info defs) 
         (ProgramDefs info (map limit_functions defs))]
      [else (error "Invalid match at limit_functions")]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (expose-allocation p)
  (match p
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Var x) (Var x)]
    [(Let var e body) (Let var (expose-allocation e) (expose-allocation body))]
    [(If cond exp1 exp2)
     (If (expose-allocation cond) (expose-allocation exp1) (expose-allocation exp2))]
    [(Begin es body) (Begin (map expose-allocation es) (expose-allocation body))]
    [(SetBang var_sym val) (SetBang var_sym (expose-allocation val))]
    [(Prim op exps) (Prim op (map expose-allocation exps))]
    [(WhileLoop cond body) (WhileLoop (expose-allocation cond) (expose-allocation body))]
    [(Program info e) (Program info (expose-allocation e))]
    [(HasType expr type)
     (let* ([exps (map expose-allocation (Prim-arg* expr))]
            [size (* 8 (+ 1 (length exps)))]
            [exp1 (Prim '+ (list (GlobalValue 'free_ptr) (Int size)))]
            [exp2 (GlobalValue 'fromspace_end)]
            [if_condition (If (Prim '< (list exp1 exp2)) (Void) (Collect (Int size)))]
            [vec-symb (gensym 'vec)]
            [allocate (Allocate (length exps) type)]
            [cnt 0]
            [init_vals (for/list ([exp exps])
                         (define ele (Prim 'vector-set! (list (Var vec-symb) (Int cnt) exp)))
                         (set! cnt (+ 1 cnt))
                         ele)]
            [vec-dec (Let vec-symb allocate (Begin init_vals (Var vec-symb)))])
      (Begin (list if_condition) vec-dec))]
    [(FunRef x n) (FunRef x n)]
    [(Apply fun exps) (Apply (expose-allocation fun) (map expose-allocation exps))]
    [(Def name params rty info body) (Def name params rty info (expose-allocation body))]
    [(ProgramDefs info defs) (ProgramDefs info (map expose-allocation defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (collect-set! e)
  (match e
    [(Void) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Var x) (set)]
    [(Collect n) (set)]
    [(Allocate n type) (set)]
    [(GlobalValue n) (set)]
    [(If cond exp1 exp2) (set-union (collect-set! cond) (collect-set! exp1) (collect-set! exp2))]
    [(Let var e body) (set-union (collect-set! e) (collect-set! body))]
    [(SetBang var e) (set-union (set var) (collect-set! e))]
    [(WhileLoop cond body) (set-union (collect-set! cond) (collect-set! body))]
    [(Prim op exps)
     (let* ([exp-sets (map collect-set! exps)] [final-sets (append exp-sets (list (set)))])
       (apply set-union final-sets))]
    [(Begin exps body)
     (let* ([exp-sets (map collect-set! exps)]
            [final-sets (append exp-sets (list (set)))]
            [body-set (collect-set! body)]
            [applied (apply set-union final-sets)])
       (set-union applied body-set))]
    [(FunRef x n) (set)]
    [(Apply fun exps) (set-union (collect-set! fun)
                                 (apply set-union (append (map collect-set! exps) (list (set)))))]
    [(Def name params rtype info body) (collect-set! body)]))

(define (uncover-get!-exp set!-vars)
  (lambda (e)
    (match e
      [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
      [(Bool x) (Bool x)]
      [(Int x) (Int x)]
      [(Void) (Void)]
      [(Collect n) (Collect n)]
      [(Allocate n type) (Allocate n type)]
      [(GlobalValue n) (GlobalValue n)]
      [(If cond exp1 exp2) (If ((uncover-get!-exp set!-vars) cond)
                         ((uncover-get!-exp set!-vars) exp1)
                         ((uncover-get!-exp set!-vars) exp2))]
      [(Let x e body)
       (Let x ((uncover-get!-exp set!-vars) e) ((uncover-get!-exp set!-vars) body))]
      [(SetBang var e) (SetBang var ((uncover-get!-exp set!-vars) e))]
      [(WhileLoop cond body) (WhileLoop ((uncover-get!-exp set!-vars) cond)
                                       ((uncover-get!-exp set!-vars) body))]
      [(Prim op es) (Prim op (map (uncover-get!-exp set!-vars) es))]
      [(Begin es body) (Begin (map (uncover-get!-exp set!-vars) es)
                              ((uncover-get!-exp set!-vars) body))]
      [(FunRef x n) (FunRef x n)]
      [(Apply fun exps) (Apply ((uncover-get!-exp set!-vars) fun)
                               (map (uncover-get!-exp set!-vars) exps))]
      [(Def name params rtype info body)
       (Def name params rtype info ((uncover-get!-exp set!-vars) body))])))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info
                                          (for/list ([def defs])
                                            (define set!-vars (collect-set! def))
                                            ((uncover-get!-exp set!-vars) def)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return cons(atom, (list (cons variables exp)))
(define (rco-atom expr)
  (define new_sym (gensym 'temp))
  (define new_var (Var new_sym))
  (match expr
    [(Void) (cons (Void) '())]
    [(Int x) (cons (Int x) (list))]
    [(Bool b) (cons (Bool b) (list))]
    [(Var var) (cons (Var var) (list))]
    [(GetBang x)
     (let* ([new_sym (gensym 'bang)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (Var x)))))]
    [(Collect n)
     (let* ([new_sym (gensym 'collect)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (Collect n)))))]
    [(Allocate n type)
     (let* ([new_sym (gensym 'allocate)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (Allocate n type)))))]
    [(GlobalValue n)
     (let* ([new_sym (gensym 'global)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (GlobalValue n)))))]
    [(WhileLoop cnd body)
     (let* ([new_sym (gensym 'while)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (WhileLoop (rco-exp cnd) (rco-exp body))))))]
    [(Begin es body)
     (let* ([new_sym (gensym 'begin)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (Begin (map rco-exp es) (rco-exp body))))))]
    [(SetBang x val)
     (let* ([new_sym (gensym 'bang)] [new_var (Var new_sym)])
       (cons new_var (list (cons new_sym (SetBang x (rco-exp val))))))]
    [(If cond exp1 exp2)
     (let* ([new_sym (gensym 'new)]
            [new_var (Var new_sym)]
            [list_e (cons new_sym (If (rco-exp cond) (rco-exp exp1) (rco-exp exp2)))])
       (cons new_var (list list_e)))]
    [(Let x e body)
     (let* ([new_sym (gensym 'new)]
            [new_var (Var new_sym)]
            [list_e (cons x (rco-exp e))]
            [list_body (cons new_sym (rco-exp body))]
            [list_combined (append (list list_e) (list list_body))])
       (cons new_var list_combined))]
    [(Prim op es)
     (let* ([new_sym (gensym 'new)]
            [new_var (Var new_sym)]
            [pairs (map rco-atom es)]
            [atoms (map car pairs)]
            [lists (map cdr pairs)]
            [combined_lists (foldr append (list) lists)]
            [combined_lists (append combined_lists (list (cons new_sym (Prim op atoms))))])
       (cons new_var combined_lists))]
    [(Apply fun es)
     (let* ([new_sym (gensym 'temp)]
            [new_var (Var new_sym)]
            [pairs (map rco-atom es)]
            [atoms (map car pairs)]
            [fun-ref-pair (rco-atom fun)]
            [fun-ref-atom (car fun-ref-pair)]
            [vs (append (foldr append '() (append (map cdr pairs) (list (cdr fun-ref-pair))))
                        (list (cons new_sym (Apply fun-ref-atom atoms))))])
       (cons new_var vs))]
    [(FunRef x n) (cons new_var (list (cons new_sym (FunRef x n))))]))

(define (generate-lets lst)
  (match lst
    [(list (cons x y)) y]
    [(cons (cons x y) z) (Let x y (generate-lets z))]
    [else
     error
     ("Invalid match in generate-lets.")]))

(define (rco-exp e)
  (match e
    [(Void) (Void)]
    [(Int x) (Int x)]
    [(Bool b) (Bool b)]
    [(Var var) (Var var)]
    [(Collect n) (Collect n)]
    [(Allocate n type) (Allocate n type)]
    [(GlobalValue n) (GlobalValue n)]
    [(Prim 'read (list)) (Prim 'read (list))]
    [(Prim op es) (generate-lets (cdr (rco-atom (Prim op es))))]
    [(Let var e body) (Let var (rco-exp e) (rco-exp body))]
    [(If cond exp1 exp2) (If (rco-exp cond) (rco-exp exp1) (rco-exp exp2))]
    [(SetBang var val) (SetBang var (rco-exp val))]
    [(GetBang var) (Var var)]
    [(WhileLoop cond body) (WhileLoop (rco-exp cond) (rco-exp body))]
    [(Begin e body) (Begin (map rco-exp e) (rco-exp body))]
    ;; Functions
    [(FunRef x n) (FunRef x n)]
    [(Apply fun exps) (generate-lets (cdr (rco-atom (Apply fun exps))))]
    [(Def name params rty info body) (Def name params rty info (rco-exp body))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map rco-exp defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define CFG (make-hash))

(define (add-to-cfg block)
  (match block
    [(Goto label) (Goto label)]
    [else (let* ([label (gensym 'label)] [_ (hash-set! CFG label block)]) (Goto label))]))

(define (assign-block-to-label block label)
  (let* ([_ (dict-set! CFG label block)]) (Goto label)))

;; explicate-pred: Lwhile, e1, e2 -> C1 tail
(define (explicate-pred pred exp1 exp2)
  (match pred
    [(Bool #t) exp1]
    [(Bool #f) exp2]
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(Let var e body) (explicate-assign e var (explicate-pred body exp1 exp2))]
    [(Prim cmp (list x y)) (IfStmt (Prim cmp (list x y)) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(Prim 'not (list x)) (IfStmt (Prim 'eq? (list x (Bool #f))) (add-to-cfg exp1) (add-to-cfg exp2))]
    [(If cond a b)
     (let* ([x (add-to-cfg exp1)] [y (add-to-cfg exp2)])
       (explicate-pred cond (explicate-pred a x y) (explicate-pred b x y)))]
    [(Begin es body) (let* ([tail (explicate-pred body exp1 exp2)]) (foldr explicate-effect body es))]
    [else (error "explicate-pred unhandled case" pred)]))

(define (get-while cond body tail)
  (let* ([sym (gensym 'loop)]
         [goto (Goto sym)]
         [body (explicate-effect body goto)]
         [loop (explicate-pred cond body tail)]
         [_ (assign-block-to-label loop sym)])
    loop))

(define (explicate-effect e cont)
  (match e
    [(Void) cont]
    [(Int x) cont]
    [(Bool x) cont]
    [(Var x) cont]
    [(Collect n) (Seq (Collect n) cont)]
    [(Allocate n type) cont]
    [(GlobalValue n) cont]
    [(Prim 'read (list)) (Seq (Prim 'read (list)) cont)]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
    [(Prim op es) cont]
    [(Let var val body) (let* ([body (explicate-effect body cont)]) (explicate-assign val var body))]
    [(If cond exp1 exp2)
     (let* ([goto (add-to-cfg cont)]
            [tail1 (explicate-effect exp1 goto)]
            [tail2 (explicate-effect exp2 goto)])
       (explicate-pred cond tail1 tail2))]
    [(Begin es body) (foldr explicate-effect cont (append es (list body)))]
    [(WhileLoop cond body) (get-while cond body cont)]
    [(SetBang x val) (explicate-assign val x cont)]
    ;; Functions
    [(FunRef label n) cont]
    [(Apply fun exps) (Seq (Call fun exps) cont)]))

;; explicate-tail : Lwhile -> C1 tail
(define (explicate-tail e)
  (match e
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Var var) (Return (Var var))]
    [(Collect n) (Return (Collect n))]
    [(Allocate n type) (Return (Allocate n type))]
    [(GlobalValue n) (Return (GlobalValue n))]
    [(Let x assign_val return_val)
     (let* ([tail (explicate-tail return_val)]) (explicate-assign assign_val x tail))]
    [(Prim op es) (Return (Prim op es))]
    [(If cond exp1 exp2) (explicate-pred cond (explicate-tail exp1) (explicate-tail exp2))]
    [(Begin exps body)
     (let* ([tail (explicate-tail body)] [seq (foldr explicate-effect tail exps)]) seq)]
    [(SetBang x rhs) (explicate-assign rhs x (Return Void))]
    [(WhileLoop cond body) (get-while cond body (Return (Void)))]
    ;; Functions
    [(FunRef label n) (Return (FunRef label n))]
    [(Apply fun exps) (TailCall fun exps)]
    [else (error "explicate-tail unhandled case" e)]))

;; explicate_assign : Lwhile, Var x, C1 tail -> C1 tail
(define (explicate-assign e x tail)
  (match e
    [(Int n) (Seq (Assign (Var x) (Int n)) tail)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) tail)]
    [(Var y) (Seq (Assign (Var x) (Var y)) tail)]
    [(Collect n) (Seq (Assign (Var x) (Collect n)) tail)]
    [(Allocate n type) (Seq (Assign (Var x) (Allocate n type)) tail)]
    [(GlobalValue n) (Seq (Assign (Var x) (GlobalValue n)) tail)]
    [(Let y assign_val return_val)
     (let* ([tail (explicate-assign return_val x tail)]) (explicate-assign assign_val y tail))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) tail)]
    [(If cond exp1 exp2)
     (let* ([new_tail (add-to-cfg tail)]
            [tail1 (explicate-assign exp1 x new_tail)]
            [tail2 (explicate-assign exp2 x new_tail)])
       (explicate-pred cond tail1 tail2))]
    [(Begin exps body)
     (let* ([tail-2 (explicate-assign body x tail)] [cont (foldr explicate-effect tail-2 exps)])
       cont)]
    [(WhileLoop cond body) (Seq (Assign (Var x) (Void)) (get-while cond body tail))]
    [(SetBang y rhs) (Seq (Assign (Var x) (Void)) (explicate-assign rhs y tail))]
    [(Void) (Seq (Assign (Var x) (Void)) tail)]
    ;; Functions
    [(FunRef label n) (Seq (Assign (Var x) (FunRef label n)) tail)]
    [(Apply fun exps) (Seq (Assign (Var x) (Call fun exps)) tail)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : Lwhile -> C1
(define (explicate-control p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs
      info
      (for/list ([def defs])
        (set! CFG (make-hash))
        (match def
          [(Def name params type info exp)
           (dict-set! CFG
                      (string->symbol (string-append (symbol->string name) (symbol->string 'start)))
                      (explicate-tail exp))
           (Def name params type info (dict-copy CFG))])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-mask type position)
  (match type
    [(list) 0]
    [(cons sym remaining) (let* ([isvec (cond
                                          [(equal? sym 'Vector) (expt 2 position)]
                                          [else 0])]
                                 [remainingval (get-mask remaining (+ position 1))])
                            (+ isvec remainingval))]))

(define (get-tag n type)
  (begin
    (define frwd 1)
    (define size (* 2 n)) ;; shift it by one byte
    (define shiftvalue 8) ;; shift to the 8th bit (2 ** 7)
    (define mask (get-mask type shiftvalue))
    (+ mask size frwd)))

;; select-instructions-atm: C0 atom -> pseudo-x86 atom
(define (select-instructions-atm atm)
  (match atm
    ['eq? 'e]
    ['> 'g]
    ['>= 'ge]
    ['< 'l]
    ['<= 'le]
    [(Void) (Imm 0)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Int x) (Imm x)]
    [(Var x) (Var x)]
    [(GlobalValue x) (Global x)]
    [else (error "select-instructions-atm unhandled case" atm)]))

(define (select-instructions-exp p)
  (match p
    [(Seq x y) (append (select-instructions-exp x) (select-instructions-exp y))]
    [(Assign x (Prim '+ (list exp1 exp2)))
     (cond
       [(eq? x exp1)
        (list (Instr 'addq (list (select-instructions-atm exp2) (select-instructions-atm exp1))))]
       [(eq? x exp2)
        (list (Instr 'addq (list (select-instructions-atm exp1) (select-instructions-atm exp2))))]
       [else
        (list (Instr 'movq (list (select-instructions-atm exp1) x))
              (Instr 'addq (list (select-instructions-atm exp2) x)))])]

    [(Assign x (Prim '- (list a1)))
     (cond
       [(eq? x a1) (list (Instr 'negq (list (select-instructions-atm a1))))]
       [else (list (Instr 'movq (list (select-instructions-atm a1) x)) (Instr 'negq (list x)))])]

    [(Assign x (Prim '- (list a1 a2)))
     (cond
       [(eq? x a1)
        (list (Instr 'subq (list (select-instructions-atm a2) (select-instructions-atm a1))))]
       [else
        (list (Instr 'movq (list (select-instructions-atm a1) x))
              (Instr 'subq (list (select-instructions-atm a2) x)))])]
    [(Prim 'read '()) (list (Callq 'read_int 0))]
    [(Assign x (Allocate n type))
     (list (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
           (Instr 'addq (list (Imm (* 8 (+ n 1))) (Global 'free_ptr)))
           (Instr 'movq (list (Imm (get-tag n type)) (Deref 'r11 0)))
           (Instr 'movq (list (Reg 'r11) x)))]
    [(Prim 'vector-set! (list vec (Int pos) an_exp)) ;; vector ref can be a statement
     (list (Instr 'movq (list vec (Reg 'r11)))
           (Instr 'movq (list (select-instructions-atm an_exp) (Deref 'r11 (* (+ 1 pos) 8)))))]
    [(Assign x (Prim 'vector-set! (list vec (Int pos) an_exp)))
     (list (Instr 'movq (list vec (Reg 'r11)))
           (Instr 'movq (list (select-instructions-atm an_exp) (Deref 'r11 (* (+ 1 pos) 8))))
           (Instr 'movq (list (Imm 0) x)))]
    [(Assign x (Prim 'vector-ref (list vec (Int pos))))
     (list (Instr 'movq (list vec (Reg 'r11))) (Instr 'movq (list (Deref 'r11 (* (+ 1 pos) 8)) x)))]
    [(Assign x (Prim 'vector-length (list vec)))
     (list (Instr 'movq (list vec (Reg 'r11)))
            (Instr 'movq (list (Deref 'r11 0) x))
            (Instr 'sarq (list (Imm 1) x))
            (Instr 'andq (list (Imm 127) x)))]
    [(Collect (Int n))
     (list (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
           (Instr 'movq (list (Imm n) (Reg 'rsi)))
           (Callq 'collect 2))]
    [(Assign x (Prim 'read '())) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
    [(Assign x (Prim 'not (list exp1)))
     (list (Instr 'movq (list (select-instructions-atm exp1) x)) (Instr 'xorq (list (Imm 1) x)))]
    [(Assign x (Prim cmp (list a1 a2)))
     (let* ([instr1 (Instr 'cmpq
                           (list (select-instructions-atm a2)
                                 (select-instructions-atm a1)))] ;; Args flipped in cmpq
            [instr2 (Instr 'set (list (select-instructions-atm cmp) (Reg 'al)))]
            [instr3 (Instr 'movzbq (list (Reg 'al) x))])
       (list instr1 instr2 instr3))]

    [(Assign x (FunRef label n)) (list (Instr 'leaq (list (Global label) x)))]
    [(Assign x (Call fun args))
     (let* ([regs (map Reg '(rdi rsi rdx rcx r8 r9))]
            [instrs_mov_args (for/list ([arg args] [reg regs])
             (Instr 'movq (list (select-instructions-atm arg) reg)))]) 
            (flatten (list instrs_mov_args (IndirectCallq fun (length args)) (Instr 'movq (list (Reg 'rax) x)))))]
    ;; Reassign variable
    [(Call fun args) 
     (let* ([regs (map Reg '(rdi rsi rdx rcx r8 r9))]
            [instrs_mov_args 
               (for/list ([arg args] [reg regs])
                 (Instr 'movq (list (select-instructions-atm arg) reg)))]
            [call_instr (IndirectCallq fun (length args))])
     (flatten (list instrs_mov_args call_instr)))]
    [(Assign x y) (list (Instr 'movq (list (select-instructions-atm y) x)))]
    ;; Tails
    [(TailCall fun args)
     (let* ([regs (map Reg '(rdi rsi rdx rcx r8 r9))]
            [instrs_mov_args
               (for/list ([arg args] [reg regs])
                 (Instr 'movq (list (select-instructions-atm arg) reg)))]
            [call_instr (TailJmp fun (length args))]) 
         (flatten (list instrs_mov_args call_instr)))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim 'vector-ref (list a1 (Int pos))) (Goto l1) (Goto l2))
     (flatten (list (select-instructions-exp (Assign (Reg 'rax) (Prim 'vector-ref (list a1 (Int pos)))))
            (Instr 'cmpq (list (Reg 'rax) (Imm 1)))
            (JmpIf 'e l1)
            (Jmp l2)))]
    [(IfStmt (Prim cmp (list a1 a2)) (Goto l1) (Goto l2))
     (list (Instr 'cmpq
                   (list (select-instructions-atm a2)
                         (select-instructions-atm a1)))
            (JmpIf (select-instructions-atm cmp) l1)
            (Jmp l2))]
    [(Return e) (flatten (list (select-instructions-exp (Assign (Reg 'rax) e))
                        (Jmp (conclusion-name fn-name))))]))

(define (select-instructions-block blck)
  (match blck
    [(cons label cmds) (cons label (Block '() (select-instructions-exp cmds)))]))

(define (start-name name)
  (string->symbol (string-append (symbol->string name) (symbol->string 'start))))

(define (conclusion-name name)
  (string->symbol (string-append (symbol->string name) (symbol->string 'conclusion))))

(define fn-name 'randoma)
(define (select-instructions-def def)
  (match def
    [(Def name params type info body) (let* 
        ([_ (set! fn-name name)]
         [regs (map Reg '(rdi rsi rdx rcx r8 r9))]
         [new_instrs empty]
         [_ (for ([param params] [reg regs])
           (set! new_instrs (append new_instrs (list (Instr 'movq (list reg (Var (car param))))))))]
         [new_body (map select-instructions-block (hash->list body))]
         [instrs_for_start (Block-instr* (dict-ref new_body (start-name name)))]
         [newer_body (dict-set new_body (start-name name) (Block '() (append new_instrs instrs_for_start)))]
         [new_info (dict-set info 'num-params (length params))]) 
         (Def name '() type new_info newer_body))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map select-instructions-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assign homes is no longer required, hence has been removed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

(define (fix-instr inst)
    (match inst
      [(Instr 'movq (list arg arg)) (list)]
      [(Instr 'movzbq (list arg1 (Deref reg1 off1)))
         (list (Instr 'movq (list (Deref reg1 off1) (Reg 'rax))) (Instr 'movzbq (list arg1 (Reg 'rax))))]
      [(Instr 'leaq (list arg1 (Deref reg1 off1)))
       (list (Instr 'leaq (list arg1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref reg1 off1))))]
      [(Instr 'cmpq (list arg1 (Imm x)))
       (list (Instr 'movq (list (Imm x) (Reg 'rax))) (Instr 'cmpq (list arg1 (Reg 'rax))))]
      [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
         (list (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
               (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
      [(TailJmp target n) (list (Instr 'movq (list target (Reg 'rax))) (TailJmp (Reg 'rax) n))]
      [else (list inst)]))

(define (fix-instructions instr_list)
  (flatten (map fix-instr instr_list)))

(define (patch-block pr)
  (cons (car pr)
        (match (cdr pr)
          [(Block info instrs) (Block info (flatten (fix-instructions instrs)))]
          [else
           error
           "Not a valid block"])))

(define (patch-instructions-def def)
  (match def
    [(Def name params type info blocks) (Def name params type info (map patch-block blocks))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map patch-instructions-def defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; prelude-and-conclusion : x86 -> x86
(define (all-but-last lst)
  (match lst
    [(list) (list)]
    [else (reverse (cdr (reverse lst)))]))

(define (remove-tail-jmps replacement)
  (lambda (blck)
    (match blck
      [(cons label (Block info instrs))
       (let* ([last_instr (last instrs)]
           [new_instrs (match last_instr
                   [(TailJmp x n) (append replacement (list (IndirectJmp x)))]
                   [else (list last_instr)])])
       (cons label (Block info (flatten (append (all-but-last instrs) new_instrs)))))]
      [else (error "undefined for remove tail jumps" blck)])))

(define (align-stack-space num_vars)
  (let* ([stackspace (* 1 num_vars)] [stackspace (align stackspace 16)]) stackspace))
(define (get-stack-space info)
  (let* ([local_types (length (dict-keys (dict-ref info 'locals-types)))]
         [local_var_size (* 1 (dict-ref info 'num_spilled))]
         [callee-size (* 8 (length (dict-ref info 'used_callee)))]
         [stacksize (+ (* 8 local_types) (+ (* 1 callee-size) (* 8 local_var_size)))]
         [stacksize (* 1 stacksize)]
         [stacksize (align-stack-space stacksize)]
         [stacksize (- stacksize callee-size)])
    stacksize))

(define (pnc-def def)
  (match def
    [(Def name params type info blocks)
     (set! fn-name name)
     (let* ([callee-saved (dict-ref info 'used_callee)]
            [instr-callee-push (for/list ([reg callee-saved])
                                 (Instr 'pushq (list reg)))]
            [instr-callee-pop (for/list ([reg (reverse callee-saved)])
                                (Instr 'popq (list reg)))]
            [stacksize (get-stack-space info)]
            [root-stack-instrs2 (make-list (dict-ref info 'num-root-spills)
                                           (list (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
                                                 (Instr 'addq (list (Imm 8) (Reg 'r15)))))]
            [main_block
             (if (eq? fn-name 'main)
                 (Block empty
                        (flatten (list 
                                    (Instr 'pushq (list (Reg 'rbp)))
                                    (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                       instr-callee-push
                                    (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))
                                    (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                                    (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                                    (Callq 'initialize 2)
                                    (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
                                       root-stack-instrs2
                                    (Jmp (start-name fn-name))
                                    )))

                 (Block empty
                        (flatten
                         (list 
                            (Instr 'pushq (list (Reg 'rbp)))
                            (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                            instr-callee-push
                            root-stack-instrs2
                            (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))
                            (Jmp (start-name fn-name))
                           ))))]
            [conclusion_block
             (Block empty 
                    (flatten 
                      (list 
                        (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))
                        instr-callee-pop 
                        (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15)))
                        (Instr 'popq (list (Reg 'rbp)))
                        (Retq))))]
            [replace_by 
              (list 
                (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))
                instr-callee-pop 
                (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15)))
                (Instr 'popq (list (Reg 'rbp)))
                )]
            [blocks (map (remove-tail-jmps replace_by) blocks)]
            [blocks (dict-set* blocks fn-name main_block (conclusion-name fn-name) conclusion_block)])
       blocks)]
    [else (error "Invalid instruction at prelude-def" def)]))

(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs info defs) (X86Program info (flatten-shallow (map pnc-def defs)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define label->live (make-hash))
(define caller-saved '(rcx rdx rsi rdi r8 r9 r10 r11))
(define callee-saved '(rdi rsi rdx rcx r8 r9))
(define offset 8)

(define global-blocks (make-hash))

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
                      [(Instr 'leaq (list arg1 arg2)) (list arg1)]
                      [(IndirectCallq x y) (append (list x) (map Reg (take callee-saved y)))]
                      [(TailJmp x y) (append (list x) (list (Reg 'rax) (Reg 'rsp)) (map Reg (take callee-saved y)))]
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
                      [(IndirectCallq x y) (map Reg caller-saved)]
                      [(TailJmp x y) (map Reg caller-saved)]
                      [else (error "Invalid instruction at instr-location-written." instr)])])
    (filter-var-reg live_list)))

(define (uncover-live-instrs instrs prev_liveness)
  (define reverse-instrs (reverse instrs))
  (define liveness
    (for/list ([instr reverse-instrs])
      (define locations_read (instr-location-read instr))
      (define locations_written (instr-location-written instr))
      (define new_liveness (set-union (set-subtract prev_liveness locations_written) locations_read))
      (set! prev_liveness new_liveness)
      new_liveness))
  (reverse liveness))

(define all-blocks (make-hash))
(define (analyze_dataflow G transfer join)
  (let* ([mapp (make-hash)]
         [_ (for ([v (in-vertices G)])
              (dict-set! mapp v (set)))]
         [worklist (make-queue)]
         [_ (for ([v (in-vertices G)])
              (enqueue! worklist v))]
         [tG (transpose G)]
         [_ (while (not (queue-empty? worklist))
                   (let* ([top-node (dequeue! worklist)]
                          [input (for/fold ([state (set)]) ([pred (in-neighbors tG top-node)])
                                   (join state (dict-ref mapp pred)))]
                          [output (transfer top-node input)]
                          [req_cond (not (equal? output (dict-ref mapp top-node)))]
                          [_ (if req_cond (dict-set! mapp top-node output) 0)]
                          [_ (if req_cond
                                 (for ([v (in-neighbors G top-node)])
                                   (enqueue! worklist v))
                                 0)])
                     0))])
    mapp))

(define (transfer! block_label live_after_set)
  (cond
    [(eq? block_label (conclusion-name fn-name)) (set (Reg 'rax) (Reg 'rsp))]
    [else
     (let* ([blok (dict-ref global-blocks block_label)]
            [instrs (Block-instr* blok)]
            [liveness (uncover-live-instrs instrs live_after_set)]
            [new_info (dict-set (Block-info blok) 'liveness liveness)]
            [new_blok (Block new_info instrs)]
            [_ (dict-set! global-blocks block_label new_blok)])
       (car liveness))]))

(define (get-transpose-cfg blocks)
  (let* ([cfg (multigraph (make-hash))]
         [_ (for ([blok blocks])
              (dict-set! global-blocks (car blok) (cdr blok))
              (add-vertex! cfg (car blok))
              (for ([instr (Block-instr* (cdr blok))])
                (match instr
                  [(Jmp label_to) (add-directed-edge! cfg (car blok) label_to)]
                  [(JmpIf cc label_to) (add-directed-edge! cfg (car blok) label_to)]
                  [else 0])))])
    (transpose cfg)))

(define (uncover-live-def def)
  (match def
    [(Def name params type info blocks)
     (set! global-blocks (make-hash))
     (set! fn-name name)
     (let* ([transposed-CFG (get-transpose-cfg blocks)]
            [_ (analyze_dataflow transposed-CFG transfer! set-union)])
       (Def name params type info (hash->list global-blocks)))]))

(define (uncover_live p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map uncover-live-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define new-callee-saved '(rax rcx rdx rsi rdi r8 r9 r10 r11 rsp rbp rbx r12 r13 r14 r15))
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
(define (is_tuple type)
  (match type
    [(cons var_name type)
     (and (list? type) (eq? (first type) 'Vector))] ;; TODO test with vector functions
    ))

(define (get-liveness-from-block info)
  (let* ([liveness (dict-ref info 'liveness)] [liveness (append (cdr liveness) (list (set)))])
    liveness))

(define (build-interference-def def)
  (match def
    [(Def name params type info blocks)
     (let* (
            [all_instrs (flatten-shallow (map (lambda (blok) (Block-instr* (cdr blok))) blocks))]
            [liveness (flatten-shallow
                       (map (lambda (blok) (get-liveness-from-block (Block-info (cdr blok))))
                            blocks))]
            [edges (map get-interference-edges all_instrs liveness)]
            [tuples (get-tuples info)]
            [more (cartesian-product tuples (map Reg new-callee-saved))]
            [edges (append edges more)]
            [graph (undirected-graph (flatten-shallow edges))]
            [info (dict-set info 'conflicts graph)]
            [info (dict-set info 'num-root-spills (length tuples))])
       (Def name params type info blocks))]))

(define (build-interference p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map build-interference-def defs))]))

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
    [else
     (let* ([top_node (pqueue-pop! pq)]
            [_ (dict-remove! handles (car top_node))]
            [reqd_color (get_greedy_color (cdr top_node) 0)]
            [color_pair (cons (Var (car top_node)) reqd_color)]
            [_ (update-saturations graph handles (Var (car top_node)) reqd_color pq)]
            [lst (append (list color_pair) (loop (- i 1) graph handles pq))])
       lst)]))

(define (saturation-cmp x y)
  (> (set-count (cdr x)) (set-count (cdr y))))

(define (color_graph graph vars)
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
    [else
     (let* ([total_offset (- (* offset (+ 1 (+ used_callee_count (- color max_register)))))])
       (cons color (Deref 'rbp total_offset)))]))

(define (get-colors-to-home colors used_callee_count)
  (let* ([max_register (num-registers-for-alloc)])
    (for/list ([color colors])
      (get-color-to-home color max_register used_callee_count))))

(define root-offsets (make-hash))
(define counter 0)

(define (allocate-register-arg arg var-to-color color-to-home tuples)
  (match arg
    [(Var v)
     (if (member v tuples)
         (let ([offset (dict-ref root-offsets
                                 v
                                 (lambda ()
                                   (begin
                                     (set! counter (+ 1 counter))
                                     (dict-set! root-offsets v counter)
                                     counter)))])
           (Deref 'r15 (* offset 8)))
         (let* ([color (dict-ref var-to-color (Var v))] [home (dict-ref color-to-home color)]) home))]
    [else arg]))

(define (allocate-register-instrs inst_list vtc cth tuples)
  (for/list ([inst inst_list])
    (match inst
      [(Instr op args)
       (Instr op
              (for/list ([arg args])
                (allocate-register-arg arg vtc cth tuples)))]
      [(IndirectCallq arg n)
       (IndirectCallq
        (match arg
          [(Var v) (if (member v tuples)
                       (let ([offset (dict-ref root-offsets
                                               v
                                               (lambda ()
                                                 (begin
                                                   (set! counter (+ 1 counter))
                                                   (dict-set! root-offsets v counter)
                                                   counter)))])
                         (Deref 'r15 (* offset 8)))
                       (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)]) home))]
          [else arg])
        n)]
      [(TailJmp arg n)
       (TailJmp
        (match arg
          [(Var v) (if (member v tuples)
                       (let ([offset (dict-ref root-offsets
                                               v
                                               (lambda ()
                                                 (begin
                                                   (set! counter (+ 1 counter))
                                                   (dict-set! root-offsets v counter)
                                                   counter)))])
                         (Deref 'r15 (* offset 8)))
                       (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)]) home))]
          [else arg])
        n)]
      [else inst])))

(define (allocate-register-block cur_block vtc cth tuples)
  (match cur_block
    [(cons label (Block info instr_list))
     (cons label (Block info (allocate-register-instrs instr_list vtc cth tuples)))]))

(define (get-tuples info)
  (map car (filter (lambda (x) (is_tuple x)) (dict-ref info 'locals-types))))

(define remaining-reg (map Reg '(rbx r12 r13 r14)))

(define (allocate-registers-def def)
  (match def
    [(Def name param type info blocks)
     (let* ([used_callee_count (set-count remaining-reg)]
            [var-to-color (color_graph (dict-ref info 'conflicts) (dict-keys (dict-ref info 'locals-types))
                                       )]
            [colors (list->set (filter (lambda (x) (>= x 0)) (map cdr var-to-color)))]
            [color-to-home (get-colors-to-home colors used_callee_count)]
            [num_spilled (length (filter (lambda (x) (Deref? (cdr x))) color-to-home))]
            [info (dict-set info 'used_callee remaining-reg)]
            [info (dict-set info 'num_spilled num_spilled)]
            [tuples (get-tuples info)]
            [new_blocks
             (map (lambda (x) (allocate-register-block x var-to-color color-to-home tuples)) blocks)])
       (Def name param type info new_blocks))]))

(define (allocate-registers p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map allocate-registers-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; ("partial evaluation" ,pe-Lvar ,interp-Lvar)
  `(("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ("reveal_functions" ,reveal_functions ,interp-Lfun-prime ,type-check-Lfun)
    ("limit_functions" ,limit_functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose_allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ("uncover-get!" ,uncover-get! ,interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ("liveness analysis" ,uncover_live ,interp-pseudo-x86-3)
    ("build interference" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers" ,allocate-registers ,interp-pseudo-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,#f)))
