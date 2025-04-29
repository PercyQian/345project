#lang racket

;; Percy Qian, Xiang Luo, Tongwei Zhang
;; Group23 for project 3
;; CSDS 345
;; 2025-04-13
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; REQUIREMENTS
;; Use the new parser that supports nested functions, closures,
;; and call-by-reference (with extra processing).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; use functionParser.rkt to parse the input file of 3test.txt
;; use simple-parser.rkt to parse the input file of 1test.txt and 2test.txt
(require (prefix-in class:  "classParser.rkt")
         (prefix-in func:   "functionParser.rkt")
         (prefix-in simple: "simpleParser.rkt"))


;; Create a wrapper function that chooses the correct parser based on filename
(define (parser filename)
  (cond [(regexp-match #rx"\\.j$"     filename) (class:parser filename)]
        [(regexp-match #rx"^3test"    filename) (func:parser   filename)]
        [else                                        (simple:parser filename)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operator Accessors for Lists
;;   operator      => operator 
;;   firstoperand  => firstoperand 
;;   secondoperand => secondoperand 
;;   drop-first-two=> drop-first-two
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define operator car )
(define firstoperand cadr )
(define secondoperand caddr )
(define drop-first-two cddr)
(define operands cdr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Closure Data Structure & Helper Functions
;;
;; A function closure is represented as:
;;   (closure <raw-params> <body> <def-env> <fname> <def-class>)
;; Parameters with a preceding ampersand (&) are processed into (ref x);
;; all other parameters pass through unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-closure
  (lambda (params body env fname . maybe-defclass)
    (if (null? maybe-defclass)
        (list 'closure params body env fname)
        (list 'closure params body env fname (car maybe-defclass)))))

(define closure?
  (lambda (v)
    (and (list? v) (eq? (operator  v) 'closure))))

(define closure-params (lambda (cl) (firstoperand  cl)))
(define closure-body   (lambda (cl) (secondoperand  cl)))
(define closure-env    (lambda (cl) (cadddr cl)))
(define closure-fname  (lambda (cl) (if (< (length cl) 5) #f (list-ref cl 4))))
(define closure-defclass (lambda (cl) (if (< (length cl) 6) #f (list-ref cl 5))))

(define process-params
  (lambda (params)
    (define (proc lst)
      (cond
        [(null? lst) '()]
        [(and (symbol? (operator  lst)) (eq? (operator  lst) '&))
         (if (null? (operands lst))
             (error 'process-params "Missing identifier after &")
             (cons (list 'ref (operator  (operands lst))) (proc (operands (operands lst)))))]
        [else (cons (operator  lst) (proc (operands lst)))]))
    (proc params)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; State Management
;;
;; A state (or environment) is a list of layers; each layer is an association list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-state
  (lambda () (list '())))  ;; one empty layer

(define push-layer
  (lambda (state) (cons '() state)))

(define pop-layer
  (lambda (state) (operands state)))

(define state-declare
  (lambda (var val state)
    (if (null? state)
        (error "Error: state is empty")
        (cons (cons (cons var (box val)) 
                  (if (assq var (operator state)) 
                      (remove (assq var (operator state)) (operator state))
                      (operator state)))
              (operands state)))))

(define base-state-lookup
  (lambda (var state)
    (cond
      [(null? state) 
       (error "Error: using before declaring" var)]
      [else
       (define binding (assq var (operator state)))
       (if binding
           (let ()
             (define val (unbox (operands binding)))
             (if (eq? val 'uninitialized)
                 0  ; Return default value 0 instead of reporting an error
                 val))
           (base-state-lookup var (operands state)))])))

(define (get-and-check-this state)
  (with-handlers 
    ([exn:fail? (lambda (e) #f)])  ;; 如果查找失败，返回 #f
    (let ([this (base-state-lookup 'this state)])
      (and this (objectC? this) this))))

(define state-lookup
  (lambda (var state . maybe-default)
    (define default (if (null? maybe-default) 
                       (lambda () (error 'state-lookup "using before declaring '~a" var))
                       (car maybe-default)))
    
    ;; 特殊处理关键字 super
    (if (eq? var 'super)
        'super  ;; 直接返回 'super 符号，不进行查找
        ;; 首先尝试查找对象字段（如果是在方法中）
        (let ((this-obj (get-and-check-this state)))
          (if (and this-obj
                   (not (eq? var 'this))  ;; 不是在查找this本身
                   (member var (class-all-fields (objectC-class this-obj))))
              ;; 是一个字段，从对象中获取
              (get-field this-obj var)
              ;; 不是字段，按常规方式从环境中查找
              (base-state-lookup var state))))))

(define state-lookup-box
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       (define binding (assq var (operator state)))
       (if binding
           (operands binding)
           (state-lookup-box var (operands state)))])))

(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (if (assq var (operator  state)) #t
              (state-lookup-for-assignment var (operands state)))])))

(define state-update
  (lambda (var val state)
    (define (find-var-binding layers)
      (if (null? layers)
          (error "Error: using before declaring" var)
          (let ()
            (define binding (assq var (operator layers)))
            (if binding
                (cons binding layers)  ; Return binding and layer
                (find-var-binding (operands layers))))))
    
    (define result (find-var-binding state))
    (define binding (operator result))
    
    ;; Update binding and return state
    (set-box! (operands binding) val)
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expression Evaluation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define M_boolean_value
  (lambda (v)
    (cond
      [(boolean? v) v]
      [(number? v) (not (zero? v))]
      [(and (list? v) (not (null? v))) #t]  ; Non-empty lists are considered true
      [(null? v) #f]                       ; Empty lists are considered false
      [else (error "Cannot convert to boolean" v)])))

;; 全局变量，跟踪当前执行的方法
(define current-method #f)

;; 更新和获取当前方法
(define (get-current-method) current-method)
(define (set-current-method! method) (set! current-method method))

;; 尝试从调用堆栈中找出当前方法
(define (find-method-in-call-stack state)
  (cons 'method current-method))  ;; 简化实现，直接返回当前方法

;; 添加全局变量记录查找层次
(define current-super-class #f)

;; 添加辅助函数管理查找
(define (get-current-super) current-super-class)
(define (set-current-super! cls) (set! current-super-class cls))

;; 方法调用帮助函数
(define (call-method obj method-closure args state return break continue throw)
  ;; 保存当前方法
  (define old-current-method (get-current-method))
  (set-current-method! method-closure)
  
  ;; 调用方法
  (define result
    (call-function method-closure args state return break continue throw))
  
  ;; 恢复原来的当前方法
  (set-current-method! old-current-method)
  
  result)

(define base-M_value
  (lambda (expr state return break continue throw)
    (cond
      [(number? expr) expr]
      [(eq? expr 'true) #t]
      [(eq? expr 'false) #f]
      [(symbol? expr) (state-lookup expr state)]
      ;; If a function definition appears in an expression, signal an error.
      [(and (list? expr) (eq? (operator expr) 'function))
       (error "Function definitions may only appear as statements")]
      [(list? expr)
       (case (operator expr)
         [(!)
          (not (M_boolean_value (M_value (firstoperand expr) state return break continue throw)))]
         [(- +)
          (if (null? (drop-first-two expr))
              ((lambda (v)
                 (case (operator expr)
                   [(+) v]
                   [(-) (- v)]))
               (M_value (firstoperand expr) state return break continue throw))
              ((lambda (v1 v2)
                 (case (operator expr)
                   [(+) (+ v1 v2)]
                   [(-) (- v1 v2)]))
               (M_value (firstoperand expr) state return break continue throw)
               (M_value (secondoperand expr) state return break continue throw)))]
         [(* / %)
          ((lambda (op v1 v2)
             (case op
               [(*) (* v1 v2)]
               [(/) (if (zero? v2)
                        (error "Division by zero")
                        (quotient v1 v2))]
               [(%) (if (zero? v2)
                        (error "Modulo by zero")
                        (modulo v1 v2))]))
           (operator expr)
           (M_value (firstoperand expr) state return break continue throw)
           (M_value (secondoperand expr) state return break continue throw))]
         [(== != < > <= >= || &&)
          (let ((v1 (M_value (firstoperand expr) state return break continue throw))
                (v2 (M_value (secondoperand expr) state return break continue throw)))
            (case (operator expr)
              [(==) (equal? v1 v2)]
              [(!=) (not (equal? v1 v2))]
              [(<) (< v1 v2)]
              [(>) (> v1 v2)]
              [(<=) (<= v1 v2)]
              [(>=) (>= v1 v2)]
              [(||) (or (M_boolean_value v1) (M_boolean_value v2))]
              [(&&) (and (M_boolean_value v1) (M_boolean_value v2))]))]
         [(funcall)
          (let ([f (M_value (firstoperand expr) state return break continue throw)])
            (unless (closure? f)
              (error "Not a function" (firstoperand expr)))
            (printf "调用函数: ~a\n" (closure-fname f))
            
            ;; 如果是点表达式调用的方法，使用 call-method
            (if (and (pair? (firstoperand expr)) 
                     (eq? (car (firstoperand expr)) 'dot))
                (let ([obj (M_value (cadr (firstoperand expr)) state return break continue throw)])
                  (if (objectC? obj)
                      (call-method obj f (operands (operands expr)) state return break continue throw)
                      (call-function f (operands (operands expr)) state return break continue throw)))
                ;; 否则使用普通函数调用
                (call-function f (operands (operands expr)) state return break continue throw)))]
         [else (error "Unknown operator in M_value:" (operator expr))])]
      [else (error "Invalid expression" expr)])))

(define M_value
  (lambda (expr state return break continue throw)
    (cond
      ;; NEW 处理
      [(and (pair? expr) (eq? (car expr) 'new))
       (eval-new (cadr expr) state)]
      
      ;; DOT 处理
      [(and (pair? expr) (eq? (car expr) 'dot))
       (let ([obj-expr (cadr expr)]
             [id (caddr expr)])
         (cond
           ;; 处理 super 关键字
           [(eq? obj-expr 'super)
            (let ([this-obj (state-lookup 'this state)])
              (unless (objectC? this-obj)
                (error 'dot "super used outside of method"))
              
              ;; 确定当前应该查找的父类
              (let ([current-class 
                     (or (get-current-super)
                         (classC-name (objectC-class this-obj)))])
                
                (let ([parent-class 
                       (classC-parent (get-class current-class))])
                  
                  (unless parent-class
                    (error 'dot "class has no parent"))
                  
                  (printf "super: 在类 ~a 的父类 ~a 中查找方法 ~a\n" 
                          current-class
                          parent-class
                          id)
                  
                  ;; 设置下一次 super 调用时的父类
                  (set-current-super! parent-class)
                  
                  ;; 获取父类的方法定义
                  (let* ([parent-C (get-class parent-class)]
                         [method (lookup-method parent-C id)]
                         [old-super (get-current-super)]
                         [env (if (null? (closure-env method))
                                  (make-state)
                                  (closure-env method))]
                         [result (make-closure 
                                  (closure-params method)
                                  (closure-body method)
                                  (state-declare 'this this-obj env)
                                  (closure-fname method)
                                  parent-class)])
                    
                    ;; 恢复原来的 super 类
                    (set-current-super! old-super)
                    
                    result))))]
           
           ;; 常规对象处理
           [else
            (let ([obj (M_value obj-expr state return break continue throw)])
              (unless (objectC? obj) (error 'dot "lhs is not an object"))
              (cond
                ;; 修改: 使用 lookup-method 在整个继承链上查找方法
                [(let ([method (with-handlers ([exn:fail? (lambda (e) #f)])
                                 (lookup-method (objectC-class obj) id))])
                   (and method
                        (let ([env (if (null? (closure-env method))
                                       (make-state)
                                       (closure-env method))])
                          (make-closure (closure-params method)
                                       (closure-body method)
                                       (state-declare 'this obj env)
                                       (closure-fname method)
                                       (classC-name (objectC-class obj))))))]
                ;; 如果在方法表中找不到，则尝试作为字段
                [else (get-field obj id)]))]))]
      
      ;; 默认情况调用基础函数
      [else (base-M_value expr state return break continue throw)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function Call Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-params
  (lambda (env params args caller-state return break continue throw)
    (cond
      ;; basic case: parameter list is empty
      [(and (null? params) (null? args)) env]
      [(null? params) 
       (if (null? args)
           env
           (error "Arity mismatch in function call: too many arguments"))]
      [(null? args) 
       (error "Arity mismatch in function call: missing arguments")]
      
      ;; recursive case: bind current parameter and continue
      [else
       (define param (operator params))
       (define arg (operator args))
       (define rest-params (operands params))
       (define rest-args (operands args))
       
       ;; handle reference parameter or normal parameter
       (if (and (list? param) (eq? (operator param) 'ref))
           (if (symbol? arg)
               (bind-params (state-declare (firstoperand param) 
                                        (state-lookup-box arg caller-state) 
                                        env)
                         rest-params 
                         rest-args 
                         caller-state 
                         return 
                         break 
                         continue 
                         throw)
               (error "Call-by-reference argument must be a variable:" arg))
           (bind-params (state-declare param 
                                    (M_value arg caller-state return break continue throw) 
                                    env)
                     rest-params 
                     rest-args 
                     caller-state 
                     return 
                     break 
                     continue 
                     throw))])))

;; 添加一个全局计数器和最大限制
(define call-depth 0)
(define max-call-depth 100)

(define call-function
  (lambda (closure args caller-state return break continue throw)
    (set! call-depth (+ call-depth 1))
    (when (> call-depth max-call-depth)
      (error "Maximum call depth exceeded - possible infinite recursion"))
    
    (define raw-params (closure-params closure))
    (define params (process-params raw-params))
    (define body (closure-body closure))
    (define def-env (closure-env closure))
    (define fname (closure-fname closure))
    
    ;; 确保 def-env 不为空
    (define actual-def-env (if (null? def-env) (make-state) def-env))
    
    ;; add function itself to environment to support recursion, then bind parameters
    (define fun-env-with-params 
      (bind-params 
       (if fname
           (state-declare fname closure actual-def-env)
           actual-def-env)
       params
       args
       caller-state
       return
       break
       continue
       throw))
    
    ;; 执行函数体并返回结果
    (define result 
      (call/cc 
       (lambda (ret)
         (M_state_list 
          body 
          fun-env-with-params 
          ret 
          (lambda (s) (break s))
          (lambda (s) (continue s))
          throw))))
    
    (set! call-depth (- call-depth 1))
    result))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Execution (M_state)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; M_state_list: evaluate a list of statements in a block. If none are given, return a default value (0).
(define M_state_list
  (lambda (stmts state return break continue throw)
    (cond
      [(null? stmts) state]
      [else
       ;; first lift all function definitions
       (define (hoist-functions stmt st)
         (if (and (list? stmt) 
                  (not (null? stmt)) 
                  (eq? (operator stmt) 'function))
             (let ()
               (define fname (firstoperand stmt))
               (define raw-params (secondoperand stmt))
               (define body (cadddr stmt))
               (state-declare fname 
                           (make-closure raw-params body st fname) 
                           st))
             st))
       
       (define hoisted-state (foldl hoist-functions state stmts))
       
       ;; then evaluate all statements normally
       (define (evaluate-statements remaining-stmts current-state)
         (if (null? (operands remaining-stmts))
             (M_state (operator remaining-stmts) current-state return break continue throw)
             (evaluate-statements (operands remaining-stmts)
                                 (M_state (operator remaining-stmts) 
                                          current-state 
                                          return 
                                          break 
                                          continue 
                                          throw))))
       
       (evaluate-statements stmts hoisted-state)])))

;; M_state_block: evaluate a block by pushing a new layer, evaluating the statements, then popping the layer.
(define M_state_block
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        state
        (let ((result (M_state_list stmts (push-layer state) return break continue throw)))
          (if (list? result)
              (pop-layer result)  ; if result is state, pop layer
              result)))))  ; if result is value, return directly

;; M_state: evaluate a single statement.
;; If stmt does not match any special form, treat it as an expression statement.
(define M_state
  (lambda (stmt state return break continue throw)
    (cond
      [(null? stmt) state]
      [(symbol? stmt) state]
      [(list? stmt)
       (case (operator stmt)
         [(begin)
          (M_state_block (operands stmt) state return break continue throw)]
         [(function)
          ;; Function definitions are processed as statements.
          (define fname (firstoperand stmt))
          (define raw-params (secondoperand stmt))
          (define body (cadddr stmt))
          (define closure (make-closure raw-params body state fname))
          (state-declare fname closure state)]
         [(var)
          (if (null? (drop-first-two stmt))
              (state-declare (firstoperand stmt) 'uninitialized state)
              (state-declare (firstoperand stmt)
                           (M_value (secondoperand stmt) state return break continue throw)
                           state))]
         [(=)
          (define lhs (firstoperand stmt))
          (define rhs (M_value (secondoperand stmt) state return break continue throw))
          (cond
            ;; 变量赋值
            [(symbol? lhs) 
             (state-update lhs rhs state)]
            
            ;; 对象字段赋值
            [(and (list? lhs) (eq? (operator lhs) 'dot))
             (define obj (M_value (firstoperand lhs) state return break continue throw))
             (define field (secondoperand lhs))
             (unless (objectC? obj) 
               (error "Left side of field assignment is not an object"))
             (set-field! obj field rhs)
             state]
            
            ;; 其他情况
            [else (error "Left side of assignment must be a variable or field")])]
         [(return)
          (return (M_value (firstoperand stmt) state return break continue throw))]
         [(if)
          (define condition-result (M_boolean_value (M_value (firstoperand stmt) state return break continue throw)))
          (define then-branch (secondoperand stmt))
          (define else-branch (if (> (length stmt) 3) (cadddr stmt) #f))
          
          (cond
            [condition-result
             (if (list? then-branch)
                 (M_state then-branch state return break continue throw)
                 (M_state_block (list then-branch) state return break continue throw))]
            [else-branch
             (if (list? else-branch)
                 (M_state else-branch state return break continue throw)
                 (M_state_block (list else-branch) state return break continue throw))]
            [else state])]
         [(while)
          (call/cc
           (lambda (break-k)
             (define (loop st iter-count)
               (cond
                 [(> iter-count 100000)  
                  (error "Maximum iteration count (100,000) exceeded. Possible infinite loop detected.")]
                 [(M_boolean_value (M_value (firstoperand stmt) st return break-k continue throw))
                  (call/cc
                   (lambda (continue-k)
                     (define body-state (M_state (secondoperand stmt) 
                                              st 
                                              return 
                                              break-k 
                                              continue-k 
                                              throw))
                     (loop (merge-top-bindings body-state st) (add1 iter-count))))]
                 [else st]))
             (loop state 0)))]
         [(break) (break state)]
         [(continue) (continue state)]
         [(throw)
          (throw (M_value (firstoperand stmt) state return break continue throw) state)]
         [(try)
          (M_state_try stmt state return break continue throw)]
         [else
          ;; Fallback: treat stmt as an expression statement.
          (begin (M_value stmt state return break continue throw)
                 state)])]
      [else (error "Invalid statement" stmt)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try-Catch-Finally Handling
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-clause
  (lambda (type clauses)
    (cond
      [(null? clauses) #f]
      [(and (list? (operator  clauses)) 
            (not (null? (operator  clauses)))
            (eq? (operator (operator  clauses)) type))
       (operator  clauses)]
      [else (find-clause type (operands clauses))])))

(define process-catch
  (lambda (catch-clause exception-val exception-state return break continue throw)
    (define catch-var (if (>= (length catch-clause) 3)
                        (firstoperand catch-clause)
                        'e))
    (define catch-body (if (>= (length catch-clause) 3)
                         (secondoperand catch-clause)
                         (firstoperand catch-clause)))
    (define catch-env (push-layer exception-state))
    (define catch-env-with-e (state-declare 'e exception-val catch-env))
    ;; If variable name is not 'e', declare the specified variable
    (define catch-env-final (if (eq? catch-var 'e)
                              catch-env-with-e
                              (state-declare catch-var exception-val catch-env-with-e)))
    ;; Execute catch block
    (M_state_block catch-body catch-env-final return break continue throw)))

(define process-finally
  (lambda (finally-clause state return break continue throw)
    (if finally-clause
        (let ()
          (define finally-body (firstoperand finally-clause))
          (define finally-env (push-layer state))
          (M_state_block finally-body finally-env return break continue throw))
        state)))

(define M_state_try
  (lambda (stmt state return break continue throw)
    (define try-body (firstoperand stmt))
    (define catch-clause (secondoperand stmt))
    (define finally-clause (cadddr stmt))
    
    (define (execute-finally env)
      (if (and (list? finally-clause) (not (null? finally-clause)))
          (M_state_block (firstoperand finally-clause) (push-layer env) return break continue throw)
          env))
    
    (define (execute-catch exception-val exception-state)
      (if (and (list? catch-clause) (not (null? catch-clause)))
          (let ()
            (define var-list (firstoperand catch-clause))
            (define catch-var (operator var-list))
            (define catch-body (secondoperand catch-clause))
            (define catch-env (push-layer exception-state))
            (define catch-state (state-declare catch-var exception-val catch-env))
            (execute-finally (M_state_block catch-body catch-state return break continue throw)))
          (throw exception-val exception-state)))
    
    (define (handle-try-result try-result)
      (cond
        ;; Handle exception
        [(and (pair? try-result) (eq? (operator try-result) 'exception))
         (define exception-val (firstoperand try-result))
         (define exception-state (drop-first-two try-result))
         (if (and (list? catch-clause) (not (null? catch-clause)))
             (execute-catch exception-val exception-state)
             (if (and (list? finally-clause) (not (null? finally-clause)))
                 (begin
                   (execute-finally exception-state)
                   (throw exception-val exception-state))
                 (throw exception-val exception-state)))]
        
        ;; Handle return
        [(and (pair? try-result) (eq? (operator try-result) 'return))
         (define return-val (operands try-result))
         (execute-finally state)
         (return return-val)]
        
        ;; Handle break
        [(and (pair? try-result) (eq? (operator try-result) 'break))
         (define break-state (operands try-result))
         (execute-finally break-state)
         (break break-state)]
        
        ;; Handle continue
        [(and (pair? try-result) (eq? (operator try-result) 'continue))
         (define continue-state (operands try-result))
         (execute-finally continue-state)
         (continue continue-state)]
        
        ;; Normal completion of try block
        [else (execute-finally try-result)]))
    
    ;; Execute try block and handle results
    (handle-try-result
     (call/cc 
      (lambda (throw-k)
        (M_state_block
         try-body
         state
         (lambda (v) (throw-k (cons 'return v)))
         (lambda (st) (throw-k (cons 'break st)))
         (lambda (st) (throw-k (cons 'continue st)))
         (lambda (val st) (throw-k (cons 'exception (cons val state))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Merging States / Layers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define merge-top-bindings
  (lambda (from-state to-state)
    (if (or (null? from-state) (null? to-state))
        to-state
        (cons (merge-layers (operator from-state) (operator to-state))
              (operands to-state)))))

(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       (define (add-binding binding result)
         (define var (operator binding))
         (if (assq var result)
             (cons binding (remove (assq var result) result))
             (cons binding result)))
       (foldr add-binding layer2 layer1)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section A  —  New data structures for classes & objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct classC  (name parent                    ; symbol  parent-class or #f
                      field-names field-inits        ; (list symbol) (list thunk)
                      methods                    ; (alist name . closure)
                      field-map)                 ; 添加字段映射
  #:transparent)

(struct objectC (class fields)                  ; classC   vector-of-values
  #:transparent)

;; global registry  <symbol,classC>
(define class-table (make-hash))

(define (get-class sym)
  (hash-ref class-table sym
            (λ () (error 'class "undefined class ~a" sym))))

;; helpers ----------------------------------------------------------

(define (class-all-fields C)
  (let loop ([cls C] [result '()])
    (if cls
        (loop (and (classC-parent cls) (get-class (classC-parent cls)))
              (append (classC-field-names cls) result))
        result)))

(define (lookup-method C m)
  (cond [(assoc m (classC-methods C))    => cdr]
        [(classC-parent C) (lookup-method (get-class (classC-parent C)) m)]
        [else (error 'dot "method ~a not found in ~a (or supers)"
                     m (classC-name C))]))

(define (field-index C fname)
  (let loop ([cls C] [offset 0])
    (define names (classC-field-names cls))
    (define pos   (index-of names fname))
    (if pos (+ offset pos)
        (if (classC-parent cls)
            (loop (get-class (classC-parent cls))
                  (+ offset (length names)))
            (error 'dot "field ~a undefined in class ~a"
                   fname (classC-name C))))))

(define (get-field obj fname)
  (let* ([cls (objectC-class obj)]
         [field-map (classC-field-map cls)]
         [pos (assoc fname field-map)])
    (if pos
        (vector-ref (objectC-fields obj) (cdr pos))
        (error 'dot "field ~a undefined in class ~a"
               fname (classC-name cls)))))

(define (set-field! obj fname v)
  (let* ([cls (objectC-class obj)]
         [field-map (classC-field-map cls)]
         [pos (assoc fname field-map)])
    (if pos
        (vector-set! (objectC-fields obj) (cdr pos) v)
        (error 'dot "field ~a undefined in class ~a"
               fname (classC-name cls)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section B  —  Building class closures from parse trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (build-class tree)
  (match tree
    [(list 'class name maybe-super body-container ...)
     (define parent (and (pair? maybe-super) (cadr maybe-super)))
     (define fields       '())
     (define field-inits  '())
     (define methods      '())

     ;; 解包嵌套的 body
     (define body (if (and (= (length body-container) 1) 
                           (list? (car body-container)))
                      (car body-container)
                      body-container))
     
     (printf "处理类主体: ~a\n" body)

     (for ([stmt body])
       (printf "处理类成员: ~a\n" stmt)
       (match stmt
         [(list 'var id init ...)
          (printf "添加字段: ~a\n" id)
          (set! fields (append fields (list id)))
          (set! field-inits
                (append field-inits
                        (list (λ (st) (if (null? init)
                                          0
                                          (M_value (car init) st
                                                   (λ (_) 0) void void
                                                   (λ _ (error "init"))))))))]
         [(list 'function fname params fbody)
          (printf "添加实例方法: ~a\n" fname)
          (set! methods
                (cons (cons fname
                            (make-closure params fbody '() fname name))
                      methods))]
         [(list 'static-function fname params fbody)
          (printf "添加静态方法: ~a\n" fname)
          (set! methods
                (cons (cons fname
                            (make-closure params fbody '() fname name))
                      methods))]
         [else (printf "未匹配的类成员: ~a\n" stmt)]))
     
     (printf "构建的类 ~a 方法: ~a\n" name methods)
     
     ;; 创建字段映射表
     (define field-map
       (let ([result '()])
         ;; 在一个顶层let表达式中处理所有计算
         (let ([current-offset 0])
           ;; 首先添加当前类的字段
           (for ([f fields]
                 [i (in-range (length fields))])
             (set! result (cons (cons f i) result)))
           
           ;; 如果有父类，添加父类的字段映射
           (when parent
             (let ([parent-class (get-class parent)])
               (set! result 
                     (append result
                             (map (lambda (p) 
                                    (cons (car p) 
                                          (+ (cdr p) (length fields))))
                                  (classC-field-map parent-class))))))
           ;; 最后返回结果
           result)))
     
     (classC name parent fields field-inits methods field-map)]))

(define (install-classes prog)
  (for ([clsdef prog])
    (hash-set! class-table
               (cadr clsdef)   ; class name
               (build-class clsdef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section C  —  Extend the evaluator (new / dot)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 1.  'new'   -------------------------------------------------------
(define (eval-new class-name state)
  (define C (get-class class-name))
  
  ;; 先定义函数
  (define (gather-all-fields cls)
    (if (classC-parent cls)
        (append (gather-all-fields (get-class (classC-parent cls)))
                (map cons 
                     (classC-field-names cls)
                     (classC-field-inits cls)))
        (map cons 
             (classC-field-names cls)
             (classC-field-inits cls))))
  
  ;; 然后使用函数
  (define all-fields (gather-all-fields C))
  
  ;; 初始化所有字段
  (define field-values
    (map (lambda (field-pair)
           (let ((init-thunk (cdr field-pair)))
             (init-thunk state)))
         all-fields))
  
  ;; 创建对象
  (objectC C (list->vector field-values)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section D  —  Interpreter entry-points
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Original single-argument behaviour kept for old tests.
(define (interpret file . maybe-class)
  (if (null? maybe-class)
      ;; ---------- old Part-3 path ----------
      (let* ([prog         (parser file)]
             [global-state (make-state)])
        (call/cc
         (λ (ret)
           (define final-state
             (M_state_list prog global-state ret
                           (λ (_) (error "break outside"))
                           (λ (_) (error "continue outside"))
                           (λ (v _) (error "uncaught" v))))
           (define main (state-lookup 'main final-state))
           (unless (closure? main)
             (error 'interpret "no main()"))
           (call-function main '() final-state ret
                          (λ (_) (error "break outside"))
                          (λ (_) (error "continue outside"))
                          (λ (v _) (error "uncaught" v))))))

      ;; ---------- Part-4 class path ----------
      (let* ([classname (string->symbol (car maybe-class))]
             [prog      (parser file)])
        (printf "解析的程序: ~a\n" prog)
        (install-classes prog)
        (define C (get-class classname))
        (printf "类的方法: ~a\n" (classC-methods C))
        (define main (lookup-method C 'main))
        (unless (closure? main)
          (error 'interpret "Class ~a has no static main()" classname))
        (call/cc
         (λ (ret)
           (call-function main '() (make-state) ret
                          (λ (_) (error "break outside"))
                          (λ (_) (error "continue outside"))
                          (λ (v _) (error "uncaught" v))))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-all
  (lambda ()
    (for-each
     (lambda (filename)
       (printf "~a\n" filename)
       (with-handlers ([exn:fail?
                        (lambda (e)
                          (printf "ERROR: ~a\n" (exn-message e)))])
         (define result
           (call/cc
            (lambda (return)
              (define program (parser filename))
              (define global-state (make-state))
              ;; execute the whole program
              (define final-state (M_state_list program global-state return
                                              (lambda (s) (error "Error: break outside loop"))
                                              (lambda (s) (error "Error: continue outside loop"))
                                              (lambda (v s) (error "Error: uncaught exception" v))))
              ;; find and call main function
              (define main-closure (state-lookup 'main final-state))
              (if (closure? main-closure)
                  (call-function main-closure '() final-state return
                                (lambda (s) (error "Error: break outside loop"))
                                (lambda (s) (error "Error: continue outside loop"))
                                (lambda (v s) (error "Error: uncaught exception" v)))
                  (error "Error: no main function defined or main is not a function")))))
         (printf "Result: ~a\n"
                 (cond
                   [(eq? result #t) "true"]
                   [(eq? result #f) "false"]
                   [else result]))))
     '("test1.txt" "test2.txt" "test3.txt" "test4.txt" "test5.txt"
       "test6.txt" "test7.txt" "test8.txt" "test9.txt" "test10.txt"
       "test11.txt" "test12.txt" "test13.txt" "test14.txt" "test15.txt"
       "test16.txt" "test17.txt" "test18.txt" "test19.txt" "test20.txt"
       "2test1.txt" "2test2.txt" "2test3.txt" "2test4.txt" "2test5.txt"
       "2test6.txt" "2test7.txt" "2test8.txt" "2test9.txt" "2test10.txt"
       "2test11.txt" "2test12.txt" "2test13.txt" "2test14.txt" "2test15.txt"
       "2test16.txt" "2test17.txt" "2test18.txt" "2test19.txt"
       "3test1.txt" "3test2.txt" "3test3.txt" "3test4.txt" "3test5.txt"
       "3test6.txt" "3test7.txt" "3test8.txt" "3test9.txt" "3test10.txt"
       "3test11.txt" "3test12.txt" "3test13.txt" "3test14.txt" "3test15.txt"
       "3test16.txt" "3test17.txt" "3test18.txt" "3test19.txt" "3test20.txt"
       "4test1.txt" "4test2.txt" "4test3.txt" "4test4.txt" "4test5.txt"
       "4test6.txt" "4test7.txt" "4test8.txt" "4test9.txt" "4test10.txt"
       "4test11.txt" "4test12.txt" "4test13.txt"))))

(define interpret-simple
  (lambda (filename)
    (call/cc
     (lambda (return)
       (let* ((program (parser filename))
              (global-state (make-state))
              ;; Evaluate all global declarations (functions and vars)
              (final-state (M_state_list program
                                         global-state
                                         return
                                         (lambda (s) (error "Error: break outside loop"))
                                         (lambda (s) (error "Error: continue outside loop"))
                                         (lambda (v s) (error "Error: uncaught exception" v)))))
         ;; Call main with no arguments
         (let ((main-closure (state-lookup 'main final-state)))
           (if (closure? main-closure)
               (call-function main-closure
                              '()
                              final-state
                              return
                              (lambda (s) (error "Error: break outside loop"))
                              (lambda (s) (error "Error: continue outside loop"))
                              (lambda (v s) (error "Error: uncaught exception" v)))
               (error "Error: no main function defined or main is not a function"))))))))


;; run all tests
;;(test-all)

;;(interpret "4test1.j" "A")
;;(interpret "4test2.j" "A")
;;(interpret "4test3.j" "A")
;;(interpret "4test4.j" "A")
;;(interpret "4test5.j" "A")
;;(interpret "4test6.j" "A")
(interpret "4test7.j" "C")
;;(interpret "4test8.j" "Square")
;;(interpret "4test9.j" "Square")
;;(interpret "4test10.j" "List")
;;(interpret "4test11.j" "List")
;;(interpret "4test12.j" "List")
;;(interpret "4test13.j" "C")


;; or run specific test (uncomment to test specific file)
;;(interpret "3test19.txt")  ;; test 19-exception handling
;;(interpret "3test20.txt")  ;; test 20-nested exception handling
;;(interpret "3test16.txt")  ;; test 16-function nested function nested function
