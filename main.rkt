#lang racket

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; REQUIREMENTS
;; Use the new parser that supports nested functions, closures,
;; and call-by-reference (with extra processing).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require "functionParser.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operator Accessors for Lists
;;   operator      => car
;;   firstoperand  => cadr
;;   secondoperand => caddr
;;   drop-first-two=> cddr
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define operator car)
(define firstoperand cadr)
(define secondoperand caddr)
(define drop-first-two cddr)
(define operands cdr)
(define operand1 cadr)
(define operand2 caddr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Closure Data Structure & Helper Functions
;;
;; A function closure is represented as:
;;   (closure <raw-params> <body> <def-env> <fname>)
;; Parameters with a preceding ampersand (&) are processed into (ref x);
;; all other parameters pass through unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-closure
  (lambda (params body env fname)
    (list 'closure params body env fname)))

(define closure?
  (lambda (v)
    (and (list? v) (eq? (car v) 'closure))))

(define closure-params (lambda (cl) (cadr cl)))
(define closure-body   (lambda (cl) (caddr cl)))
(define closure-env    (lambda (cl) (cadddr cl)))
(define closure-fname  (lambda (cl) (if (< (length cl) 5) #f (list-ref cl 4))))

(define process-params
  (lambda (params)
    (define (proc lst)
      (cond
        [(null? lst) '()]
        [(and (symbol? (car lst)) (eq? (car lst) '&))
         (if (null? (cdr lst))
             (error 'process-params "Missing identifier after &")
             (cons (list 'ref (car (cdr lst))) (proc (cdr (cdr lst)))))]
        [else (cons (car lst) (proc (cdr lst)))]))
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
  (lambda (state) (cdr state)))

(define state-declare
  (lambda (var val state)
    (if (null? state)
        (error "Error: state is empty")
        ((lambda (layer rest)
           ;; 总是允许覆盖当前层中的变量定义
           ;; 这对于函数参数和嵌套函数非常重要
           (cons (cons (cons var (box val)) 
                      (if (assq var layer) 
                          (remove (assq var layer) layer)
                          layer))
                 rest))
         (car state) (cdr state)))))

(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) 
       (error "Error: using before declaring" var)]
      [else
       (define binding (assq var (car state)))
       (if binding
           (let ([val (unbox (cdr binding))])
             (if (eq? val 'uninitialized)
                 0  ; 返回默认值0而不是报错
                 val))
           (state-lookup var (cdr state)))])))

(define state-lookup-box
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       (define binding (assq var (car state)))
       (if binding
           (cdr binding)
           (state-lookup-box var (cdr state)))])))

(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (if (assq var (car state)) #t
              (state-lookup-for-assignment var (cdr state)))])))

(define state-update
  (lambda (var val state)
    (define (find-var-binding layers)
      (if (null? layers)
          (error "Error: using before declaring" var)
          (let ([binding (assq var (car layers))])
            (if binding
                (cons binding layers)  ; 返回绑定和层
                (find-var-binding (cdr layers))))))
    
    (define result (find-var-binding state))
    (define binding (car result))
    
    ;; 更新绑定并返回状态
    (set-box! (cdr binding) val)
    state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expression Evaluation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define M_boolean_value
  (lambda (v)
    (cond
      [(boolean? v) v]
      [(number? v) (not (zero? v))]
      [(and (list? v) (not (null? v))) #t]  ; 非空列表视为true
      [(null? v) #f]                       ; 空列表视为false
      [else (error "Cannot convert to boolean" v)])))

(define M_value
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
          (define op (operator expr))
          (define v1 (M_value (firstoperand expr) state return break continue throw))
          (define v2 (M_value (secondoperand expr) state return break continue throw))
          (case op
            [(*) (* v1 v2)]
            [(/) (if (zero? v2)
                     (error "Division by zero")
                     (quotient v1 v2))]
            [(%) (if (zero? v2)
                     (error "Modulo by zero")
                     (modulo v1 v2))])]
         [(== != < > <= >= || &&)
          (define v1 (M_value (firstoperand expr) state return break continue throw))
          (define v2 (M_value (secondoperand expr) state return break continue throw))
          (case (operator expr)
            [(==) (equal? v1 v2)]
            [(!=) (not (equal? v1 v2))]
            [(<) (< v1 v2)]
            [(>) (> v1 v2)]
            [(<=) (<= v1 v2)]
            [(>=) (>= v1 v2)]
            [(||) (or (M_boolean_value v1) (M_boolean_value v2))]
            [(&&) (and (M_boolean_value v1) (M_boolean_value v2))])]
         [(funcall)
          (define fname (firstoperand expr))
          (define actuals (drop-first-two expr))
          (define fval 
            (if (symbol? fname)
                (state-lookup fname state)
                (M_value fname state return break continue throw)))
          (if (not (closure? fval))
              (error "Attempted to call a non-function:" fname)
              (call-function fval actuals state return break continue throw))]
         [else (error "Unknown operator in M_value:" (operator expr))])]
      [else (error "Invalid expression" expr)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function Call Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-params
  (lambda (env params args caller-state return break continue throw)
    (cond
      ;; 基本情况：参数列表为空
      [(and (null? params) (null? args)) env]
      [(null? params) 
       (if (null? args)
           env
           (error "Arity mismatch in function call: too many arguments"))]
      [(null? args) 
       (error "Arity mismatch in function call: missing arguments")]
      
      ;; 递归情况：绑定当前参数并继续
      [else
       (define param (car params))
       (define arg (car args))
       (define rest-params (cdr params))
       (define rest-args (cdr args))
       
       (cond
         ;; 处理引用参数
         ((and (list? param) (eq? (car param) 'ref))
          (if (symbol? arg)
              (bind-params (state-declare (cadr param) 
                                        (state-lookup-box arg caller-state) 
                                        env)
                         rest-params 
                         rest-args 
                         caller-state 
                         return 
                         break 
                         continue 
                         throw)
              (error "Call-by-reference argument must be a variable:" arg)))
         
         ;; 处理普通参数
         (else
          (bind-params (state-declare param 
                                    (M_value arg caller-state return break continue throw) 
                                    env)
                     rest-params 
                     rest-args 
                     caller-state 
                     return 
                     break 
                     continue 
                     throw)))])))

(define call-function
  (lambda (closure args caller-state return break continue throw)
    (define raw-params (closure-params closure))
    (define params (process-params raw-params))
    (define body (closure-body closure))
    (define def-env (closure-env closure))
    (define fname (closure-fname closure))
    
    ;; 添加函数自身到环境以支持递归，然后绑定参数
    (define fun-env-with-params 
      (bind-params 
       (if fname
           (state-declare fname closure def-env)
           def-env)
       params
       args
       caller-state
       return
       break
       continue
       throw))
    
    ;; 执行函数体并返回结果
    (call/cc 
     (lambda (ret)
       (M_state_list 
        body 
        fun-env-with-params 
        ret 
        (lambda (s) (break s))
        (lambda (s) (continue s))
        throw)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Execution (M_state)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; M_state_list: evaluate a list of statements in a block. If none are given, return a default value (0).
(define M_state_list
  (lambda (stmts state return break continue throw)
    (cond
      [(null? stmts) state]
      [else
       ;; 首先提升所有函数定义
       (define hoisted-state 
         (foldl 
          (lambda (stmt st)
            (if (and (list? stmt) 
                     (not (null? stmt)) 
                     (eq? (car stmt) 'function))
                (let ((fname (cadr stmt))
                      (raw-params (caddr stmt))
                      (body (cadddr stmt)))
                  (state-declare fname 
                               (make-closure raw-params body st fname) 
                               st))
                st))
          state
          stmts))
       
       ;; 然后正常求值所有语句
       (define (evaluate-statements remaining-stmts current-state)
         (if (null? (cdr remaining-stmts))
             (M_state (car remaining-stmts) current-state return break continue throw)
             (evaluate-statements (cdr remaining-stmts)
                                 (M_state (car remaining-stmts) 
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
              (pop-layer result)  ; 如果结果是状态，弹出层
              result)))))  ; 如果结果是值，直接返回

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
          (M_state_block (cdr stmt) state return break continue throw)]
         [(function)
          ;; Function definitions are processed as statements.
          (define fname (cadr stmt))
          (define raw-params (caddr stmt))
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
          (define var (firstoperand stmt))
          (define val (M_value (secondoperand stmt) state return break continue throw))
          (if (not (symbol? var))
              (error "Left side of assignment must be a variable")
              (state-update var val state))]
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
             (letrec ((loop (lambda (st iter-count)
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
                                [else st]))))
               (loop state 0))))]
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
      [(and (list? (car clauses)) 
            (not (null? (car clauses)))
            (eq? (operator (car clauses)) type))
       (car clauses)]
      [else (find-clause type (cdr clauses))])))

(define process-catch
  (lambda (catch-clause exception-val exception-state return break continue throw)
    (let* ((catch-var (if (>= (length catch-clause) 3)
                         (cadr catch-clause)
                         'e))
           (catch-body (if (>= (length catch-clause) 3)
                          (caddr catch-clause)
                          (cadr catch-clause)))
           (catch-env (push-layer exception-state))
           ;; 先在环境中声明变量e
           (catch-env-with-e (state-declare 'e exception-val catch-env))
           ;; 如果变量名不是e，再声明指定的变量
           (catch-env-final (if (eq? catch-var 'e)
                               catch-env-with-e
                               (state-declare catch-var exception-val catch-env-with-e))))
      ;; 执行catch块
      (M_state_block catch-body catch-env-final return break continue throw))))

(define process-finally
  (lambda (finally-clause state return break continue throw)
    (if finally-clause
        (let* ((finally-body (cadr finally-clause))
               (finally-env (push-layer state)))
          (M_state_block finally-body finally-env return break continue throw))
        state)))

(define M_state_try
  (lambda (stmt state return break continue throw)
    (define try-body (cadr stmt))
    (define catch-clause (caddr stmt))
    (define finally-clause (cadddr stmt))
    
    (define (execute-finally env)
      (if (and (list? finally-clause) (not (null? finally-clause)))
          (M_state_block (cadr finally-clause) (push-layer env) return break continue throw)
          env))
    
    (define (execute-catch exception-val exception-state)
      (cond
        [(and (list? catch-clause) (not (null? catch-clause)))
         (let* ([var-list (cadr catch-clause)]
                [catch-var (car var-list)]
                [catch-body (caddr catch-clause)]
                [catch-env (push-layer exception-state)]
                [catch-state (state-declare catch-var exception-val catch-env)])
           (execute-finally (M_state_block catch-body catch-state return break continue throw)))]
        [else (throw exception-val exception-state)]))
    
    (define (handle-try-result try-result)
      (cond
        ;; 处理异常
        [(and (pair? try-result) (eq? (car try-result) 'exception))
         (let ([exception-val (cadr try-result)]
               [exception-state (cddr try-result)])
           (if (and (list? catch-clause) (not (null? catch-clause)))
               (execute-catch exception-val exception-state)
               (if (and (list? finally-clause) (not (null? finally-clause)))
                   (begin
                     (execute-finally exception-state)
                     (throw exception-val exception-state))
                   (throw exception-val exception-state))))]
        
        ;; 处理return
        [(and (pair? try-result) (eq? (car try-result) 'return))
         (let ([return-val (cdr try-result)])
           (execute-finally state)
           (return return-val))]
        
        ;; 处理break
        [(and (pair? try-result) (eq? (car try-result) 'break))
         (let ([break-state (cdr try-result)])
           (execute-finally break-state)
           (break break-state))]
        
        ;; 处理continue
        [(and (pair? try-result) (eq? (car try-result) 'continue))
         (let ([continue-state (cdr try-result)])
           (execute-finally continue-state)
           (continue continue-state))]
        
        ;; 正常执行完try块
        [else (execute-finally try-result)]))
    
    ;; 执行try块并处理结果
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
        (cons (merge-layers (car from-state) (car to-state))
              (cdr to-state)))))

(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       (define (add-binding binding result)
         (define var (car binding))
         (if (assq var result)
             (cons binding (remove (assq var result) result))
             (cons binding result)))
       (foldr add-binding layer2 layer1)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define test-all
  (lambda ()
    (define (run-test filename)
      (printf "~a\n" filename)
      (with-handlers ([exn:fail?
                        (lambda (e)
                          (printf "ERROR: ~a\n" (exn-message e)))])
        (define result 
          (call/cc
            (lambda (return)
              (define program (parser filename))
              (define global-state (make-state))
              ;; 执行整个程序
              (define final-state 
                (M_state_list program global-state return
                            (lambda (s) (error "Error: break outside loop"))
                            (lambda (s) (error "Error: continue outside loop"))
                            (lambda (v s) (error "Error: uncaught exception" v))))
              ;; 查找并调用main函数
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
    
    (for-each run-test 
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
                "3test16.txt" "3test17.txt" "3test18.txt" "3test19.txt" "3test20.txt"))))

(define test-specific
  (lambda (filename)
    (printf "Testing ~a\n" filename)
    (with-handlers ([exn:fail?
                    (lambda (e)
                      (printf "ERROR: ~a\n" (exn-message e)))])
      (define result
        (call/cc
         (lambda (return)
           (define program (parser filename))
           (define global-state (make-state))
           ;; 执行整个程序
           (define final-state 
             (M_state_list program global-state return
                          (lambda (s) (error "Error: break outside loop"))
                          (lambda (s) (error "Error: continue outside loop"))
                          (lambda (v s) (error "Error: uncaught exception" v))))
           ;; 查找并调用main函数
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
                [else result])))))

;; 运行所有测试
(test-all)

;; 或者运行特定测试（取消注释以测试特定文件）
;;(test-specific "3test19.txt")  ;; 测试19-异常处理
;;(test-specific "3test20.txt")  ;; 测试20-嵌套异常处理
;;(test-specific "3test16.txt")  ;; 测试16-函数嵌套函数嵌套函数
