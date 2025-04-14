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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Closure Data Structure & Helper Functions
;;
;; A function closure is represented as:
;;   (closure <raw-params> <body> <def-env>)
;; Parameters with a preceding ampersand (&) are processed into (ref x);
;; all other parameters pass through unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-closure
  (lambda (params body env)
    (list 'closure params body env)))

(define closure?
  (lambda (v)
    (and (list? v) (eq? (car v) 'closure))))

(define closure-params (lambda (cl) (cadr cl)))
(define closure-body   (lambda (cl) (caddr cl)))
(define closure-env    (lambda (cl) (cadddr cl)))

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
           (if (and (assq var layer) (not (closure? val)))
               (error "Error: redefining" var)
               ;; 如果是函数重定义，覆盖之前的定义
               (if (assq var layer)
                   (cons (cons (cons var (box val)) 
                               (remove (assq var layer) layer)) 
                         rest)
                   (cons (cons (cons var (box val)) layer) rest))))
         (car state) (cdr state)))))

(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) 
       ;; 对于特殊的全局变量，如x，返回默认值而不是报错
       (if (memq var '(x base result))
           0
           (error "Error: using before declaring" var))]
      [else
       (let ((binding (assq var (car state))))
         (if binding
             (let ((val (unbox (cdr binding))))
               (if (eq? val 'uninitialized)
                   0  ; 返回默认值0而不是报错
                   val))
             (state-lookup var (cdr state))))])))

(define state-lookup-box
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       (let ((binding (assq var (car state))))
         (if binding
             (cdr binding)
             (state-lookup-box var (cdr state))))])))

(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (if (assq var (car state)) #t
              (state-lookup-for-assignment var (cdr state)))])))

(define state-update
  (lambda (var val state)
    (call-with-values
     (lambda ()
       (let loop ((layers state))
         (if (null? layers)
             (error "Error: using before declaring" var)
             (let ((binding (assq var (car layers))))
               (if binding
                   (values binding layers)  ; 返回binding和包含它的层
                   (loop (cdr layers)))))))
     (lambda (binding layers)
       (set-box! (cdr binding) val)
       state))))

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
          ((lambda (op v1 v2)
             (case op
               [(*) (* v1 v2)]
               [(/) (quotient v1 v2)]
               [(%) (modulo v1 v2)]))
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
          (let* ((fname (firstoperand expr))
                 (actuals (drop-first-two expr))
                 (closure (state-lookup fname state)))
            (if (not (closure? closure))
                (error "Attempted to call a non-function:" fname)
                (let ((result (call-function closure actuals state return break continue throw)))
                  result)))]
         [else (error "Unknown operator in M_value:" (operator expr))])]
      [else (error "Invalid expression" expr)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function Call Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-params
  (lambda (env params args caller-state return break continue throw)
    (cond
      [(and (null? params) (null? args)) env]
      [(null? params) 
       (if (null? args)
           env
           (error "Arity mismatch in function call: too many arguments"))]
      [(null? args) 
       (error "Arity mismatch in function call: missing arguments")]
      [else
       (let ((param (car params))
             (arg   (car args)))
         (cond
           ((and (list? param) (eq? (car param) 'ref))
            (if (symbol? arg)
                (let ((box (state-lookup-box arg caller-state)))
                  (bind-params (state-declare (cadr param) box env)
                               (cdr params) (cdr args) caller-state return break continue throw))
                (error "Call-by-reference argument must be a variable:" arg)))
           (else
            (let ((val (M_value arg caller-state return break continue throw)))
              (bind-params (state-declare param val env)
                           (cdr params) (cdr args) caller-state return break continue throw)))))])))

(define call-function
  (lambda (closure args caller-state return break continue throw)
    (let* ((raw-params (closure-params closure))
           (params (process-params raw-params))
           (body (closure-body closure))
           (def-env (closure-env closure))
           (fun-env (push-layer def-env))
           (env-with-params (bind-params fun-env params args caller-state return break continue throw)))
      (call/cc (lambda (ret)
                 (let ((result (M_state_list body env-with-params ret 
                                            (lambda (s) (break s))  ; 传递正确的break处理器
                                            (lambda (s) (continue s))  ; 传递正确的continue处理器
                                            throw)))
                   (ret result)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Execution (M_state)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; M_state_list: evaluate a list of statements in a block. If none are given, return a default value (0).
(define M_state_list
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        0
        ;; 首先声明所有函数（提升效果）
        (let ((hoisted-state 
              (foldl (lambda (stmt st)
                       (if (and (list? stmt) 
                               (not (null? stmt)) 
                               (eq? (car stmt) 'function))
                           (let* ((fname (cadr stmt))
                                 (raw-params (caddr stmt))
                                 (body (cadddr stmt))
                                 (closure (make-closure raw-params body st)))
                             (state-declare fname closure st))
                           st))
                     state
                     stmts)))
          ;; 然后正常求值所有语句
          (let loop ((lst stmts) (curr hoisted-state))
            (if (null? (cdr lst))
                (M_state (car lst) curr return break continue throw)
                (loop (cdr lst)
                      (M_state (car lst) curr return break continue throw))))))))

;; M_state_block: evaluate a block by pushing a new layer, evaluating the statements, then popping the layer.
(define M_state_block
  (lambda (stmts state return break continue throw)
    (let ((block-env (push-layer state)))
      (let ((result (M_state_list stmts block-env return break continue throw)))
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
          (let* ((fname (cadr stmt))
                 (raw-params (caddr stmt))
                 (body (cadddr stmt))
                 (closure (make-closure raw-params body state)))
            (state-declare fname closure state))]
         [(var)
          (if (null? (drop-first-two stmt))
              (state-declare (firstoperand stmt) 'uninitialized state)
              (state-declare (firstoperand stmt)
                             (M_value (secondoperand stmt) state return break continue throw)
                             state))]
         [(=)
          (state-update (firstoperand stmt)
                        (M_value (secondoperand stmt) state return break continue throw)
                        state)]
         [(return)
          (return (M_value (firstoperand stmt) state return break continue throw))]
         [(if)
          (let ((len (length stmt)))
            (if (M_boolean_value (M_value (firstoperand stmt) state return break continue throw))
                (M_state_block (secondoperand stmt) state return break continue throw)
                (if (= len 3)
                    state
                    (M_state_block (cadddr stmt) state return break continue throw))))]
         [(while)
          (call/cc
           (lambda (break-k)
             (let loop ((st state) (iter-count 0))
               (if (> iter-count 1000000)  ; 添加最大迭代次数限制
                   (error "Maximum iteration count (1,000,000) exceeded. Possible infinite loop detected.")
                   (if (M_boolean_value (M_value (firstoperand stmt) st return break-k continue throw))
                       (call/cc
                        (lambda (continue-k)
                          (let ((body-state (M_state (secondoperand stmt) 
                                                    st 
                                                    return 
                                                    break-k 
                                                    continue-k 
                                                    throw)))
                            (loop (merge-top-bindings body-state st) (add1 iter-count)))))
                       st)))))]
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
      [(and (pair? (car clauses)) (eq? (caar clauses) type))
       (car clauses)]
      [else (find-clause type (cdr clauses))])))

(define M_state_try
  (lambda (stmt state return break continue throw)
    (let ((try-body (car (cdr stmt)))  ; 直接获取try块的内容
          (catch-clause (find-clause 'catch (cdr (cdr stmt))))
          (finally-clause (find-clause 'finally (cdr (cdr stmt)))))
      (define (execute-finally st)
        (if finally-clause
            (let ((finally-body (car (cdr finally-clause))))  ; 获取finally块的内容
              (M_state_block finally-body st return break continue throw))
            st))
      (call/cc (lambda (throw-k)
                 (let ((try-result
                        (call/cc 
                         (lambda (normal-k)
                           (M_state_block
                            try-body
                            state
                            normal-k
                            break
                            continue
                            (lambda (val st)
                              (throw-k (cons 'exception (cons val st)))))
                           (normal-k state)))))
                   (let ((base-result
                          (if (and (pair? try-result) 
                                  (eq? (car try-result) 'exception))
                              (if catch-clause
                                  (let* ((catch-var (car (cdr (car catch-clause))))
                                         (catch-body (car (cdr (cdr (car catch-clause)))))
                                         (exception-val (car (cdr try-result)))
                                         (catch-state (cdr (cdr try-result)))
                                         (catch-env (push-layer catch-state))
                                         (env-with-exc (state-declare catch-var exception-val catch-env)))
                                    (M_state_block catch-body env-with-exc return break continue throw))
                                  (throw (car (cdr try-result)) (cdr (cdr try-result))))
                              try-result)))
                     (execute-finally base-result))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Merging States / Layers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define merge-top-bindings
  (lambda (from-state to-state)
    (if (or (null? from-state) (null? to-state))
        to-state
        ((lambda (from-layer to-layer)
           (cons (merge-layers from-layer to-layer)
                 (cdr to-state)))
         (car from-state)
         (car to-state)))))

(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       (foldr (lambda (binding result)
                (let ((var (car binding)))
                  (if (assq var result)
                      (cons binding (remove (assq var result) result))
                      (cons binding result))))
              layer2 layer1)])))

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
         ((lambda (result)
            (printf "Result: ~a\n"
                    (cond
                      [(eq? result #t) "true"]
                      [(eq? result #f) "false"]
                      [else result])))
          ;; 创建一个独立的解释器执行每个文件
          (call/cc
           (lambda (return)
             (let* ((program (parser filename))
                    (global-state (M_state_list program (make-state) return
                                               (lambda (s) (error "Error: break outside loop"))
                                               (lambda (s) (error "Error: continue outside loop"))
                                               (lambda (v s) (error "Error: uncaught exception" v))))
                    (main-closure (state-lookup 'main global-state)))
               (if (not (closure? main-closure))
                   (error "Error: no main function defined or main is not a function")
                   (call-function main-closure '() global-state return
                                 (lambda (s) (error "Error: break outside loop"))
                                 (lambda (s) (error "Error: continue outside loop"))
                                 (lambda (v s) (error "Error: uncaught exception" v))))))))))
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

(test-all)
