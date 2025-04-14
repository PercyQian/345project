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
           (if (assq var layer)
               (error "Error: redefining" var)
               (cons (cons (cons var (box val)) layer) rest)))
         (car state) (cdr state)))))

(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       (let ((binding (assq var (car state))))
         (if binding
             (let ((val (unbox (cdr binding))))
               (if (eq? val 'uninitialized)
                   (error "Error: using before assigning" var)
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
                   binding
                   (loop (cdr layers)))))))
     (lambda (binding)
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
                (call-function closure actuals state return break continue throw)))]
         [else (error "Unknown operator in M_value:" (operator expr))])]
      [else (error "Invalid expression" expr)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function Call Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bind-params
  (lambda (env params args caller-state return break continue throw)
    (cond
      [(and (null? params) (null? args)) env]
      [(or (null? params) (null? args))
       (error "Arity mismatch in function call")]
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
                 (let ((result (M_state_list body env-with-params ret break continue throw)))
                   (ret result)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Execution (M_state)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; M_state_list: evaluate a list of statements in a block. If none are given, return a default value (0).
(define M_state_list
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        0
        (let loop ((lst stmts) (curr state))
          (if (null? (cdr lst))
              (M_state (car lst) curr return break continue throw)
              (loop (cdr lst)
                    (M_state (car lst) curr return break continue throw)))))))

;; M_state_block: evaluate a block by pushing a new layer, evaluating the statements, then popping the layer.
(define M_state_block
  (lambda (stmts state return break continue throw)
    (let ((block-env (push-layer state)))
      (let ((result (M_state_list stmts block-env return break continue throw)))
        (pop-layer block-env)  ; remove the extra layer
        result))))

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
             (define (loop st)
               (if (M_boolean_value (M_value (firstoperand stmt) st return break continue throw))
                   (let ((body-state (M_state (secondoperand stmt) st return break continue throw)))
                     (loop (merge-top-bindings body-state st)))
                   st))
             (loop state)))]
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
    ((lambda (try-body catch-clause finally-clause)
       (define (execute-finally st)
         (if finally-clause
             (foldl (lambda (s st)
                      (M_state s st return break continue throw))
                    st
                    (firstoperand finally-clause))
             st))
       (call/cc (lambda (throw-k)
                  (let ((try-result
                         (foldl (lambda (s st)
                                  (M_state s st return break continue
                                           (lambda (val st)
                                             (throw-k (list 'exception val st)))))
                                state
                                (firstoperand try-body))))
                    (let ((base-result
                           (if (eq? (operator try-result) 'exception)
                               (if catch-clause
                                   ((lambda (catch-var)
                                      (pop-layer
                                       (foldl (lambda (s st)
                                                (M_state s st return break continue throw))
                                              (state-declare catch-var
                                                             (firstoperand try-result)
                                                             (push-layer (drop-first-two try-result)))
                                              (secondoperand catch-clause))))
                                    (firstoperand (car catch-clause)))
                                   (throw (firstoperand try-result) (drop-first-two try-result)))
                               (cdr try-result))))
                      (execute-finally base-result))))))
     (firstoperand stmt)
     (find-clause 'catch (drop-first-two stmt))
     (find-clause 'finally (drop-first-two stmt)))))

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
;; Interpreter Entry
;;
;; After processing all top-level declarations, look up 'main in the global state,
;; then call main with an empty argument list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interpret
  (lambda (filename)
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
                            (lambda (v s) (error "Error: uncaught exception" v)))))))))

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
          (interpret filename))))
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
