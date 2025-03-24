#lang racket

(require "simpleParser.rkt")

;; Group member: Tongwei Zhang, Xiang Luo, Percy Qian
;; ============================
;; State Management
;; ============================

;; Create a new state object - clearly representing layer structure
(define make-state
  (lambda ()
    (list '())))  ;; Initial state: single empty layer

;; Create a new scope layer
(define push-layer
  (lambda (state)
    (cons '() state)))

;; Remove the top scope layer
(define pop-layer
  (lambda (state)
    (cdr state)))

;; Declare variable in current layer
(define state-declare
  (lambda (var val state)
    (if (null? state)
        (error "Error: state is empty")
        (let ([layer (car state)]
              [rest (cdr state)])
          (cond
            [(assq var layer) (error "Error: redefining" var)]
            [else (cons (cons (cons var (box val)) layer) rest)])))))

;; Variable layer lookup - returns the layer and position where variable is found
(define state-lookup-layer
  (lambda (var state)
    (letrec ([search-layers 
              (lambda (var layers layer-idx)
                (if (null? layers)
                    (values #f #f)  ;; Not found
                    (let ([binding (assq var (car layers))])
                      (if binding
                          (values (car layers) layer-idx)  ;; Found variable layer
                          (search-layers var (cdr layers) (+ layer-idx 1))))))])
      (search-layers var state 0))))

;; State lookup interface 
(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (let ([binding (assq var (car state))])
              (if binding
                  (let ([val (unbox (cdr binding))])
                    (if (eq? val 'uninitialized)
                        (error "Error: using before assigning" var)
                        val))
                  ;; Variable not in top layer - continue searching deeper
                  (state-lookup var (cdr state))))])))

;; Lookup function for assignment - only checks if variable exists, not if initialized
(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (let ([binding (assq var (car state))])
              (if binding
                  #t  ;; Variable exists, return true
                  (state-lookup-for-assignment var (cdr state))))])))

;; State update interface
(define state-update
  (lambda (var val state)
    (let-values ([(layer layer-idx) (state-lookup-layer var state)])
      (if layer
          ;; Found variable layer - update its value
          (let ([binding (assq var layer)])
            (set-box! (cdr binding) val)
            state)
          ;; Variable not found - error handling
          (if (eq? var 'e) 
              ;; Special case for try-catch
              (state-declare var val state)
              (error "Error: using before declaring" var))))))

;; ============================
;; Expression Evaluation
;; ============================

(define M_value
  (lambda (expr state return break continue throw)
    (cond
      [(number? expr) expr]
      [(eq? expr 'true) #t]
      [(eq? expr 'false) #f]
      [(symbol? expr) (state-lookup expr state)]
      [(list? expr)
       (case (car expr)
         [(!) (not (M_boolean_value (M_value (cadr expr) state return break continue throw)))]
         [(- +) 
          ;; Check if unary minus/plus
          (if (null? (cddr expr))
              (let ([v (M_value (cadr expr) state return break continue throw)])
                (case (car expr)
                  [(+) v]
                  [(-) (- v)]))
              ;; Otherwise binary operator
              (let ([v1 (M_value (cadr expr) state return break continue throw)]
                    [v2 (M_value (caddr expr) state return break continue throw)])
                (case (car expr)
                  [(+) (+ v1 v2)]
                  [(-) (- v1 v2)])))]
         [(* / %)
          (let ([op (car expr)]
                [v1 (M_value (cadr expr) state return break continue throw)]
                [v2 (M_value (caddr expr) state return break continue throw)])
            (case op
              [(*) (* v1 v2)]
              [(/) (quotient v1 v2)]
              [(%) (modulo v1 v2)]))]
         [(== != < > <= >= || &&)
          (let ([op (car expr)]
                [v1 (M_value (cadr expr) state return break continue throw)]
                [v2 (M_value (caddr expr) state return break continue throw)])
            (case op
              [(==) (equal? v1 v2)]
              [(!=) (not (equal? v1 v2))]
              [(<) (< v1 v2)]
              [(>) (> v1 v2)]
              [(<=) (<= v1 v2)]
              [(>=) (>= v1 v2)]
              [(||) (or (M_boolean_value v1) (M_boolean_value v2))]
              [(&&) (and (M_boolean_value v1) (M_boolean_value v2))]))]
         [else (error "Unknown operator" (car expr))])]
      [else (error "Invalid expression" expr)])))

;; Convert to boolean value
(define M_boolean_value
  (lambda (v)
    (cond
      [(boolean? v) v]
      [(number? v) (not (zero? v))]
      [else (error "Cannot convert to boolean" v)])))

;; ============================
;; Statement Execution
;; ============================

;; Execute statement list
(define M_state_list
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        state
        (M_state_list (cdr stmts)
                      (M_state (car stmts) state return break continue throw)
                      return break continue throw))))

;; Add a generic block execution function
(define M_state_block
  (lambda (body-stmts state return break continue throw)
    ;; Create new scope layer
    (let ([block-state (push-layer state)])
      ;; Execute statements in block and return after popping layer
      (pop-layer 
       (if (list? (car body-stmts)) 
           ;; Process list of statements
           (M_state_list body-stmts block-state return break continue throw)
           ;; Process single statement
           (M_state body-stmts block-state return break continue throw))))))

;; Main statement execution function with enhanced scope rules
(define M_state
  (lambda (stmt state return break continue throw)
    (cond
      [(null? stmt) state]
      [(eq? (car stmt) 'begin)
       ;; Begin block automatically creates new scope
       (M_state_block (cdr stmt) state return break continue throw)]
      [(list? stmt)
       (case (car stmt)
         [(var)
          (if (null? (cddr stmt))
              (state-declare (cadr stmt) 'uninitialized state)
              (state-declare (cadr stmt) (M_value (caddr stmt) state return break continue throw) state))]
         [(=)
          (when (and (symbol? (cadr stmt)) (not (eq? (cadr stmt) 'e)))
            (state-lookup-for-assignment (cadr stmt) state))
          (state-update (cadr stmt) 
                        (M_value (caddr stmt) state return break continue throw) 
                        state)]
         [(return)
          (return (M_value (cadr stmt) state return break continue throw))]
         [(if)
          (if (M_boolean_value (M_value (cadr stmt) state return break continue throw))
              ;; Use generic block function for if branch
              (M_state_block (caddr stmt) state return break continue throw)
              (if (null? (cdddr stmt))
                  state
                  ;; Use generic block function for else branch
                  (M_state_block (cadddr stmt) state return break continue throw)))]
         [(while)
          (M_state_while stmt state return break continue throw)]
         [(break)
          (break state)]
         [(continue)
          (continue state)]
         [(throw)
          (throw (M_value (cadr stmt) state return break continue throw) state)]
         [(try)
          (M_state_try stmt state return break continue throw)]
         [else (error "Unknown statement type" stmt)])]
      [else (error "Invalid statement" stmt)])))

;; Helper function: find try-catch-finally clause
(define find-clause
  (lambda (type clauses)
    (cond
      [(null? clauses) #f]
      [(and (pair? (car clauses)) (eq? (caar clauses) type)) (car clauses)]
      [else (find-clause type (cdr clauses))])))

;; Handle try-catch-finally statements
(define M_state_try
  (lambda (stmt state return break continue throw)
    (let ([try-body (cadr stmt)]
          [catch-clause (find-clause 'catch (cddr stmt))]
          [finally-clause (find-clause 'finally (cddr stmt))])
      
      ;; Helper function
      (define (execute-finally st)
        (if finally-clause
            (foldl (lambda (s st) (M_state s st return break continue throw))
                   st
                   (cadr finally-clause))
            st))
      
      ;; Simplified exception handling structure
      (let* ([try-result 
              (call/cc
               (lambda (throw-k)
                 ;; Use tags to distinguish normal execution and exceptions
                 (cons 'normal
                       (foldl (lambda (s st)
                                (M_state s st 
                                         ;; Maintain return continuation
                                         return 
                                         break continue
                                         (lambda (val st) 
                                           (throw-k (cons 'exception (cons val st))))))
                              state
                              try-body))))]
             
             ;; Process try block execution result
             [base-result 
              (if (eq? (car try-result) 'exception)
                  ;; Has exception - execute catch block
                  (if catch-clause
                      (let ([catch-var (car (cadr catch-clause))])
                        (pop-layer
                         (foldl (lambda (s st) 
                                  (M_state s st return break continue throw))
                                (state-declare catch-var 
                                              (cadr try-result) 
                                              (push-layer (cddr try-result)))
                                (caddr catch-clause))))
                      ;; No catch - call external throw
                      (throw (cadr try-result) (cddr try-result)))
                  ;; Normal execution - use try block result
                  (cdr try-result))])
        
        ;; Finally execute finally block
        (execute-finally base-result)))))

;; Loop statement - create new scope for each iteration
(define M_state_while
  (lambda (stmt state return break continue throw)
    (call/cc
     (lambda (break-k)
       (letrec ([loop (lambda (state)
                        (if (M_boolean_value (M_value (cadr stmt) state return break-k continue throw))
                            ;; Reduce nested let, use function composition
                            (loop (merge-top-bindings 
                                   (pop-layer
                                    (call/cc
                                     (lambda (continue-k)
                                       (M_state (caddr stmt)
                                               (push-layer state)
                                               return
                                               (lambda (s) (break-k (merge-top-bindings (pop-layer s) state)))
                                               (lambda (s) (continue-k (merge-top-bindings (pop-layer s) state)))
                                               throw))))
                                   state))
                            state))])
         (loop state))))))

;; Merge top layer bindings
(define merge-top-bindings
  (lambda (from-state to-state)
    (if (or (null? from-state) (null? to-state))
        to-state
        (let ([from-layer (car from-state)]
              [to-layer (car to-state)])
          (cons (merge-layers from-layer to-layer)
                (cdr to-state))))))

;; Merge two states, preserve variable values in current state but clean extra layers
(define merge-state
  (lambda (current-state original-state)
    (cond
      ;; Handle empty state cases
      [(null? current-state) original-state]
      [(null? original-state) current-state]
      ;; Normal case
      [else
       (let ([current-length (length current-state)]
             [original-length (length original-state)])
         (if (= current-length original-length)
             ;; Same length, merge top layer
             (cons (merge-layers (car current-state) (car original-state))
                   (cdr current-state))
             ;; Different lengths, recursive handling
             (if (> current-length original-length)
                 ;; Current state has more layers, preserve current but merge internal state
                 (cons (car current-state) 
                       (merge-state (cdr current-state) original-state))
                 ;; Original state has more layers, preserve original while merging
                 (cons (merge-layers (car current-state) (car original-state))
                       (merge-state (cdr current-state) (cdr original-state))))))])))

;; Merge variable bindings from two layers
(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       ;; Merge bindings from layer1 into layer2
       (foldr (lambda (binding result)
                (let ([var (car binding)])
                  (if (assq var result)
                      ;; Variable already exists in layer2, update with layer1's value
                      (cons binding (remove (assq var result) result))
                      ;; Variable doesn't exist, add to result
                      (cons binding result))))
              layer2
              layer1)])))

;; ============================
;; Interpreter Entry
;; ============================

(define interpret
  (lambda (filename)
    (call/cc
     (lambda (return)
       (let ([program (parser filename)])
         ;; Program is a list of statements, so we call M_state_list directly
         (M_state_list program 
                      (list '()) ; Initial empty state
                      return
                      (lambda (s) (error "Error: break outside loop"))
                      (lambda (s) (error "Error: continue outside loop"))
                      (lambda (v s) (error "Error: uncaught exception" v))))))))

;; ============================
;; Test Functions
;; ============================

;; Framework for testing all files
(define test-all
  (lambda ()
    (for-each
     (lambda (filename)
       (printf "~a\n" filename)
       (with-handlers ([exn:fail? (lambda (e)
                                   (printf "ERROR: ~a\n" (exn-message e)))])
         (let ([result (interpret filename)])
           ;; Convert boolean values to true/false
           (printf "Result: ~a\n" 
                   (cond
                     [(eq? result #t) "true"]
                     [(eq? result #f) "false"]
                     [else result])))))
     '("test1.txt" "test2.txt" "test3.txt" "test4.txt" "test5.txt"
       "test6.txt" "test7.txt" "test8.txt" "test9.txt" "test10.txt"
       "test11.txt" "test12.txt" "test13.txt" "test14.txt" "test15.txt"
       "test16.txt" "test17.txt" "test18.txt" "test19.txt" "test20.txt"
       "2test1.txt" "2test2.txt" "2test3.txt" "2test4.txt" "2test5.txt"
       "2test6.txt" "2test7.txt" "2test8.txt" "2test9.txt" "2test10.txt"
       "2test11.txt" "2test12.txt" "2test13.txt" "2test14.txt" "2test15.txt"
       "2test16.txt" "2test17.txt" "2test18.txt" "2test19.txt" ))))

;; Special test function - test a single file and print detailed structure
(define test-single
  (lambda (filename)
    (printf "Testing file: ~a\n" filename)
    (let ([program (parser filename)])
      (printf "Parse result:\n~a\n" program)
      (with-handlers ([exn:fail? (lambda (e)
                                   (printf "Error message: ~a\n" (exn-message e)))])
        (let ([result (interpret filename)])
          (printf "Return result: ~a\n" result))))))

;; Run tests
(test-all)  ;; Run all tests
