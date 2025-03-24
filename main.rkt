;; Group member: Tongwei Zhang, Xiang Luo, Percy Qian


#lang racket

(require "simpleParser.rkt")

;; Operator accessors for lists:
;;  operator      => car
;;  firstoperand  => cadr
;;  secondoperand => caddr
;;  drop-first-two => cddr

(define operator car)
(define firstoperand cadr)
(define secondoperand caddr)
(define drop-first-two cddr)



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
        ((lambda (layer rest)
           (cond
             [(assq var layer) (error "Error: redefining" var)]
             [else (cons (cons (cons var (box val)) layer) rest)]))
         (operator state)
         (cdr state)))))

;; Variable layer lookup - returns the layer and position where variable is found
(define state-lookup-layer
  (lambda (var state)
    ;; Replace `letrec` with an internal definition
    (define (search-layers var layers layer-idx)
      (if (null? layers)
          (values #f #f)  ;; Not found
          ((lambda (binding)
             (if binding
                 (values (operator layers) layer-idx)  ;; Found variable layer
                 (search-layers var (cdr layers) (+ layer-idx 1))))
           (assq var (operator layers)))))
    (search-layers var state 0)))

;; State lookup interface 
(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       ((lambda (binding)
          (if binding
              ((lambda (val)
                 (if (eq? val 'uninitialized)
                     (error "Error: using before assigning" var)
                     val))
               (unbox (cdr binding)))
              ;; Variable not in top layer - continue searching deeper
              (state-lookup var (cdr state))))
        (assq var (operator state)))])))

;; Lookup function for assignment - only checks if variable exists, not if initialized
(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else
       ((lambda (binding)
          (if binding
              #t
              (state-lookup-for-assignment var (cdr state))))
        (assq var (operator state)))])))

;; State update interface
(define state-update
  (lambda (var val state)
    (call-with-values
     (lambda () (state-lookup-layer var state))
     (lambda (layer layer-idx)
       (if layer
           ;; Found variable layer - update its value
           ((lambda (binding)
              (set-box! (cdr binding) val)
              state)
            (assq var layer))
           ;; Variable not found - error handling
           (if (eq? var 'e)
               ;; Special case for try-catch
               (state-declare var val state)
               (error "Error: using before declaring" var)))))))

;; ============================
;; Expression Evaluation
;; ============================

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
      [(list? expr)
       (case (operator expr)
         [(!)
          (not (M_boolean_value (M_value (firstoperand expr) state return break continue throw)))]
         [(- +)
          ;; Check if unary minus/plus
          (if (null? (drop-first-two expr))
              ;; unary + or unary -
              ((lambda (v)
                 (case (operator expr)
                   [(+) v]
                   [(-) (- v)]))
               (M_value (firstoperand expr) state return break continue throw))
              ;; binary + or -
              ((lambda (v1 v2)
                 (case (operator expr)
                   [(+) (+ v1 v2)]
                   [(-) (- v1 v2)]))
               (M_value (firstoperand expr) state return break continue throw)
               (M_value (secondoperand  expr) state return break continue throw)))]
         [(* / %)
          ((lambda (op v1 v2)
             (case op
               [(*) (* v1 v2)]
               [(/) (quotient v1 v2)]
               [(%) (modulo v1 v2)]))
           (operator expr)
           (M_value (firstoperand expr) state return break continue throw)
           (M_value (secondoperand  expr) state return break continue throw))]
         [(== != < > <= >= || &&)
          ((lambda (op v1 v2)
             (case op
               [(==) (equal? v1 v2)]
               [(!=) (not (equal? v1 v2))]
               [(<) (< v1 v2)]
               [(>) (> v1 v2)]
               [(<=) (<= v1 v2)]
               [(>=) (>= v1 v2)]
               [(||) (or (M_boolean_value v1) (M_boolean_value v2))]
               [(&&) (and (M_boolean_value v1) (M_boolean_value v2))]))
           (operator expr)
           (M_value (firstoperand expr) state return break continue throw)
           (M_value (secondoperand  expr) state return break continue throw))]
         [else (error "Unknown operator" (operator expr))])]
      [else (error "Invalid expression" expr)])))

;; ============================
;; Statement Execution
;; ============================

;; Execute statement list
(define M_state_list
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        state
        (M_state_list (cdr stmts)
                      (M_state (operator stmts) state return break continue throw)
                      return break continue throw))))

;; A generic block execution function
(define M_state_block
  (lambda (body-stmts state return break continue throw)
    ((lambda (block-state)
       (pop-layer
        (if (list? (operator body-stmts))
            (M_state_list body-stmts block-state return break continue throw)
            (M_state body-stmts block-state return break continue throw))))
     (push-layer state))))

;; Main statement execution
(define M_state
  (lambda (stmt state return break continue throw)
    (cond
      [(null? stmt) state]
      [(eq? (operator stmt) 'begin)
       (M_state_block (cdr stmt) state return break continue throw)]
      [(list? stmt)
       (case (operator stmt)
         [(var)
          (if (null? (drop-first-two stmt))
              (state-declare (firstoperand stmt) 'uninitialized state)
              (state-declare (firstoperand stmt)
                             (M_value (secondoperand  stmt) state return break continue throw)
                             state))]
         [(=)
          ;; Ensure variable is declared (except the special 'e' used by try/catch)
          (when (and (symbol? (firstoperand stmt)) (not (eq? (firstoperand stmt) 'e)))
            (state-lookup-for-assignment (firstoperand stmt) state))
          (state-update (firstoperand stmt)
                        (M_value (secondoperand  stmt) state return break continue throw)
                        state)]
         [(return)
          (return (M_value (firstoperand stmt) state return break continue throw))]
         [(if)
          (if (M_boolean_value (M_value (firstoperand stmt) state return break continue throw))
              (M_state_block (secondoperand  stmt) state return break continue throw)
              (if (null? (cdddr stmt))
                  state
                  (M_state_block (cadddr stmt) state return break continue throw)))]
         [(while)
          (M_state_while stmt state return break continue throw)]
         [(break)
          (break state)]
         [(continue)
          (continue state)]
         [(throw)
          (throw (M_value (firstoperand stmt) state return break continue throw) state)]
         [(try)
          (M_state_try stmt state return break continue throw)]
         [else (error "Unknown statement type" stmt)])]
      [else (error "Invalid statement" stmt)])))

;; ============================
;; try-catch-finally
;; ============================

;; Helper function: find try/catch/finally clause
(define find-clause
  (lambda (type clauses)
    (cond
      [(null? clauses) #f]
      [(and (pair? (operator clauses)) (eq? (caar clauses) type)) (operator clauses)]
      [else (find-clause type (cdr clauses))])))

;; Handle try-catch-finally
(define M_state_try
  (lambda (stmt state return break continue throw)
    ((lambda (try-body catch-clause finally-clause)
       ;; A small helper to run finally clauses
       (define (execute-finally st)
         (if finally-clause
             (foldl (lambda (s st) (M_state s st return break continue throw))
                    st
                    (firstoperand finally-clause))
             st))
       ;; Now run the "try" body with a continuation for exceptions
       ((lambda (try-result)
          ((lambda (base-result)
             (execute-finally base-result))
           (if (eq? (operator try-result) 'exception)
               (if catch-clause
                   ((lambda (catch-var)
                      (pop-layer
                       (foldl (lambda (s st)
                                (M_state s st return break continue throw))
                              (state-declare
                               catch-var
                               (firstoperand try-result)
                               (push-layer (drop-first-two try-result)))
                              (secondoperand  catch-clause))))
                    (operator (firstoperand catch-clause)))
                   (throw (firstoperand try-result) (drop-first-two try-result)))
               (cdr try-result))))
        (call/cc
         (lambda (throw-k)
           (cons 'normal
                 (foldl
                  (lambda (s st)
                    (M_state s st
                             return
                             break
                             continue
                             (lambda (val st)
                               (throw-k (cons 'exception (cons val st))))))
                  state
                  try-body))))))
     (firstoperand stmt)
     (find-clause 'catch (drop-first-two stmt))
     (find-clause 'finally (drop-first-two stmt)))))

;; ============================
;; while loops
;; ============================

(define M_state_while
  (lambda (stmt state return break continue throw)
    (call/cc
     (lambda (break-k)
       (define (loop st)
         (if (M_boolean_value (M_value (firstoperand stmt) st return break-k continue throw))
             (loop
              (merge-top-bindings
               (pop-layer
                (call/cc
                 (lambda (continue-k)
                   (M_state (secondoperand  stmt)
                            (push-layer st)
                            return
                            (lambda (s)
                              (break-k (merge-top-bindings (pop-layer s) st)))
                            (lambda (s)
                              (continue-k (merge-top-bindings (pop-layer s) st)))
                            throw))))
               st))
             st))
       (loop state)))))

;; ============================
;; Merging states / layers
;; ============================

(define merge-top-bindings
  (lambda (from-state to-state)
    (if (or (null? from-state) (null? to-state))
        to-state
        ((lambda (from-layer to-layer)
           (cons (merge-layers from-layer to-layer)
                 (cdr to-state)))
         (operator from-state)
         (operator to-state)))))

(define merge-state
  (lambda (current-state original-state)
    (cond
      [(null? current-state) original-state]
      [(null? original-state) current-state]
      [else
       ((lambda (current-length original-length)
          (if (= current-length original-length)
              (cons (merge-layers (operator current-state) (operator original-state))
                    (cdr current-state))
              (if (> current-length original-length)
                  (cons (operator current-state)
                        (merge-state (cdr current-state) original-state))
                  (cons (merge-layers (operator current-state) (operator original-state))
                        (merge-state (cdr current-state)
                                     (cdr original-state))))))
        (length current-state)
        (length original-state))])))

(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       (foldr (lambda (binding result)
                ((lambda (var)
                   (if (assq var result)
                       ;; If it already exists, remove older version, keep the new
                       (cons binding (remove (assq var result) result))
                       (cons binding result)))
                 (operator binding)))
              layer2
              layer1)])))

;; ============================
;; Interpreter Entry
;; ============================

(define interpret
  (lambda (filename)
    (call/cc
     (lambda (return)
       ((lambda (program)
          (M_state_list program
                        (list '()) ; initial empty state
                        return
                        (lambda (s) (error "Error: break outside loop"))
                        (lambda (s) (error "Error: continue outside loop"))
                        (lambda (v s) (error "Error: uncaught exception" v))))
        (parser filename))))))

;; ============================
;; Test Functions
;; ============================

(define test-all
  (lambda ()
    (for-each
     (lambda (filename)
       (printf "~a\n" filename)
       (with-handlers ([exn:fail? (lambda (e)
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
       "2test16.txt" "2test17.txt" "2test18.txt" "2test19.txt"))))

(test-all); run test-all

;; Example of running them automatically:
;; (test-all)
;; (test-single "test1.txt")
