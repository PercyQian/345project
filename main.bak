#lang racket

(require "simpleParser.rkt")

;; ============================
;; State Operations - 使用纯函数式方法
;; ============================

(define state-lookup
  (lambda (var state)
    (match (assq var state)
      [#f (error "Error: using before declaring" var)]
      [(cons _ 'uninitialized) (error "Error: using before assigning" var)]
      [(cons _ val) val])))

(define state-declare
  (lambda (var val state)
    (if (assq var state)
        (error "Error: redefining" var)
        (cons (cons var val) state))))

(define state-update
  (lambda (var val state)
    (match (split-at-var var state)
      [(list before #f _) (error "Error: using before declaring" var)]
      [(list before pair after) 
       (append before (list (cons var val)) after)])))

;; 辅助函数：将状态分割成三部分：目标变量之前、目标变量、之后
(define split-at-var
  (lambda (var state)
    (let loop ([before '()] [rest state])
      (cond
        [(null? rest) (list before #f '())]
        [(eq? var (caar rest)) (list before (car rest) (cdr rest))]
        [else (loop (append before (list (car rest))) (cdr rest))]))))


;; ============================
;; Expression Evaluation - 使用模式匹配简化代码
;; ============================

(define coerce-to-number
  (lambda (val)
    (cond
      ((number? val) val)
      ((boolean? val) (if val 1 0))
      (else (error "Error: Cannot coerce to number" val)))))

(define coerce-to-boolean
  (lambda (val)
    (cond
      ((boolean? val) val)
      ((number? val) (not (zero? val)))
      (else (error "Error: Cannot coerce to boolean" val)))))

(define operator car)
(define firstoperand cadr)
(define secondoperand caddr)

(define M_value
  (lambda (expr state)
    (match expr
      [(? number?) expr]
      ['true #t]
      ['false #f]
      [(? symbol?) (state-lookup expr state)]
      [(list '! a) (not (coerce-to-boolean (M_value a state)))]
      [(list op a b) 
       (evaluate-binary-op op 
                          (M_value a state)
                          (M_value b state))]
      [(list '- a) (- (coerce-to-number (M_value a state)))]
      [_ (error 'bad-expr "Error: Unknown expression")])))

;; 辅助函数：处理二元运算
(define evaluate-binary-op
  (lambda (op a b)
    (match op
      ['+ (+ (coerce-to-number a) (coerce-to-number b))]
      ['- (- (coerce-to-number a) (coerce-to-number b))]
      ['* (* (coerce-to-number a) (coerce-to-number b))]
      ['/ (if (zero? (coerce-to-number b))
              (error "Division by zero")
              (quotient (coerce-to-number a) (coerce-to-number b)))]
      ['% (modulo (coerce-to-number a) (coerce-to-number b))]
      ['== (= (coerce-to-number a) (coerce-to-number b))]
      ['!= (not (= (coerce-to-number a) (coerce-to-number b)))]
      ['< (< (coerce-to-number a) (coerce-to-number b))]
      ['> (> (coerce-to-number a) (coerce-to-number b))]
      ['<= (<= (coerce-to-number a) (coerce-to-number b))]
      ['>= (>= (coerce-to-number a) (coerce-to-number b))]
      ['|| (or (coerce-to-boolean a) (coerce-to-boolean b))]
      ['&& (and (coerce-to-boolean a) (coerce-to-boolean b))]
      [_ (error 'bad-op "Error: Invalid operation")])))


;; ============================
;; Boolean Expression Evaluation
;; ============================

(define M_boolean
  (lambda (expression state)
    (cond
      ((boolean? expression) expression)
      ((eq? expression 'true) #t)
      ((eq? expression 'false) #f)
      ((symbol? expression) (state-lookup expression state))
      ((pair? expression)
       (cond
         ;; Boolean operators
         ((eq? '&& (operator expression)) 
          (and (M_boolean (firstoperand expression) state) 
               (M_boolean (secondoperand expression) state)))
         ((eq? '|| (operator expression)) 
          (or (M_boolean (firstoperand expression) state) 
              (M_boolean (secondoperand expression) state)))
         ((eq? '! (operator expression)) 
          (not (M_boolean (firstoperand expression) state)))

         ;; Relational operators
         ((eq? '== (operator expression)) 
          (equal? (M_value (firstoperand expression) state)
                  (M_value (secondoperand expression) state)))
         ((eq? '!= (operator expression)) 
          (not (equal? (M_value (firstoperand expression) state)
                       (M_value (secondoperand expression) state))))
         ((eq? '< (operator expression)) 
          (< (M_value (firstoperand expression) state)
             (M_value (secondoperand expression) state)))
         ((eq? '> (operator expression)) 
          (> (M_value (firstoperand expression) state)
             (M_value (secondoperand expression) state)))
         ((eq? '<= (operator expression)) 
          (<= (M_value (firstoperand expression) state)
              (M_value (secondoperand expression) state)))
         ((eq? '>= (operator expression)) 
          (>= (M_value (firstoperand expression) state)
              (M_value (secondoperand expression) state)))

         (else (error 'bad-op "Error: Invalid boolean operation"))))
      (else (error 'bad-expr "Error: Invalid boolean expression")))))


;; ============================
;; Statement Execution - 使用模式匹配和递归替代命令式编程
;; ============================

(define M_statement
  (lambda (stmt state)
    (match stmt
      [(list 'var var) 
       (cons (state-declare var 'uninitialized state) #f)]
      
      [(list 'var var expr) 
       (cons (state-declare var (M_value expr state) state) #f)]
      
      [(list '= var expr)
       (cons (state-update var (M_value expr state) state) #f)]
      
      [(list 'return expr)
       (cons state (M_value expr state))]
      
      [(list 'if cond then-stmt)
       (if (coerce-to-boolean (M_value cond state))
           (M_statement then-stmt state)
           (cons state #f))]
      
      [(list 'if cond then-stmt else-stmt)
       (if (coerce-to-boolean (M_value cond state))
           (M_statement then-stmt state)
           (M_statement else-stmt state))]
      
      [(list 'while cond body)
       (if (coerce-to-boolean (M_value cond state))
           (match (M_statement body state)
             [(cons new-state #f) (M_statement stmt new-state)]
             [result result])
           (cons state #f))]
      
      [(cons 'begin stmts)
       (execute-statements stmts state)]
      
      [_ (error 'bad-stmt "Error: Unknown statement type")])))

;; 辅助函数：执行语句序列
(define execute-statements
  (lambda (stmts state)
    (match stmts
      ['() (cons state #f)]
      [(cons stmt rest)
       (match (M_statement stmt state)
         [(cons new-state #f) (execute-statements rest new-state)]
         [result result])])))


;; ============================
;; Program Execution
;; ============================

(define interpret
  (lambda (filename)
    (match (M_state (parser filename) '())
      [(cons _ #f) 0]
      [(cons _ val) (cond
                     [(boolean? val) (if val 'true 'false)]
                     [else val])])))

(define M_state execute-statements)


;; ============================
;; Testing
;; ============================

(define test-files
  '("test1.txt" "test2.txt" "test3.txt" "test4.txt" "test5.txt"
    "test6.txt" "test7.txt" "test8.txt" "test9.txt" "test10.txt"
    "test11.txt" "test12.txt" "test13.txt" "test14.txt" "test15.txt"
    "test16.txt" "test17.txt" "test18.txt" "test19.txt" "test20.txt"))

(define test
  (lambda ()
    (for-each
     (lambda (filename)
       (printf "~a\n" filename)
       (with-handlers ([exn:fail? (lambda (e)
                                   (printf "~a\n" (exn-message e)))])
         (printf "Result: ~a\n" (interpret filename))))
     test-files)))

(test)
