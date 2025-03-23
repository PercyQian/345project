#lang racket

(require "simpleParser.rkt")

;; ============================
;; State Operations
;; ============================

(define state-lookup
  (lambda (var state)
    (match (assq var state)
      [#f (error "Error: using before declaring" var)]
      [(cons _ 'uninitialized) (error "Error: using before assigning" var)]
      [(cons _ val) 
       (cond
         [(eq? val 'true) #t]
         [(eq? val 'false) #f]
         [else val])])))

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
       (let ([stored-val (cond
                          [(eq? val #t) 'true]
                          [(eq? val #f) 'false]
                          [else val])])
         (append before (list (cons var stored-val)) after))])))

;; 辅助函数:将状态分割成三部分:目标变量之前、目标变量、之后
(define split-at-var
  (lambda (var state)
    (let loop ([before '()] [rest state])
      (cond
        [(null? rest) (list before #f '())]
        [(eq? var (caar rest)) (list before (car rest) (cdr rest))]
        [else (loop (append before (list (car rest))) (cdr rest))]))))

;; ============================
;; Expression Evaluation
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
      ((eq? val 'true) #t)
      ((eq? val 'false) #f)
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
       (let ([val-a (M_value a state)]
             [val-b (M_value b state)])
         (case op
           [(== != < > <= >= || &&) 
            (evaluate-boolean-op op val-a val-b)]
           [else (evaluate-numeric-op op val-a val-b)]))]
      [(list '- a) (- (coerce-to-number (M_value a state)))]
      [_ (error 'bad-expr "Error: Unknown expression")])))

;; 分离布尔运算和数值运算
(define evaluate-boolean-op
  (lambda (op a b)
    (case op
      [(==) (equal? a b)]
      [(!=) (not (equal? a b))]
      [(<) (< (coerce-to-number a) (coerce-to-number b))]
      [(>) (> (coerce-to-number a) (coerce-to-number b))]
      [(<=) (<= (coerce-to-number a) (coerce-to-number b))]
      [(>=) (>= (coerce-to-number a) (coerce-to-number b))]
      [(||) (or (coerce-to-boolean a) (coerce-to-boolean b))]
      [(&&) (and (coerce-to-boolean a) (coerce-to-boolean b))])))

(define evaluate-numeric-op
  (lambda (op a b)
    (case op
      [(+) (+ (coerce-to-number a) (coerce-to-number b))]
      [(-) (- (coerce-to-number a) (coerce-to-number b))]
      [(*) (* (coerce-to-number a) (coerce-to-number b))]
      [(/) (if (zero? (coerce-to-number b))
               (error "Division by zero")
               (quotient (coerce-to-number a) (coerce-to-number b)))]
      [(%) (modulo (coerce-to-number a) (coerce-to-number b))])))

;; ============================
;; Statement Execution
;; ============================

(define M_statement
  (lambda (stmt state)
    (match stmt
      [(list 'var var) 
       (cons (state-declare var 'uninitialized state) #f)]
      
      [(list 'var var expr) 
       (let ([val (M_value expr state)])
         (cons (state-declare var val state) #f))]
      
      [(list '= var expr)
       (let ([val (M_value expr state)])
         (cons (state-update var val state) #f))]
      
      [(list 'return expr)
       (let ([val (M_value expr state)])
         (cons (cons (cons 'return-flag #t) state) val))]
      
      [(list 'if cond then-stmt)
       (let ([cond-val (coerce-to-boolean (M_value cond state))])
         (if cond-val
             (M_statement then-stmt state)
             (cons state #f)))]
      
      [(list 'if cond then-stmt else-stmt)
       (let ([cond-val (coerce-to-boolean (M_value cond state))])
         (if cond-val
             (M_statement then-stmt state)
             (M_statement else-stmt state)))]
      
      [(list 'while cond body)
       (if (coerce-to-boolean (M_value cond state))
           (match (M_statement body state)
             [(cons new-state #f) (M_statement stmt new-state)]
             [result result])
           (cons state #f))]
      
      [(cons 'begin stmts)
       (execute-statements stmts state)]
      
      [_ (error 'bad-stmt "Error: Unknown statement type")])))

;; 辅助函数:执行语句序列
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
    (let* ([result (M_state (parser filename) '())]
           [state (car result)]
           [return-val (cdr result)])
      (if (and (pair? result) (eq? (cdr result) #f) (not (assq 'return-flag state)))
          ;; 程序没有return语句的情况
          0
          ;; 程序有return语句的情况
          (cond
            [(eq? return-val #t) 'true]
            [(eq? return-val #f) 'false]
            [else return-val])))))

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

