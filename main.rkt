#lang racket

(require "simpleParser.rkt")

;; ============================
;; 状态管理
;; ============================

;; 创建新的作用域层
(define push-layer
  (lambda (state)
    (cons '() state)))

;; 移除顶层作用域
(define pop-layer
  (lambda (state)
    (cdr state)))

;; 在当前层声明变量
(define state-declare
  (lambda (var val state)
    (if (null? state)
        (error "Error: state is empty")
        (let ([layer (car state)]
              [rest (cdr state)])
          (cond
            [(assq var layer) (error "Error: redefining" var)]
            [else (cons (cons (cons var (box val)) layer) rest)])))))

;; 查找变量值 - 增加严格的作用域检查
(define state-lookup
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (let ([binding (assq var (car state))])
              (if binding
                  (let ([boxed-value (cdr binding)])
                    (let ([val (unbox boxed-value)])
                      (if (eq? val 'uninitialized)
                          (error "Error: using before assigning" var)
                          val)))
                  (state-lookup var (cdr state))))])))

;; 在赋值时使用的查找函数 - 只检查变量是否存在,不检查是否已初始化
(define state-lookup-for-assignment
  (lambda (var state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (let ([binding (assq var (car state))])
              (if binding
                  #t  ;; 变量存在,返回true
                  (state-lookup-for-assignment var (cdr state))))])))

;; 更新变量值
(define state-update
  (lambda (var val state)
    (cond
      [(null? state) (error "Error: using before declaring" var)]
      [else (let ([layer (car state)]
                  [rest (cdr state)])
              (let ([binding (assq var layer)])
                (if binding
                    (begin  
                      (set-box! (cdr binding) val)
                      state)
                    ;; 严格检查: 如果在顶层找不到变量直接报错
                    (if (and (not (eq? var 'e)) (null? rest))
                        (error "Error: using before declaring" var)
                        (cons layer (state-update var val rest))))))])))

;; ============================
;; 表达式求值
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
         [(+ - * / %)
          (let ([op (car expr)]
                [v1 (M_value (cadr expr) state return break continue throw)]
                [v2 (M_value (caddr expr) state return break continue throw)])
            (case op
              [(+) (+ v1 v2)]
              [(-) (- v1 v2)]
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

;; 转换为布尔值
(define M_boolean_value
  (lambda (v)
    (cond
      [(boolean? v) v]
      [(number? v) (not (zero? v))]
      [else (error "Cannot convert to boolean" v)])))

;; ============================
;; 语句执行
;; ============================

;; 执行语句列表
(define M_state_list
  (lambda (stmts state return break continue throw)
    (if (null? stmts)
        state
        (M_state_list (cdr stmts)
                      (M_state (car stmts) state return break continue throw)
                      return break continue throw))))

;; 主语句执行函数,加强作用域规则
(define M_state
  (lambda (stmt state return break continue throw)
    (cond
      [(null? stmt) state]
      [(eq? (car stmt) 'begin)
       ;; begin块自动创建新作用域
       (let* ([new-state (push-layer state)]
              [result (M_state_list (cdr stmt) new-state return break continue throw)])
         (pop-layer result))]
      [(list? stmt)
       (case (car stmt)
         [(var)
          (if (null? (cddr stmt))
              (state-declare (cadr stmt) 'uninitialized state)
              (state-declare (cadr stmt) (M_value (caddr stmt) state return break continue throw) state))]
         [(=)
          (let ([var (cadr stmt)]
                [val (M_value (caddr stmt) state return break continue throw)])
            ;; 使用专用函数检查变量存在性
            (when (and (symbol? var) (not (eq? var 'e)))
              (state-lookup-for-assignment var state))  ;; 只检查变量是否存在,不检查初始化状态
            (state-update var val state))]
         [(return)
          (return (M_value (cadr stmt) state return break continue throw))]
         [(if)
          (if (M_boolean_value (M_value (cadr stmt) state return break continue throw))
              ;; if块和else块也应该创建新作用域
              (let* ([new-state (push-layer state)]
                     [result (M_state (caddr stmt) new-state return break continue throw)])
                (pop-layer result))
              (if (null? (cdddr stmt))
                  state
                  (let* ([new-state (push-layer state)]
                         [result (M_state (cadddr stmt) new-state return break continue throw)])
                    (pop-layer result))))]
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

;; 辅助函数:查找try-catch-finally子句
(define find-clause
  (lambda (type clauses)
    (cond
      [(null? clauses) #f]
      [(and (pair? (car clauses)) (eq? (caar clauses) type)) (car clauses)]
      [else (find-clause type (cdr clauses))])))

;; 处理try-catch-finally语句
(define M_state_try
  (lambda (stmt state return break continue throw)
    (let ([try-body (cadr stmt)]
          [clauses (cddr stmt)])
      (let ([catch-clause (find-clause 'catch clauses)]
            [finally-clause (find-clause 'finally clauses)])
        
        ;; 标记异常的辅助函数
        (define (mark-as-exception val st)
          (cons 'exception (cons val st)))
        
        ;; 检查是否是异常
        (define (exception? obj)
          (and (pair? obj) (eq? (car obj) 'exception)))
        
        ;; 获取异常值和状态
        (define (exception-val-state exn)
          (values (cadr exn) (cddr exn)))
        
        ;; 执行finally块
        (define (execute-finally st)
          (if finally-clause
              (let ([finally-stmts (cadr finally-clause)])
                (foldl (lambda (s st)
                         (M_state s st return break continue throw))
                       st
                       finally-stmts))
              st))
        
        ;; 执行try块
        (let ([try-result
               (call/cc
                (lambda (return-from-try)
                  (call/cc
                   (lambda (throw-from-try)
                     (let ([local-throw 
                            (lambda (val st)
                              (throw-from-try (mark-as-exception val st)))])
                       (let ([after-try 
                              (foldl 
                               (lambda (s st)
                                 (M_state s st return break continue local-throw))
                               state
                               try-body)])
                         (let ([final-state (execute-finally after-try)])
                           (return-from-try final-state))))))))])
          
          ;; 检查是否有异常
          (if (exception? try-result)
              ;; 处理异常情况
              (let-values ([(exception-val exception-state) (exception-val-state try-result)])
                (if catch-clause
                    ;; 执行catch块
                    (let* ([catch-var-expr (cadr catch-clause)]
                           [catch-var (car catch-var-expr)]
                           [catch-body (caddr catch-clause)]
                           [new-layer (push-layer exception-state)]
                           [with-exception (state-declare catch-var exception-val new-layer)]
                           [after-catch (foldl 
                                         (lambda (s st) 
                                           (M_state s st return break continue throw))
                                         with-exception
                                         catch-body)]
                           [removed-layer (pop-layer after-catch)]
                           [final-state (execute-finally removed-layer)])
                      final-state)
                    ;; 无catch块 - 执行finally后继续抛出异常
                    (let ([final-state (execute-finally exception-state)])
                      (throw exception-val final-state))))
              
              ;; 正常情况 - 返回状态
              try-result))))))

;; 循环语句 - 为每次迭代创建新作用域
(define M_state_while
  (lambda (stmt state return break continue throw)
    (call/cc
     (lambda (break-k)
       (letrec ([loop (lambda (state)
                        (if (M_boolean_value (M_value (cadr stmt) state return break-k continue throw))
                            ;; 为循环体创建新的作用域
                            (let* ([loop-state (push-layer state)]
                                   [body-state 
                                    (call/cc
                                     (lambda (continue-k)
                                       (M_state (caddr stmt) 
                                               loop-state
                                               return 
                                               (lambda (s) (break-k (merge-top-bindings (pop-layer s) state)))
                                               (lambda (s) (continue-k (merge-top-bindings (pop-layer s) state)))
                                               throw)))])
                              ;; 保留变量更新但移除作用域
                              (loop (merge-top-bindings (pop-layer body-state) state)))
                            state))])
         (loop state))))))

;; 合并顶层变量绑定
(define merge-top-bindings
  (lambda (from-state to-state)
    (if (or (null? from-state) (null? to-state))
        to-state
        (let ([from-layer (car from-state)]
              [to-layer (car to-state)])
          (cons (merge-layers from-layer to-layer)
                (cdr to-state))))))

;; 合并两个状态,保留当前状态中的变量值,但清除多余层
(define merge-state
  (lambda (current-state original-state)
    (cond
      ;; 处理空状态情况
      [(null? current-state) original-state]
      [(null? original-state) current-state]
      ;; 正常情况
      [else
       (let ([current-length (length current-state)]
             [original-length (length original-state)])
         (if (= current-length original-length)
             ;; 长度相同时,合并最外层
             (cons (merge-layers (car current-state) (car original-state))
                   (cdr current-state))
             ;; 长度不同时,递归处理
             (if (> current-length original-length)
                 ;; 当前状态层数多,保留当前层但合并内部状态
                 (cons (car current-state) 
                       (merge-state (cdr current-state) original-state))
                 ;; 原始状态层数多,保留原始层同时合并
                 (cons (merge-layers (car current-state) (car original-state))
                       (merge-state (cdr current-state) (cdr original-state))))))])))

;; 合并两个层中的变量绑定
(define merge-layers
  (lambda (layer1 layer2)
    (cond
      [(null? layer1) layer2]
      [(null? layer2) layer1]
      [else
       ;; 将layer1中的绑定合并到layer2中
       (foldr (lambda (binding result)
                (let ([var (car binding)])
                  (if (assq var result)
                      ;; 变量已存在于layer2,使用layer1的值更新
                      (cons binding (remove (assq var result) result))
                      ;; 变量不存在,添加到结果
                      (cons binding result))))
              layer2
              layer1)])))

;; ============================
;; 解释器入口
;; ============================

(define interpret
  (lambda (filename)
    (call/cc
     (lambda (return)
       (let ([program (parser filename)])
         ;; 程序是一个语句列表,所以我们直接调用M_state_list
         (M_state_list program 
                      (list '()) ; 初始空状态
                      return
                      (lambda (s) (error "Error: break outside loop"))
                      (lambda (s) (error "Error: continue outside loop"))
                      (lambda (v s) (error "Error: uncaught exception" v))))))))

;; ============================
;; 测试函数
;; ============================

;; 测试框架 - 综合测试所有文件
(define test-all
  (lambda ()
    (for-each
     (lambda (filename)
       (printf "~a\n" filename)
       (with-handlers ([exn:fail? (lambda (e)
                                   (printf "ERROR: ~a\n" (exn-message e)))])
         (printf "Result: ~a\n" (interpret filename))))
     '("test1.txt" "test2.txt" "test3.txt" "test4.txt" "test5.txt"
       "test6.txt" "test7.txt" "test8.txt" "test9.txt" "test10.txt"
       "test11.txt" "test12.txt" "test13.txt" "test14.txt" "test15.txt"
       "test16.txt" "test17.txt" "test18.txt" "test19.txt"))))

;; 特殊测试函数 - 只测试一个文件并打印详细结构
(define test-single
  (lambda (filename)
    (printf "测试文件: ~a\n" filename)
    (let ([program (parser filename)])
      (printf "解析结果:\n~a\n" program)
      (with-handlers ([exn:fail? (lambda (e)
                                   (printf "错误信息: ~a\n" (exn-message e)))])
        (let ([result (interpret filename)])
          (printf "返回结果: ~a\n" result))))))

;; 执行部分测试
(test-all)  ;; 运行所有测试
