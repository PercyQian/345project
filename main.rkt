#lang racket

(require "simpleParser.rkt")

;; ============================
;; 状态管理
;; ============================

;; 创建新的状态对象 - 更明确地表示层级结构
(define make-state
  (lambda ()
    (list '())))  ;; 初始状态:单层空环境

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

;; 变量层级查找 - 返回找到变量的层及其位置
(define state-lookup-layer
  (lambda (var state)
    (letrec ([search-layers 
              (lambda (var layers layer-idx)
                (if (null? layers)
                    (values #f #f)  ;; 未找到
                    (let ([binding (assq var (car layers))])
                      (if binding
                          (values (car layers) layer-idx)  ;; 找到变量所在层
                          (search-layers var (cdr layers) (+ layer-idx 1))))))])
      (search-layers var state 0))))

;; 更新状态查找接口
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
                  ;; 变量不在顶层 - 继续在更深层查找
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

;; 更新状态更新接口
(define state-update
  (lambda (var val state)
    (let-values ([(layer layer-idx) (state-lookup-layer var state)])
      (if layer
          ;; 找到变量所在层 - 更新其值
          (let ([binding (assq var layer)])
            (set-box! (cdr binding) val)
            state)
          ;; 未找到变量 - 错误处理
          (if (eq? var 'e) 
              ;; 为try-catch专门处理
              (state-declare var val state)
              (error "Error: using before declaring" var))))))

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
         [(- +) 
          ;; 检查是否为一元负号/正号
          (if (null? (cddr expr))
              (let ([v (M_value (cadr expr) state return break continue throw)])
                (case (car expr)
                  [(+) v]
                  [(-) (- v)]))
              ;; 否则是二元操作符
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

;; 添加通用的块执行函数
(define M_state_block
  (lambda (body-stmts state return break continue throw)
    ;; 创建新作用域层
    (let ([block-state (push-layer state)])
      ;; 执行块内语句并返回弹出层后的状态
      (pop-layer 
       (if (list? (car body-stmts)) 
           ;; 处理语句列表
           (M_state_list body-stmts block-state return break continue throw)
           ;; 处理单个语句
           (M_state body-stmts block-state return break continue throw))))))

;; 主语句执行函数,加强作用域规则
(define M_state
  (lambda (stmt state return break continue throw)
    (cond
      [(null? stmt) state]
      [(eq? (car stmt) 'begin)
       ;; begin块自动创建新作用域
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
              ;; 使用通用块执行函数处理if分支
              (M_state_block (caddr stmt) state return break continue throw)
              (if (null? (cdddr stmt))
                  state
                  ;; 使用通用块执行函数处理else分支
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
          [catch-clause (find-clause 'catch (cddr stmt))]
          [finally-clause (find-clause 'finally (cddr stmt))])
      
      ;; 辅助函数定义
      (define (execute-finally st)
        (if finally-clause
            (foldl (lambda (s st) (M_state s st return break continue throw))
                   st
                   (cadr finally-clause))
            st))
      
      ;; 简化异常处理结构
      (let* ([try-result 
              (call/cc
               (lambda (throw-k)
                 ;; 使用标记来区分正常执行和异常
                 (cons 'normal
                       (foldl (lambda (s st)
                                (M_state s st 
                                         ;; 保持return continuation不变
                                         return 
                                         break continue
                                         (lambda (val st) 
                                           (throw-k (cons 'exception (cons val st))))))
                              state
                              try-body))))]
             
             ;; 处理try块执行结果
             [base-result 
              (if (eq? (car try-result) 'exception)
                  ;; 有异常 - 执行catch块
                  (if catch-clause
                      (let ([catch-var (car (cadr catch-clause))])
                        (pop-layer
                         (foldl (lambda (s st) 
                                  (M_state s st return break continue throw))
                                (state-declare catch-var 
                                              (cadr try-result) 
                                              (push-layer (cddr try-result)))
                                (caddr catch-clause))))
                      ;; 无catch - 调用外部throw
                      (throw (cadr try-result) (cddr try-result)))
                  ;; 正常执行 - 使用try块的结果
                  (cdr try-result))])
        
        ;; 最后执行finally块
        (execute-finally base-result)))))

;; 循环语句 - 为每次迭代创建新作用域
(define M_state_while
  (lambda (stmt state return break continue throw)
    (call/cc
     (lambda (break-k)
       (letrec ([loop (lambda (state)
                        (if (M_boolean_value (M_value (cadr stmt) state return break-k continue throw))
                            ;; 减少嵌套let,使用函数组合
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
         (let ([result (interpret filename)])
           ;; 转换布尔值为true/false
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
