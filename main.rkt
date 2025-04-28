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
;;   (closure <raw-params> <body> <def-env> <fname>)
;; Parameters with a preceding ampersand (&) are processed into (ref x);
;; all other parameters pass through unchanged.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-closure
  (lambda (params body env fname)
    (list 'closure params body env fname)))

(define closure?
  (lambda (v)
    (and (list? v) (eq? (operator  v) 'closure))))

(define closure-params (lambda (cl) (firstoperand  cl)))
(define closure-body   (lambda (cl) (secondoperand  cl)))
(define closure-env    (lambda (cl) (cadddr cl)))
(define closure-fname  (lambda (cl) (if (< (length cl) 5) #f (list-ref cl 4))))

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

(define state-lookup
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
           (state-lookup var (operands state)))])))

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
          (define fname (firstoperand expr))
          (define actuals (drop-first-two expr))
          (define fval (if (symbol? fname)
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

(define call-function
  (lambda (closure args caller-state return break continue throw)
    (define raw-params (closure-params closure))
    (define params (process-params raw-params))
    (define body (closure-body closure))
    (define def-env (closure-env closure))
    (define fname (closure-fname closure))
    
    ;; add function itself to environment to support recursion, then bind parameters
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
    
    ;; execute function body and return result
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
                      methods)                       ; (alist name . closure)
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
  (if (classC-parent C)
      (append (class-all-fields (get-class (classC-parent C)))
              (classC-field-names C))
      (classC-field-names C)))

(define (lookup-method C m)
  (cond [(assoc m (classC-methods C))    => cadr]
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
  (vector-ref (objectC-fields obj)
              (field-index (objectC-class obj) fname)))

(define (set-field! obj fname v)
  (vector-set! (objectC-fields obj)
               (field-index (objectC-class obj) fname) v))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section B  —  Building class closures from parse trees
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (build-class tree)
  (match tree
    [(list 'class name maybe-super body ...)
     (define parent (and (pair? maybe-super) (cadr maybe-super)))
     (define fields       '())
     (define field-inits  '())
     (define methods      '())

     (for ([stmt body])
       (match stmt
         [(list 'var (id) init ...)
          (set! fields (append fields (list id)))
          (set! field-inits
                (append field-inits
                        (list (λ (st) (if (null? init)
                                          0
                                          (M_value (car init) st
                                                   (λ (_) 0) void void
                                                   (λ _ (error "init"))))))))]
         [(list 'function fname params fbody)
          (set! methods
                (cons (cons fname
                            (make-closure params fbody '() fname))
                      methods))]
         [(list 'static-function 'main params fbody)
          (set! methods
                (cons (cons 'main
                            (make-closure params fbody '() 'main))
                      methods))] ;; any other static forms ignored per spec
         [else (void)]))

     (classC name parent fields field-inits methods)]))

(define (install-classes prog)
  (for ([clsdef prog])
    (hash-set! class-table
               (cadr clsdef)   ; class name
               (build-class clsdef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Section C  —  Extend the evaluator (new / dot)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; keep originals for fallback
(define base-M_value   M_value)
(define base-state-lookup state-lookup)
(define base-state-update state-update)

;; find ‘this’ up env-stack
(define (find-this st)
  (cond [(null? st) #f]
        [(assq 'this (car st)) => (λ (b) (unbox (cdr b)))]
        [else (find-this (cdr st))]))

;; 1.  enhanced state-lookup / update
(define (state-lookup var state)
  (with-handlers ([exn:fail?
                   (λ (e)
                     (define self (find-this state))
                     (if (and self (objectC? self)
                              (member var
                                      (class-all-fields
                                       (objectC-class self))))
                         (get-field self var)
                         (raise e)))])
    (base-state-lookup var state)))


(define (state-update var val state)
  (with-handlers ([exn:fail?
                   (λ (e)
                     (define self (find-this state))
                     (if (and self (objectC? self)
                              (member var (class-all-fields
                                           (objectC-class self))))
                         (begin (set-field! self var val) state)
                         (raise e)))])
    (base-state-update var val state)))

;; 2.  ‘new’   -------------------------------------------------------
(define (eval-new cname state)
  (define C (get-class cname))
  (define init-vec
    (for/vector ([th (in-list (classC-field-inits C))])
      (th state)))
  (objectC C init-vec))

;; 3.  redefine M_value with cases for new / dot  --------------------
(define (M_value expr state return break continue throw)
  (cond
    ;; ---- NEW ------------------------------------------------------
    [(and (pair? expr) (eq? (car expr) 'new))
     (eval-new (cadr expr) state)]

    ;; ---- DOT ------------------------------------------------------
    [(and (pair? expr) (eq? (car expr) 'dot))
     (define obj (M_value (cadr expr) state return break continue throw))
     (unless (objectC? obj) (error 'dot "lhs is not an object"))
     (define id  (caddr expr))
     (cond
       ;; method?
       [(assoc id (classC-methods (objectC-class obj))) =>
                                                        (λ (pair)
                                                          (define mclos (cdr pair))
                                                          ;; produce bound method closure with this=obj
                                                          (make-closure (closure-params mclos)
                                                                        (closure-body   mclos)
                                                                        (state-declare 'this obj (closure-env mclos))
                                                                        (closure-fname  mclos)))]
       ;; else field
       [else (get-field obj id)])]

    ;; otherwise defer to old evaluator -----------------------------
    [else (base-M_value expr state return break continue throw)]))

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
        (install-classes prog)
        (define C      (get-class classname))
        (define main   (lookup-method C 'main))
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
       "3test16.txt" "3test17.txt" "3test18.txt" "3test19.txt" "3test20.txt"))))

(define interpret
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
(test-all)

;; or run specific test (uncomment to test specific file)
(interpret "3test19.txt")  ;; test 19-exception handling
;;(interpret "3test20.txt")  ;; test 20-nested exception handling
;;(interpret "3test16.txt")  ;; test 16-function nested function nested function
