;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [var-exp
    (id symbol?)]
  [lit-exp
    (val (lambda (x)
            (ormap
              (lambda (pred) (pred x))
              (list number? vector? boolean? symbol? string? pair? null?))))]
  [if-exp
    (conditional expression?)
    (body expression?)]
  [if-else-exp
    (conditional expression?)
    (body expression?)
    (fallback expression?)]
  [set-exp
    (id symbol?)
    (body expression?)]
  [let-exp
    (binds (list-of (lambda (x) (and (symbol? (car x)) (expression? (cadr x))))))
    (bodies (list-of expression?))]
  [let*-exp
    (binds (list-of (lambda (x) (and (symbol? (car x)) (expression? (cadr x))))))
    (bodies (list-of expression?))]
  [letrec-exp
    (binds (list-of (lambda (x) (and (symbol? (car x)) (expression? (cadr x))))))
    (bodies (list-of expression?))]
  [named-let-exp
    (name symbol?)
    (binds (list-of (lambda (x) (and (symbol? (car x)) (expression? (cadr x))))))
    (bodies (list-of expression?))]
  [lambda-exp
    (ids (list-of symbol?))
    (bodies (list-of expression?))]
  [lambda-variable-exp
    (ids (lambda (x) (or (symbol? x) (improper? x))))
    (bodies (list-of expression?))]
  [app-exp
    (rator expression?)
    (rands (list-of expression?))])

;;(define-datatype environment environment?
  ;;(empty-env-record)
  ;;(extended-env-record
   ;;(syms (list-of symbol?))
   ;;(vals (list-of scheme-value?))
   ;;(env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])



;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (datum)
    (cond
     [(symbol? datum) (var-exp datum)]
     [(or (number? datum) (boolean? datum) (string? datum) (vector? datum)) (lit-exp datum)]
     [(pair? datum)
      (cond
          [(eqv? (car datum) 'lambda)
            (if (< (length datum) 3)
              (eopl:error 'parse-exp "incorrect length in lambda expression ~s" datum))
            (cond 
              [((list-of symbol?) (2nd datum))
                (lambda-exp (2nd  datum)
                (map parse-exp (cddr datum)))]
              [(or (symbol? (2nd datum)) (improper-symbols? (2nd datum)))
                (lambda-variable-exp (2nd datum)
                  (map parse-exp (cddr datum)))]
            [else
              (eopl:error 'parse-exp "bad lambda expression: ~s" datum)])]
      [(eqv? (car datum) 'if)
        (cond
          [(= 3 (length datum))
            (if-exp 
              (parse-exp (2nd datum))
              (parse-exp (3rd datum)))]
          [(= 4 (length datum))
            (if-else-exp 
              (parse-exp (2nd datum))
              (parse-exp (3rd datum)) 
              (parse-exp (4th datum)))]
          [else
            (eopl:error 'parse-exp "incorrect length in if expression: ~s" datum)])]
      [(eqv? (car datum) 'set!)
        (if (not (= 3 (length datum)))
          (eopl:error 'parse-exp "incorrect length in set! expression: ~s" datum))
        (if (not (symbol? (2nd datum)))
          (eopl:error 'parse-exp "must set a symbol in set! expression: ~s" datum))
        (set-exp (2nd datum) (parse-exp (3rd datum)))]
      [(eqv? (car datum) 'let)
        (cond
          [(< (length datum) 3)
            (eopl:error 'parse-exp "too short let expression: ~s" datum)]
          [(symbol? (2nd datum))
            (if (not (and 
              (list? (3rd datum))
              (andmap (lambda (x) 
                (and (list? x) (= 2 (length x)) (symbol? (car x)))) (4rd datum))))
              (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
            (named-let-exp
              (2nd datum)
              (map (lambda (pair)
                  (list (car pair) (parse-exp (cadr pair))))
                (3rd datum))
              (map parse-exp (cdddr datum)))]
          [else
            (if (not (and 
              (list? (2nd datum))
              (andmap (lambda (x) 
                (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
              (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
            (let-exp 
              (map (lambda (pair)
                  (list (car pair) (parse-exp (cadr pair))))
                (2nd datum))
              (map parse-exp (cddr datum)))])]
      [(eqv? (car datum) 'let*)
        (if (< (length datum) 3)
          (eopl:error 'parse-exp "too short let expression: ~s" datum))
        (if (not (and 
          (list? (2nd datum))
          (andmap (lambda (x) 
            (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
          (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
        (let*-exp 
          (map (lambda (pair)
              (list (car pair) (parse-exp (cadr pair))))
            (2nd datum))
          (map parse-exp (cddr datum)))]
      [(eqv? (car datum) 'letrec)
        (if (< (length datum) 3)
          (eopl:error 'parse-exp "too short let expression: ~s" datum))
        (if (not (and 
          (list? (2nd datum))
          (andmap (lambda (x) 
            (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
          (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
        (letrec-exp 
          (map (lambda (pair)
              (list (car pair) (parse-exp (cadr pair))))
            (2nd datum))
          (map parse-exp (cddr datum)))]
      [(eq? (car datum) 'quote)
        (lit-exp (cadr datum))]
      [else 
        (if (not (list? (cdr datum)))
          (eopl:error 'parse-exp "bad argument list in application: ~s" datum))
        (app-exp (parse-exp (1st datum))
        (map parse-exp (cdr datum)))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))







;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+


;; environment type definitions

(define scheme-value?
  (lambda (x) #t))


(define empty-env
  (lambda ()
    '()))


(define extend-env
  (lambda (symbols values env)
    (cons (cons symbols
                (list->vector values))
          env)))


(define apply-env
  (lambda (env symbol success fail)
    (if (null? env)
        (fail)
        (let ([symbols (caar env)]
              [values (cdar env)]
              [enclosing-env (cdr env)])
          (let ([pos (rib-find-position symbol symbols)])
            (if (number? pos)
                (success (vector-ref values pos))
                (apply-env enclosing-env symbol success fail)))))))


; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

;;(define empty-env
  ;;(lambda ()
    ;;(empty-env-record)))

;;(define extend-env
  ;;(lambda (syms vals env)
    ;;(extended-env-record syms vals env)))

(define rib-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
             (if (number? list-index-r)
                 (+ 1 list-index-r)
                 #f))))))

;;(define apply-env
  ;;(lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    ;;(cases environment env
      ;;(empty-env-record ()
        ;;(fail))
      ;;(extended-env-record (syms vals env)
	;;(let ((pos (list-find-position sym syms)))
      	  ;;(if (number? pos)
	      ;;(succeed (list-ref vals pos))
	      ;;(apply-env env sym succeed fail)))))))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



;; To be added later









;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+



;; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form (empty-env))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (let ((identity-proc (lambda (x) x)))
    (lambda (exp env)
        (cases expression exp
               [lit-exp (datum) datum]
               [if-else-exp (conditional-exp then-exp else-exp)
                (if (eval-exp conditional-exp env)
                  (eval-exp then-exp env)
                  (eval-exp else-exp env))]
               [var-exp (id)
                        (apply-env env id ; look up its value.
                         identity-proc ; procedure to call if id is in the environment
                         (lambda () 
                          (apply-env global-env id
                            identity-proc
                            (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
                                                "variable not found in environment: ~s" id)))))]
               [app-exp (rator rands)
                        (let ([proc-value (eval-exp rator env)]
                              [args (eval-rands rands env)])
                          (apply-proc proc-value args))]
               [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))
  
; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (exp) (eval-exp exp env)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s"
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 zero? = < <= > >= not cons car cdr list null? assq eq?
                            equal? atom? length list->vector list? pair? procedure? vector->list vector 
                            vector-set! display newline cadr cdar caar cddr caaar caadr cadar cdaar caddr cdadr cddar cdddr))

(define global-env         ; for now, our initial global environment only contains
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (trace-lambda apply-prim-proc (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (apply add1 args)]
      [(sub1) (apply sub1 args)] 
      [(zero?) (apply zero? args)]
      [(=) (apply = args)]
      [(<) (apply < args)]
      [(<=) (apply <= args)]
      [(>) (apply > args)]
      [(>=) (apply >= args)]
      [(not) (apply not args)]
      [(cons) (apply cons args)]
      [(car) (apply car args)]
      [(cdr) (apply cdr args)]
      [(list) (apply list args)]
      [(null?) (apply null? args)]
      [(assq) (apply assq args)]
      [(eq?) (apply eq? args)]
      [(equal?) (apply equal? args)]
      [(atom?) (apply atom? args)]
      [(length) (apply length args)]
      [(list->vector) (apply list->vector args)]
      [(list?) (apply list? args)]
      [(pair?) (apply pair? args)]
      [(procedure?) (if (= 1 (length args)) (proc-val? (car args)) (error 'apply-prim-proc "Incorrect number of arguments to procedure procedure?"))]
      [(vector->list) (apply vector->list args)]
      [(vector) (apply vector args)]
      [(vector-set!) (apply vector-set! args)]
      [(display) (apply display args)]
      [(newline) (apply newline args)]
      [(cadr) (apply cadr args)]
      [(cdar) (apply cdar args)]
      [(caar) (apply caar args)]
      [(cddr) (apply cddr args)]
      [(caaar) (apply caaar args)]
      [(caadr) (apply caadr args)]
      [(cadar) (apply cadar args)]
      [(cdaar) (apply cdaar args)]
      [(caddr) (apply caddr args)]
      [(cdadr) (apply cdadr args)]
      [(cddar) (apply cddar args)]
      [(cdddr) (apply cdddr args)]
      [else (error 'apply-prim-proc
            "Bad primitive procedure name: ~s"
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
