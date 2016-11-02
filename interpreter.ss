
;;  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;;-------------------+
;;                   |
;;    DATATYPES      |
;;                   |
;;-------------------+

;; parsed expression

(define (improper? x)
  (and (pair? x) (not (list? (cdr x)))))


(define (improper-symbols? x)
  (if (pair? x)
      (if (pair? (cdr x))
          (and (symbol? (car x)) (improper-symbols? (cdr x)))
          (and (symbol? (car x)) (symbol? (cdr x))))
      #f))


(define literal?
  (lambda (x)
    (ormap
     (lambda (pred) (pred x))
     (list number? vector? boolean? symbol? string? pair? null?))))


(define-datatype expression expression?

  [var-exp ; var expression
   (id symbol?)]

  [lit-exp ; literal expression
   (val literal?)]

  [if-exp ; if expressions
   (conditional expression?)
   (body expression?)]

  [if-else-exp
   (conditional expression?)
   (body expression?)
   (fallback expression?)]

  [set-exp ; set expression
   (id symbol?)
   (body expression?)]

  [define-exp ; define expression
    (id symbol?)
    (body expression?)]

  [let-exp ; let expressions
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]

  [let*-exp
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]

  [letrec-exp
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]

  [named-let-exp
   (name symbol?)
   (vars (list-of symbol?))
   (vals (list-of expression?))
   (bodies (list-of expression?))]

  [lambda-exp ; lambda expressions
   (ids (list-of symbol?))
   (bodies (list-of expression?))]

  [lambda-variable-exp
   (ids (lambda (x) (or (symbol? x) (improper? x))))
   (bodies (list-of expression?))]

  [app-exp ; application expression
   (rator expression?)
   (rands (list-of expression?))]

  [begin-exp ; begin
   (bodies (list-of expression?))]

  [cond-exp ; cond
   (conditionals (list-of expression?))
   (bodies (list-of (list-of expression?)))
   (else-exp (list-of expression?))]

  [and-exp ; and
   (bodies (list-of expression?))]

  [or-exp ; or
   (bodies (list-of expression?))]

  [case-exp ; a nightmare
   (exp expression?)
   (keys (list-of (list-of (lambda (x) (or (number? x) (symbol? x))))))
   (results (list-of (list-of expression?)))
   (else-result (list-of expression?))]

  [while-exp
   (condition expression?)
   (bodies (list-of expression?))])





;; datatype for procedures.  At first there is only one
;; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (vars (list-of symbol?))
   (bodies (list-of expression?))
   (env environment?)]
  [closure-variable
   (vars (lambda (x) (or (symbol? x) (improper? x))))
   (bodies (list-of expression?))
   (env environment?)])


(define-datatype reference reference?
  [ref
   (vector vector?)
   (index integer?)])


(define deref
  (lambda (r)
    (cases reference r
           [ref (vec i)
                (vector-ref vec i)])))


(define set-ref!
  (lambda (r val)
    (cases reference r
           [ref (vec i)
                (vector-set! vec i val)])))


(define apply-env-ref
  (lambda (env symbol success fail)
    (if (null? env)
        (fail)
        (let ([symbols (caar env)]
              [values (cdar env)]
              [enclosing-env (cdr env)])
          (let ([pos (rib-find-position symbol symbols)])
            (if (number? pos)
                (success (ref values pos))
                (apply-env-ref enclosing-env symbol success fail)))))))




;;-------------------+
;;                   |
;;    PARSER         |
;;                   |
;;-------------------+


;; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

;; You will want to replace this with your parser that includes more expression
;; types, more options for these types, and error-checking.

;; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)


(define process-cond
  (lambda (datum conditionals list-of-bodies)
    (cond
     [(null? datum)
      (list (reverse conditionals) (reverse list-of-bodies) '())]
     [(eqv? 'else (caar datum))
      (list (reverse conditionals) (reverse list-of-bodies) (cdar datum))]
     [else
      (process-cond (cdr datum)
                    (cons (caar datum) conditionals)
                    (cons (cdar datum) list-of-bodies))])))


(define process-case process-cond)


(define parse-exp
  (lambda (datum)
    (cond

     [(symbol? datum)
      (var-exp datum)] ; var expression

     [(or (number? datum)
          (boolean? datum)
          (string? datum)
          (vector? datum))
      (lit-exp datum)] ; literal expression

     [(pair? datum)
      (cond
       [(eqv? (car datum) 'lambda) ; lambda expression
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

       [(eqv? 'or (car datum))
        (or-exp (map parse-exp (cdr datum)))]

       [(eqv? 'and (car datum))
        (and-exp (map parse-exp (cdr datum)))]

       [(eqv? (car datum) 'if) ; if expression
        (cond
         [(= 3 (length datum))
          (if-exp ; one-armed if expression
           (parse-exp (2nd datum))
           (parse-exp (3rd datum)))]
         [(= 4 (length datum))
          (if-else-exp ; two-armed if expression
           (parse-exp (2nd datum))
           (parse-exp (3rd datum))
           (parse-exp (4th datum)))]
         [else
          (eopl:error 'parse-exp "incorrect length in if expression: ~s" datum)])]

       [(eqv? 'begin (car datum))
        (begin-exp (map parse-exp (cdr datum)))]

       ;; TODO FIX THIS
       [(eqv? 'case (car datum)) ; case
        (let ((processed-case (process-case (cddr datum) '() '())))
          (case-exp (parse-exp (cadr datum))
                    (car processed-case)
                    (map (lambda (list-of-bodies)
                           (map parse-exp list-of-bodies))
                         (cadr processed-case))
                    (if (null? (caddr processed-case))
                        (list (parse-exp '(void)))
                        (map parse-exp (caddr processed-case)))))]


       [(eqv? 'cond (car datum)) ; cond
        (let ((processed-cond (process-cond (cdr datum) '() '())))
          (cond-exp (map parse-exp (car processed-cond))
                    (map (lambda (list-of-bodies)
                           (map parse-exp list-of-bodies))
                         (cadr processed-cond))
                    (if (null? (caddr processed-cond))
                        (list (parse-exp '(void)))
                        (map parse-exp (caddr processed-cond)))))]

       [(eqv? (car datum) 'set!) ; set!
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp "incorrect length in set! expression: ~s" datum))
        (if (not (symbol? (2nd datum)))
            (eopl:error 'parse-exp "must set a symbol in set! expression: ~s" datum))
        (set-exp (2nd datum) (parse-exp (3rd datum)))]

       [(eqv? (car datum) 'define) ; define
        (if (not (= 3 (length datum)))
            (eopl:error 'parse-exp "incorrect length in define expression: ~s" datum))
        (if (not (symbol? (2nd datum)))
            (eopl:error 'parse-exp "must set a symbol in define expression: ~s" datum))
        (define-exp (2nd datum) (parse-exp (3rd datum)))]

       [(eqv? (car datum) 'let) ; let expression
        (cond
         [(< (length datum) 3)
          (eopl:error 'parse-exp "too short let expression: ~s" datum)]
         [(symbol? (2nd datum)) ; named let
          (if (not (and
                    (list? (3rd datum))
                    (andmap (lambda (x)
                              (and (list? x) (= 2 (length x)) (symbol? (car x)))) (3rd datum))))
              (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
          (named-let-exp ; returning a named-let expression
           (2nd datum)
           (map car (3rd datum))
           (map (lambda (x) (parse-exp (cadr x))) (3rd datum))
           (map parse-exp (cdddr datum)))]
         [else ; normal let
          (if (not (and
                    (list? (2nd datum))
                    (andmap (lambda (x)
                              (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
              (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
          (let-exp ; returns a let-expression
           (map car (2nd datum))
           (map (lambda (x) (parse-exp (cadr x))) (2nd datum))
           (map parse-exp (cddr datum)))])]

       [(eqv? (car datum) 'let*) ; let* expression
        (if (< (length datum) 3)
            (eopl:error 'parse-exp "too short let expression: ~s" datum))
        (if (not (and
                  (list? (2nd datum))
                  (andmap (lambda (x)
                            (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
            (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
        (let*-exp
         (map car (2nd datum))
         (map (lambda (x) (parse-exp (cadr x))) (2nd datum))
         (map parse-exp (cddr datum)))]

       [(eqv? (car datum) 'letrec) ; letrec expression
        (if (< (length datum) 3)
            (eopl:error 'parse-exp "too short let expression: ~s" datum))
        (if (not (and
                  (list? (2nd datum))
                  (andmap (lambda (x)
                            (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
            (eopl:error 'parse-exp "bad let bindings in expression: ~s" datum))
        (letrec-exp
         (map car (2nd datum))
         (map (lambda (x) (parse-exp (cadr x))) (2nd datum))
         (map parse-exp (cddr datum)))]

       [(eqv? (car datum) 'while)
        (while-exp
         (parse-exp (2nd datum))
         (map parse-exp (cddr datum)))]

       [(eq? (car datum) 'quote) ; literal expression
        (lit-exp (cadr datum))]

       [else ; application expression
        (if (not (list? (cdr datum)))
            (eopl:error 'parse-exp "bad argument list in application: ~s" datum))
        (app-exp (parse-exp (1st datum))
                 (map parse-exp (cdr datum)))])]

     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))







;;-------------------+
;;                   |
;;   ENVIRONMENTS    |
;;                   |
;;-------------------+


;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define environment? (list-of pair?))

(define empty-env
  (lambda ()
    '()))


(define extend-env
  (lambda (symbols values env)
    (cons (cons symbols
                (list->vector values))
          env)))


(define extend-env-recursively
  (lambda (symbols expressions env)
    (let* ((len (length symbols))
           (new-env (extend-env symbols (make-list len 'this-should-go-away) env))
           (vec (cdar new-env)))
      (for-each
       (lambda (pos exp)
         (vector-set! vec
                      pos
                      (eval-exp exp new-env)))
       (iota len)
       expressions)
      new-env)))


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


;; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

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








;;-----------------------+
;;                       |
;;   SYNTAX EXPANSION    |
;;                       |
;;-----------------------+


(define syntax-expand
  (lambda (parsed-exp)
    (cases expression parsed-exp

           [or-exp (bodies)
                   (if (null? bodies)
                       (lit-exp #f)
                       (let ((sym (gensym)))
                         (syntax-expand (let-exp (list sym)
                                                 (list (car bodies))
                                                 (list (if-else-exp (var-exp sym)
                                                                    (var-exp sym)
                                                                    (or-exp (cdr bodies))))))))]

           [and-exp (bodies)
                    (if (null? bodies)
                        (lit-exp #t)
                        (syntax-expand (if-else-exp (car bodies)
                                                    (if (null? (cdr bodies))
                                                        (car bodies)
                                                        (and-exp (cdr bodies)))
                                                    (car bodies))))]

           [if-exp (conditional body)
                   (if-exp (syntax-expand conditional)
                           (syntax-expand body))]

           [if-else-exp (conditional then-body else-body)
                        (if-else-exp (syntax-expand conditional)
                                     (syntax-expand then-body)
                                     (syntax-expand else-body))]

           [begin-exp (bodies)
                      (syntax-expand (app-exp (lambda-exp '() bodies) '()))]

           [case-exp (exp list-of-keys list-of-bodies else-exps)
                     (syntax-expand
                      (if (null? list-of-keys)
                          (begin-exp else-exps)
                          (if-else-exp (app-exp (var-exp 'member?) (list exp (lit-exp (car list-of-keys))))
                                       (begin-exp (car list-of-bodies))
                                       (case-exp exp
                                                 (cdr list-of-keys)
                                                 (cdr list-of-bodies)
                                                 else-exps))))]



           [cond-exp (conditionals list-of-bodies else-exps)
                     (syntax-expand
                      (if (null? conditionals)
                          (begin-exp else-exps)
                          (if-else-exp (car conditionals)
                                       (begin-exp (car list-of-bodies))
                                       (cond-exp (cdr conditionals)
                                                 (cdr list-of-bodies)
                                                 else-exps))))]

           [set-exp (id body)
                    (set-exp id
                             (syntax-expand body))]

           [define-exp (id body)
             (define-exp id
               (syntax-expand body))]

           [let-exp (vars vals bodies)
                    (app-exp
                     (lambda-exp vars (map syntax-expand bodies))
                     (map syntax-expand vals))]

           [letrec-exp (vars vals bodies)
                       (letrec-exp vars
                                   (map syntax-expand vals)
                                   (map syntax-expand bodies))]

           [let*-exp (vars vals bodies)
                     (syntax-expand (let-exp (list (car vars))
                                             (list (car vals))
                                             (if (null? (cdr vars))
                                                 bodies
                                                 (list (let*-exp (cdr vars)
                                                                 (cdr vals)
                                                                 bodies)))))]

           [named-let-exp (name vars vals bodies)
                          (syntax-expand (app-exp
                                          (letrec-exp (list name)
                                                      (list (lambda-exp vars bodies))
                                                      (list (var-exp name)))
                                          vals))]


           [while-exp (test bodies)
                      (while-exp (syntax-expand test)
                                 (map syntax-expand bodies))]

           [lambda-exp (ids bodies)
                       (lambda-exp ids
                                   (map syntax-expand bodies))]

           [lambda-variable-exp (ids bodies)
                                (lambda-variable-exp ids
                                                     (map syntax-expand bodies))]

           [app-exp (rator rands)
                    (app-exp (syntax-expand rator)
                             (map syntax-expand rands))]

           [else parsed-exp]

           )))







;;-------------------+
;;                   |
;;   INTERPRETER     |
;;                   |
;;-------------------+


;; will need to change
(define apply-k
  (trace-lambda a-k (k v)
    (cases continuation k
      [identity-k () v]
      [one-armed-test-k (then-exp env k)
                        (if v (eval-exp then-exp env k))]
      [test-k (then-exp else-exp env k) 
              (eval-exp (if v then-exp else-exp)
                        env
                        k)]
      [bodies-k (remaining-bodies env k)
                (if (null? remaining-bodies)
                    (apply-k k v)
                    (eval-bodies remaining-bodies env k))]
      [while-k (bodies test env k)
               (if v
                   (eval-bodies bodies
                                env
                                (eval-exp test
                                          env
                                          (while-k bodies test env k)))
                   (apply-k k (void)))]
      [rator-k (rands env k)
               (eval-rands rands
                           env
                           (rands-k v k))]

      [rands-k (proc k)
               (apply-proc proc v k)]
      [map-k (proc cdr-of-list k)
             (map-cps proc
                      cdr-of-list
                      (cons-k v k))]
      [cons-k (first k)
              (apply-k k (cons first v))]


)))


(define-datatype continuation continuation?
  [identity-k]
  [one-armed-test-k (then-exp expression?)
                    (env environment?)
                    (k continuation?)]
  [test-k (then-exp expression?)
          (else-exp expression?)
          (env environment?)
          (k continuation?)]
  [bodies-k (remaining-bodies (list-of expression?))
            (env environment?)
            (k continuation?)]
  [while-k (bodies (list-of expression?))
           (test expression?)
           (env environment?)
           (k continuation?)]
  [rator-k (rands (list-of expression?))
           (env environment?)
           (k continuation?)]
  [rands-k (proc-value scheme-value?)
           (k continuation?)]
  [map-k (proc procedure?)
         (cdr-of-list list?)
         (k continuation?)]
  [cons-k (first scheme-value?)
          (k continuation?)])


;; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ;; later we may add things that are not expressions.
    (eval-exp form (empty-env) (identity-k))))


;; eval-exp is the main component of the interpreter
;; evaluates an expression

(define eval-exp
  (let ((identity-proc (lambda (x) x)))
    (lambda (exp env k)
      (cases expression exp
             [lit-exp (datum) (apply-k k datum)]
             [if-exp (conditional-exp then-exp)
                     (eval-exp conditional-exp
                               env
                               (one-armed-test-k then-exp env k))]
             [if-else-exp (conditional-exp then-exp else-exp)
                          (eval-exp conditional-exp 
                                    env
                                    (test-k then-exp else-exp env k))]
             ; todo: continuation-ify
             [set-exp (id body)
                      (set-ref! (apply-env-ref env id
                                               identity-proc
                                               (lambda ()
                                                 (apply-env-ref global-env id
                                                                identity-proc
                                                                (lambda () (eopl:error
                                                                            'apply-env
                                                                            "variable not found in environment: ~s"
                                                                            id)))))
                                (eval-exp body env))]
             ; todo: continuation-ify
             [define-exp (id body)
               (apply-env-ref global-env id
                              (lambda (r) (set-ref! r (eval-exp body env)))
                             (lambda ()
                                (set! global-env (extend-env (list id) (list (eval-exp body env)) global-env))))]

             [lambda-exp (vars bodies)
                         (apply-k (closure vars bodies env) k)]

             [lambda-variable-exp (vars bodies)
                                  (apply-k (closure-variable vars bodies env) k)]

             [letrec-exp (vars vals bodies)
                         (let ((new-env (extend-env-recursively vars vals env)))
                           (eval-bodies bodies new-env k))]

             [while-exp (test bodies)
                        (eval-exp test
                                  env
                                  (while-k bodies
                                           test
                                           env
                                           k))]

             [var-exp (id)
                      (apply-k k (apply-env env id ; look up its value.
                                            identity-proc ; procedure to call if id is in the environment
                                            (lambda ()
                                              (apply-env global-env id
                                                         identity-proc
                                                         (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
                                                                                "variable not found in environment: ~s" id))))))]

             [app-exp (rator rands)
                      (eval-exp rator
                                env
                                (rator-k rands env k))]

             [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))


;; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env k)
          (map-cps (lambda (exp k) (eval-exp exp env k)) rands)))


(define map-cps
  (trace-lambda map-c (cps-proc ls k)
    (if (null? ls)
        (apply-k k '())
        (cps-proc (car ls)
                  (map-k cps-proc (cdr ls) k)))))

;; evalute a list of expressions in order, returning the last

(define eval-bodies
  (lambda (bodies env k)
        (eval-exp (car bodies)
                  env
                  (bodies-k (cdr bodies) env k))))



;; Apply a procedure to its arguments.
;; expressions given as arguments are resolved to values here

(define apply-proc
  (lambda (proc-value args k)
    (cases proc-val proc-value
           [prim-proc (op) (apply-prim-proc op args k)]
           [closure (symbols bodies env)
                    (eval-bodies bodies (extend-env symbols args env) k)]
           [closure-variable (symbols bodies env)
                             (eval-bodies bodies 
                                          (extend-env
                                                  (to-proper symbols)
                                                  (convert-variable-args symbols args)
                                                  env)
                                          k)]
           ;; You will add other cases
           [else (eopl:error 'apply-proc
                             "Attempt to apply bad procedure: ~s"
                             proc-value)])))


(define to-proper
  (lambda (symbols)
    (if (symbol? symbols)
        (list symbols)
        (cons (car symbols) (to-proper (cdr symbols))))))


(define convert-variable-args
  (lambda (symbols args)
    (if (symbol? symbols)
        (list args)
        (cons (car args) (convert-variable-args (cdr symbols) (cdr args))))))


;; procedure names which will be evaluated by apply-prim-proc
(define *prim-proc-names* '(+ - * / quotient add1 sub1 zero? = < <= > >= not cons car cdr
                              list null? assq eq? equal? atom? length list->vector list? pair? map apply
                              procedure? vector->list vector vector-set! display newline cadr cdar caar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr make-vector vector-ref set-car!
                              set-cdr! vector? number? symbol? exit void member? append eqv? list-tail printf))


(define global-env
  (extend-env
   *prim-proc-names*
   (map prim-proc
        *prim-proc-names*)
   (empty-env)))


(define reset-global-env
  (lambda () (set! global-env (extend-env
                               *prim-proc-names*
                               (map prim-proc
                                    *prim-proc-names*)
                               (empty-env)))))


;; args have been evaluated by this point
(define apply-prim-proc
  (lambda (prim-proc args)
    (apply-k k 
    (case prim-proc
      [(exit) (error 'exit "Exiting interpreter")]
      [(void) (apply void args)]
      [(+) (apply + args)] ; numerical procedures
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(quotient) (apply quotient args)]
      [(add1) (apply add1 args)]
      [(sub1) (apply sub1 args)]
      [(=) (apply = args)]
      [(<) (apply < args)]
      [(<=) (apply <= args)]
      [(>) (apply > args)]
      [(>=) (apply >= args)]
      [(not) (apply not args)]
      [(cons) (apply cons args)] ; list procedures
      [(list) (apply list args)]
      [(append) (apply append args)]
      [(list-tail) (apply list-tail args)]
      [(assq) (apply assq args)]
      [(length) (apply length args)]
      [(list->vector) (apply list->vector args)] ; vector stuff
      [(make-vector) (apply make-vector args)]
      [(vector-ref) (apply vector-ref args)]
      [(vector->list) (apply vector->list args)]
      [(vector) (apply vector args)]
      [(vector?) (apply vector? args)] ; predicates
      [(number?) (apply number? args)]
      [(symbol?) (apply symbol? args)]
      [(zero?) (apply zero? args)]
      [(null?) (apply null? args)]
      [(atom?) (apply atom? args)]
      [(procedure?) (if (= 1 (length args))
                        (proc-val? (car args))
                        (error 'apply-prim-proc "Incorrect number of arguments to procedure procedure?"))]
      [(map) (map-cps (lambda (arg map-k)
                          (apply-proc (car args) arg) map-k) (cadr args) k)]
      [(apply) (apply-proc (car args) (flatten (cdr args)) k)]
      [(list?) (apply list? args)]
      [(pair?) (apply pair? args)]
      [(eq?) (apply eq? args)]
      [(eqv?) (apply eqv? args)]
      [(equal?) (apply equal? args)]
      [(member?) (not (not (apply member args)))]
      [(car) (apply car args)] ; car/cdr procedures
      [(cdr) (apply cdr args)]
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
      [(vector-set!) (apply vector-set! args)] ; mutation procedures
      [(set-car!) (apply set-car! args)]
      [(set-cdr!) (apply set-cdr! args)]
      [(display) (apply display args)] ; printing procedures
      [(newline) (apply newline args)]
      [(printf) (apply printf args)]
      [else (error 'apply-prim-proc
                   "Bad primitive procedure name: ~s"
                   prim-proc)])))


(define flatten
  (lambda (ls)
    (cond
     [(null? ls) '()]
     [(null? (cdr ls)) (car ls)]
     [else (cons (car ls) (flatten (cdr ls)))])))


(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      (cond
       [(eq? (void) answer)
        (newline)]
       [(proc-val? answer)
        (cases proc-val answer
               [prim-proc (op)
                          (display "#<procedure ") (display op) (display ">")
                          (newline) (newline)]
               [else
                (display "#<procedure>") (newline) (newline)])]
       [else (eopl:pretty-print answer) (newline)])
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))

; (load "14-test.ss")(r)
; (load "16-test.ss")(r)
; (load "17-test.ss")(r)
