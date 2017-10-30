;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

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
    (sym (lambda (s) (or (boolean? s) (symbol? s))))
    (depth integer?)
    (position integer?)]

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
    (addr expression?)
    (body expression?)]

  [define-exp ; define expression
    (id symbol?)
    (body expression?)]

  [let-exp ; let expressions
    ; (vars (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]

  [let*-exp
    ; (vars (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]

  [letrec-exp
    ; (vars (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]

  [named-let-exp
    (name symbol?)
    ; (vars (list-of symbol?))
    (vals (list-of expression?))
    (bodies (list-of expression?))]

  [lambda-exp ; lambda expressions
    ; (ids (list-of (lambda (x) (or (symbol? x) (expression? x)))))
    (formals-by-reference? (list-of boolean?))
    (bodies (list-of expression?))]

  [reference-exp] ; reference expression for use in lambda formals

  [lambda-variable-exp
    (len-formals integer?)
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





; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
   (formals-by-reference (list-of boolean?))
   (bodies (list-of expression?))
   (env (list-of vector?))]
  [closure-variable ; TODO: make this work like the closure above
    (num-vars integer?)
    (bodies (list-of expression?))
    (env (list-of pair?))])

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
  (lambda (env depth position)
    (if (null? env)
      #f
      (if (zero? depth)
          (ref (car env) position)
          (apply-env-ref (cdr env) (sub1 depth) position)))))


(define apply-global-env-ref
  (lambda (sym)
    (let ([values (cdr global-env)]
          [symbols (car global-env)])
      (let ([pos (rib-find-position sym symbols)])
        (if (number? pos)
            (ref values pos)
            #f)))))


;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression
; types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
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
  (lambda (exp)
    (parse-lexical exp '())))

(define find-address
  (lambda (var scopes)
    (let helper ((var var) (scopes scopes) (d 0) (p 0))
      (cond
        ((null? scopes)
          (var-exp var -1 -1))
        ((null? (car scopes))
          (helper var (cdr scopes) (+ d 1) 0))
        ((eq? (caar scopes) var)
          (var-exp #f d p))
        (else
          (helper var (cons (cdar scopes) (cdr scopes)) d (+ p 1)))))))

(define snoc
  (lambda (thing ls)
    (append ls (list thing))))

(define parse-lexical
  (lambda (datum scopes)
    (cond

     [(symbol? datum)
      (find-address datum scopes)] ; var expression

     [(or (number? datum)
          (boolean? datum)
          (string? datum)
          (vector? datum))
      (lit-exp datum)] ; literal expression

     [(pair? datum)
      (cond


       [(eqv? (car datum) 'lambda) ; lambda expression
        (if (< (length datum) 3)
            (eopl:error 'parse-lexical "incorrect length in lambda expression ~s" datum))
        (cond
         [((list-of (lambda (x) (or (symbol? x) (eqv? 'ref (car x))))) (2nd datum))
          (lambda-exp (map (lambda (s) (not (symbol? s))) (2nd  datum))
                      (map (lambda (d) ; setting the bodies of the lambda-exp
                             (parse-lexical d (cons (map (lambda (s) ; map is here for ref
                                                           (if (symbol? s)
                                                               s
                                                               (cadr s)))
                                                         (2nd datum))
                                                    scopes)))
                           (cddr datum)))]

         [(or (symbol? (2nd datum)) ; lambda variable expression
              (improper-symbols? (2nd datum)))
          (lambda-variable-exp (length (to-proper (2nd datum)))
                               (map (lambda (d)
                                      (parse-lexical d (cons (to-proper (2nd datum))
                                                             scopes)))
                                       (cddr datum)))]

         [else
          (eopl:error 'parse-lexical "bad lambda expression: ~s" datum)])]

       [(eqv? 'or (car datum))
        (or-exp (map (lambda (d)
                       (parse-lexical d scopes))
                     (cdr datum)))]

       [(eqv? 'and (car datum))
        (and-exp (map (lambda (d)
                        (parse-lexical d scopes))
                      (cdr datum)))]

       [(eqv? (car datum) 'if) ; if expression
        (cond
         [(= 3 (length datum))
          (if-exp ; one-armed if expression
           (parse-lexical (2nd datum) scopes)
           (parse-lexical (3rd datum) scopes))]
         [(= 4 (length datum))
          (if-else-exp ; two-armed if expression
           (parse-lexical (2nd datum) scopes)
           (parse-lexical (3rd datum) scopes)
           (parse-lexical (4th datum) scopes))]
         [else
          (eopl:error 'parse-lexical "incorrect length in if expression: ~s" datum)])]

       [(eqv? 'begin (car datum))
        (begin-exp (map (lambda (d)
                          (parse-lexical d (cons '() scopes)))
                        (cdr datum)))]

       [(eqv? 'case (car datum)) ; case
        (let ((processed-case (process-case (cddr datum) '() '())))
          (case-exp (parse-lexical (cadr datum) scopes)
                    (car processed-case)
                    (map (lambda (list-of-bodies)
                           (map (lambda (d)
                                  (parse-lexical d scopes))
                                list-of-bodies))
                         (cadr processed-case))
                    (if (null? (caddr processed-case))
                        (list (parse-lexical '(void) scopes))
                        (map (lambda (d)
                               (parse-lexical d scopes))
                             (caddr processed-case)))))]


       [(eqv? 'cond (car datum)) ; cond
        (let ((processed-cond (process-cond (cdr datum) '() '())))
          (cond-exp (map (lambda (d)
                           (parse-lexical d scopes))
                         (car processed-cond))
                    (map (lambda (list-of-bodies)
                           (map (lambda (d)
                                  (parse-lexical d (cons '() scopes)))
                                list-of-bodies))
                         (cadr processed-cond))
                    (if (null? (caddr processed-cond))
                        (list (parse-lexical '(void) scopes))
                        (map (lambda (d)
                               (parse-lexical d (cons '() scopes)))
                             (caddr processed-cond)))))]

          [(eqv? (car datum) 'set!) ; set!
           (if (not (= 3 (length datum)))
               (eopl:error 'parse-lexical "incorrect length in set! expression: ~s" datum))
           (if (not (symbol? (2nd datum)))
               (eopl:error 'parse-lexical "must set a symbol in set! expression: ~s" datum))
           (set-exp (find-address (2nd datum) scopes) (parse-lexical (3rd datum) scopes))]

          [(eqv? (car datum) 'define) ; define
           (if (not (= 3 (length datum)))
               (eopl:error 'parse-lexival "incorrect length in define expression: ~s" datum))
           (if (not (symbol? (2nd datum)))
               (eopl:error 'parse-lexival "must set a symbol in define expression: ~s" datum))
           (define-exp (2nd datum) (parse-lexical (3rd datum) scopes))]

          [(eqv? (car datum) 'let) ; let family of expressions
           (cond
            [(< (length datum) 3)
             (eopl:error 'parse-lexical "too short let expression: ~s" datum)]

            [(symbol? (2nd datum)) ; named let
             (if (not (and (list? (3rd datum)) ; one body of cond
                           (andmap (lambda (x)
                                     (and (list? x) (= 2 (length x)) (symbol? (car x)))) (3rd datum))))
                 (eopl:error 'parse-lexical "bad let bindings in expression: ~s" datum))
             (named-let-exp ; returning a named-let expression (2nd body of cond)
              (2nd datum)
              (map (lambda (x) (parse-lexical (cadr x)
                                              scopes))
                   (3rd datum))
              (map (lambda (d) (parse-lexical d (cons (map car (3rd datum))
                                                      (cons (list (2nd datum)) scopes))))
                   (cdddr datum)))]

            [else ; normal let
             (if (not (and
                       (list? (2nd datum))
                       (andmap (lambda (x)
                                 (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
                 (eopl:error 'parse-lexical "bad let bindings in expression: ~s" datum))
             (let-exp ; returns a let-expression
              (map (lambda (x) (parse-lexical (cadr x) scopes)) (2nd datum))
              (map (lambda (d)
                     (parse-lexical d (cons (map car (2nd datum))
                                            scopes)))
                   (cddr datum)))])]

          [(eqv? (car datum) 'let*) ; let* expression
           (if (< (length datum) 3)
               (eopl:error 'parse-lexical "too short let expression: ~s" datum))
           (if (not (and (list? (2nd datum))
                         (andmap (lambda (x)
                                   (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
               (eopl:error 'parse-lexical "bad let bindings in expression: ~s" datum))
           (let ((let*-scopes scopes))
             (let ((values (fold-left (lambda (so-far next)
                                        (let ((vals (snoc (parse-lexical (cadr next) let*-scopes) so-far)))
                                          (set! let*-scopes (cons (list (car next)) let*-scopes))
                                          vals))
                                      '()
                                      (2nd datum))))
               (let*-exp
                values
                (map (lambda (d)
                       (parse-lexical d let*-scopes))
                     (cddr datum)))))]

          [(eqv? (car datum) 'letrec) ; letrec expression
           (if (< (length datum) 3)
               (eopl:error 'parse-lexical "too short let expression: ~s" datum))
           (if (not (and
                     (list? (2nd datum))
                     (andmap (lambda (x)
                               (and (list? x) (= 2 (length x)) (symbol? (car x)))) (2nd datum))))
               (eopl:error 'parse-lexical "bad let bindings in expression: ~s" datum))

           (let ((letrec-scopes (cons (map car (2nd datum))
                                      scopes)))
             (letrec-exp
              (map (lambda (x) (parse-lexical (cadr x) letrec-scopes))
                   (2nd datum))
              (map (lambda (d) (parse-lexical d letrec-scopes))
                   (cddr datum))))]

          [(eqv? (car datum) 'while)
            (while-exp
              (parse-lexical (2nd datum) scopes)
              (map (lambda (d) (parse-lexical d scopes))
                   (cddr datum)))]

          [(eq? (car datum) 'quote) ; literal expression
            (lit-exp (cadr datum))]

          [else ; application expression
            (if (not (list? (cdr datum)))
              (eopl:error 'parse-lexical "bad argument list in application: ~s" datum))
            (app-exp (parse-lexical (1st datum) scopes)
                     (map (lambda (d) (parse-lexical d scopes))
                          (cdr datum)))])]

     [else (eopl:error 'parse-lexical "bad expression: ~s" datum)])))







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


(define extend-env ; takes VALUES and not expressions
  (lambda (values env)
    (cons (list->vector values)
          env)))

(define extend-env-recursively ; takes EXPRESSIONS and not values
  (lambda (expressions env)
    (let* ((len (length expressions))
           (new-env (extend-env (make-list len 'this-should-go-away) env))
           (vec (car new-env)))
      (for-each
       (lambda (pos exp)
         (vector-set! vec
                      pos
                      (eval-exp exp new-env)))
       (iota len)
       expressions)
      new-env)))

(define apply-env
  (lambda (env depth position)
    (if (zero? depth)
        (vector-ref (car env) position)
        (apply-env (cdr env) (sub1 depth) position))))


; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

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








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+


(define syntax-expand
  (lambda (parsed-exp)
    (cases expression parsed-exp

           [or-exp (bodies)
                   (if (null? bodies)
                       (lit-exp #f)
                       (syntax-expand (let-exp
                                       (list (car bodies)) ; if true, refer to the let variable
                                       (list (if-else-exp (var-exp #f 0 0) ; we've just created
                                                          (var-exp #f 0 0)
                                                          (or-exp (cdr bodies)))))))]

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

           [set-exp (addr body)
                    (set-exp addr
                             (syntax-expand body))]

           [define-exp (id body)
                    (define-exp id
                             (syntax-expand body))]

           [let-exp (vals bodies)
                    (app-exp
                     (lambda-exp (make-list (length vals) #f) (map syntax-expand bodies))
                     (map syntax-expand vals))]

           [letrec-exp (vals bodies)
                       (letrec-exp
                                   (map syntax-expand vals)
                                   (map syntax-expand bodies))]

           [let*-exp (vals bodies)
                     (syntax-expand (let-exp
                                             (list (car vals))
                                             (if (null? (cdr vals))
                                                 bodies
                                                 (list (let*-exp
                                                                 (cdr vals)
                                                                 bodies)))))]

           [named-let-exp (name vals bodies)
                          (syntax-expand (app-exp
                                          (letrec-exp
                                                      (list (lambda-exp (make-list (length vals) #f) bodies))
                                                      (list (var-exp #f 0 0)))
                                          vals))]


           [while-exp (test bodies)
                      (while-exp (syntax-expand test)
                                 (map syntax-expand bodies))]

           [lambda-exp (reference-formals? bodies)
                       (lambda-exp reference-formals?
                                   (map syntax-expand bodies))]

           [lambda-variable-exp (ids bodies)
                                (lambda-variable-exp ids
                                                     (map syntax-expand bodies))]

           [app-exp (rator rands)
                    (app-exp (syntax-expand rator)
                             (map syntax-expand rands))]

           [else parsed-exp]

           )))







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
; evaluates an expression

(define eval-exp
  (let ((identity-proc (lambda (x) x)))
    (lambda (exp env)
        (cases expression exp
               [lit-exp (datum) datum]

               [if-exp (conditional-exp then-exp)
                (if (eval-exp conditional-exp env)
                  (eval-exp then-exp env))]

               [if-else-exp (conditional-exp then-exp else-exp)
                (if (eval-exp conditional-exp env)
                  (eval-exp then-exp env)
                  (eval-exp else-exp env))]

               [set-exp (addr body)
                        (set-ref! (cases expression addr
                                    (var-exp (sym depth pos)
                                             (if sym
                                                 (apply-global-env-ref sym)
                                                 (apply-env-ref env depth pos)))
                                    (else (eopl:error 'eval-exp-set-exp "wtf")))
                                  (eval-exp body env))]

               [define-exp (id body)
                 (let ((r (apply-global-env-ref id)))
                      (if r
                          (set-ref! r (eval-exp body env))
                          (set! global-env
                                    (cons (cons id
                                                (car global-env))
                                          (list->vector (cons (eval-exp body
                                                                        env)
                                                              (vector->list (cdr global-env))))))))]

               [lambda-exp (reference-formals? bodies)
                           (closure reference-formals? bodies env)]

               [lambda-variable-exp (vars bodies)
                (closure-variable vars bodies env)]

               [letrec-exp (vals bodies)
                (let ((new-env (extend-env-recursively vals env)))
                  (eval-bodies bodies new-env))]

               [while-exp (test bodies)
                          (if (eval-exp test env)
                              (begin (eval-bodies bodies env) (eval-exp exp env)))]

               [var-exp (sym depth position)
                        (if sym
                            (apply-global-env sym)
                            (apply-env env depth position))]

               [app-exp (rator rands)
                        (let* ([proc-value (eval-exp rator env)]
                               [args (cases proc-val proc-value
                                            (prim-proc (name) (eval-rands rands env))
                                            (closure (reference-formals? bodies closure-env)
                                                     (map (lambda (reference-formal? arg index)
                                                            (if reference-formal?
                                                                (cases expression arg
                                                                  (var-exp (sym depth pos)
                                                                           (if sym
                                                                               (apply-global-env-ref sym)
                                                                               (apply-env-ref env depth pos)))
                                                                  (else (eopl:error 'eval-exp-app-exp "wtf")))
                                                                (eval-exp arg env)))
                                                            reference-formals? rands (iota (length rands))))
                                            (closure-variable (vars bodies env)
                                                              (eval-rands rands env)))])
                          (apply-proc proc-value args))]

               [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)]))))


; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands env)
    (map (lambda (exp) (eval-exp exp env)) rands)))


; evalute a list of expressions in order, returning the last

(define eval-bodies
  (lambda (bodies env)
    (if (null? (cdr bodies))
      (eval-exp (car bodies) env)
      (begin (eval-exp (car bodies) env)
        (eval-bodies (cdr bodies) env)))))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [closure (reference-formals? bodies env)
               (let* ([identity-proc (lambda (v) v)]
                      [values (map (lambda (reference-formal? arg) (if reference-formal?
                                                                        (deref arg)
                                                                        arg))
                                   reference-formals? args)]
                      [new-env (extend-env values env)]
                      [result (eval-bodies bodies new-env)])
                     (for-each (lambda (reference-formal? arg value index)
                                       (when reference-formal?
                                           (set-ref! arg (apply-env new-env 0 index))))
                               reference-formals? args values (iota (length args)))
                     result)]
      [closure-variable (num-symbols bodies env)
        (eval-bodies bodies (extend-env
                             (convert-variable-args num-symbols args)
                              env))]
      ; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s"
                    proc-value)])))

(define to-proper
  (lambda (symbols)
    (if (symbol? symbols)
      (list symbols)
      (cons (car symbols) (to-proper (cdr symbols))))))

(define convert-variable-args
  (lambda (num-symbols args)
    (if (= 1 num-symbols)
      (list args)
      (cons (car args) (convert-variable-args (sub1 num-symbols) (cdr args))))))

; Usually an interpreter must define each
; built-in procedure individually.  We are "cheating" a little bit.

(define *prim-proc-names* '(+ - * / quotient add1 sub1 zero? = < <= > >= not cons car cdr
                              list null? assq eq? equal? atom? length list->vector list? pair? map apply
                              procedure? vector->list vector vector-set! display newline cadr cdar caar cddr
                              caaar caadr cadar cdaar caddr cdadr cddar cdddr make-vector vector-ref set-car!
                              set-cdr! vector? number? symbol? exit void member? append eqv? list-tail))

(define global-env
  (cons *prim-proc-names*
        (list->vector (map prim-proc
                           *prim-proc-names*))))


        ;;(let ([symbols (caar env)]
              ;;[values (cdar env)]
              ;;[enclosing-env (cdr env)])
          ;;(let ([pos (rib-find-position symbol symbols)])
            ;;(if (number? pos)
                ;;(success (vector-ref values pos))
                ;;(apply-env enclosing-env symbol success fail)))))))

(define reset-global-env
  (lambda ()
    (set! global-env
      (cons *prim-proc-names*
            (list->vector (map prim-proc
                               *prim-proc-names*))))))

(define apply-global-env
  (lambda (sym)
    (let ([symbols (car global-env)]
          [values (cdr global-env)])
      (let ([pos (rib-find-position sym symbols)])
        (if (number? pos)
            (vector-ref values pos)
            (eopl:error 'apply-global-env "Symbol ~s not in global environment" sym))))))



(define apply-prim-proc
  (lambda (prim-proc args)
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
      [(map) (apply map (lambda col-of-args
                    (apply-proc (car args) col-of-args)) (cdr args))]
      [(apply) (apply-proc (car args) (flatten (cdr args)))]
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



(display "13-test")(newline)(load "13-test.ss")(r)
(display "14-test")(newline)(load "14-test.ss")(r)
(display "16-test")(newline)(load "16-test.ss")(r)
(display "17-test")(newline)(load "17-test.ss")(r)
