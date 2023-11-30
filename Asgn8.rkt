#lang typed/racket

(require typed/rackunit)

; Full Project Implemented

#|
============================================================
|#

;; Values

; output data type
(define-type Value (U Real Boolean CloV PrimV String))

; closures
(struct CloV ([params : (Listof Symbol)]
              [num-params : Natural]
              [body : ExprC]
              [env : Env]) #:transparent)

; primitives
(struct PrimV ([op : (-> (Listof Value) Real Value)])#:transparent)


; real numbers
(struct NumC ([n : Real]) #:transparent)

;; Expressions

; defines all types of expressions that the interpeter can evaluate
(define-type ExprC (U NumC IdC LamC AppC IfC StrC))

; bindings: names that can be substituted for other expressions
(struct IdC ([s : Symbol])  #:transparent)

; lambda expressions
(struct LamC ([params : (Listof Symbol)]
              [types : (Listof Type)]
              [num-params : Natural]
              [body : ExprC])  #:transparent)

; function applications: names and arguments that can be passed into functions and evaluated
(struct AppC ([fun : ExprC]
              [arglist : (Listof ExprC)]
              [num-args : Natural])  #:transparent)

; if less than 0: basic if statement, checks if test expression is <= 0
; if it is interpeter evaluates expression 'then,' otherwise it evaluates 'else'
(struct IfC ([test : ExprC]
             [then : ExprC]
             [else : ExprC]) #:transparent)

; expression type that handles strings
(struct StrC ([str : String]) #:transparent)


;; Environment

; binds a symbol to a value
(struct Binding ((name : Symbol) (val : Value)) #:transparent)

; Environment is a list of bindings
(define-type Env (Listof Binding))

;; Types

(define-type Type (U NumT StrT BoolT FuncT))

(struct NumT()#:transparent)
(struct StrT()#:transparent)
(struct BoolT()#:transparent)
(struct FuncT([args : (Listof Type)]
             [ret : Type]) #:transparent)

;; Type Environment

(struct Type-Map ([id : Symbol]
                  [ty : Type]))

(define-type Type-Env (Listof Type-Map))


#|
============================================================
|#

;; Interpreter Functions

; top-level function, runs a PAIG program given a list 
; of function s-expressions
(define (top-interp [s : Sexp]) : String
  (serialize (interp (parse s) top-env)))

; evaluates an AST substituting in functions as needed
(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(NumC n) n]
    [(StrC s) s]
    [(IdC n) (lookup n env)]
    [(LamC p t n b) (CloV p n b env)]
    [(AppC f a n)
     (define fd (interp f env))
     (define arg-values (for/list : (Listof Value) ([arg a]) (interp arg env)))
     (match fd
       [(PrimV p) (p arg-values n)]
       [(CloV c-params c-n c-body c-env)
        (cond
          [(= n c-n)
           (interp c-body
                  (extend-env arg-values c-params c-env))]
          [else (paig-error 'ArityError 'interp (format "Incorrect Number of Funtion Arguments: ~e" e))])]
       [other (paig-error 'TypeError 'interp (format "Non-Function ~e Passed In Function Application: ~e" fd e))])]
    [(IfC test then else)
     (match (interp test env)
       [(? boolean? b)
        (if b (interp then env) (interp else env))]
       [other (paig-error 'TypeError 'interp (format "Non-Boolean Used as Condition in If Statement: ~e" e))])]))


; returns a string representation of a PAIG5 value
(define (serialize [val : Value]) : String
  (match val
    [(? real? r) (~v r)]
    [(? boolean? b) (if b "true" "false")]
    [(CloV p n b e) "#<procedure>"]
    [(PrimV p) "#<primop>"]
    [(? string? s) (~v s)]))

#|
============================================================
|#

;; Parser Functions

; parses concrete syntax defining expressions into an AST
(define (parse [exp : Sexp]) : ExprC
  (match exp
    [(? real? n) (NumC n)]
    [(? string? s) (StrC s)]
    [(? symbol? id)
     (if (reserved id) (paig-error 'IOError 'parse (format "Reserved Symbol ~e Can Not Be An ID" id))
         (IdC id))]
    [(list s1 '? s2 'else: s3)
     (IfC (parse s1) (parse s2) (parse s3))]

    [(list 'blam (list (list (? symbol? p) ': ty)...) body)
     (define params(cast p (Listof Symbol)))
     (define types (map parse-type (cast ty (Listof Sexp))))
     (cond
       [(ormap reserved params)
        (paig-error 'IOError 'parse (format "Reserved Symbol ~e In Function Definition: ~e"
                                            (bad-symbol params) exp))]
       [(has-duplicate params)
        ((paig-error 'ArityError 'parse (format "Function Defintion Contains Duplicate Symbols: ~e" exp)))]
       [else (LamC params types (length params) (parse body))])]

    [(list 'with (list expr 'as (list (? symbol? id) ': ty))... ': body)
     (define idlist (cast id (Listof Symbol)))
     (define exprlist (cast expr (Listof Sexp)))
     (define typelist (map parse-type (cast ty (Listof Sexp))))
     (cond
       [(ormap reserved idlist)
        (paig-error 'IOError 'parse (format "Reserved Symbol ~e In With Statement: ~e"
                                            (bad-symbol idlist) exp))]
       [(has-duplicate idlist)
        ((paig-error 'ArityError 'parse (format "With Statement Contains Duplicate Symbols: ~e" exp)))]
       [else (AppC (LamC idlist typelist (length idlist) (parse body))
                   (map parse exprlist)
                   (length exprlist))])]     
    [(list exp explist ...)
     (AppC (parse exp)
           (map parse explist)
           (length explist))]
    [other (error 'PAIG "parse, Malformed Expression: ~e" other)]))


#|
============================================================
|#

;; Type Checker

(define (parse-type [s : Sexp]) : Type
  (match s
    ['num (NumT)]
    ['str (StrT)]
    ['bool (BoolT)]
    [(list (? symbol? s1) ... '-> s2)
     (define args (cast s1 (Listof Symbol)))
     (FuncT
      (map parse-type args)
      (parse-type s2))]
    [other (paig-error 'SyntaxError 'parse-type (format "Gave a non-existent type: ~e" s))]))

(define (type-check [exp : ExprC] [env : Type-Env]) : Type
  (match exp
    [(NumC n) (NumT)]
    [(StrC s) (StrT)]
    [(IdC n) (type-lookup n env)]
    [(LamC p t n b)
     (define ret (type-check b (extend-type-env p t env)))
     (FuncT t ret)]
    [(IfC test then else)
     (define test-type (type-check test env))
     (define then-type (type-check then env))
     (define else-type (type-check else env))
     (cond
       [(not (BoolT? test-type)) (error "s2")]
       [(not (equal? then-type else-type)) (error "s3")]
       [else then-type])]
    [(AppC f a n)
     (define f-type (type-check f env))
     (define a-type (for/list : (Listof Type) ([arg a]) (type-check arg env)))
     (cond
       [(not (FuncT? f-type)) (error "s4")]
       ;[(not (equal? (length (FuncT-args f-type)) n)) (error "s5")]
       [(not (andmap equal? (FuncT-args f-type) a-type))
        (error 'bad "s6 ~e, ~e" (FuncT-args f-type) a-type)]
       [else (FuncT-ret f-type)])]))


; searches for ids bound to types in the type-environment
; returns the type if it is bound
(define (type-lookup [for : Symbol] [env : Type-Env]) : Type
    (match env
      ['() (paig-error 'IOError 'type-lookup (format "name not found: ~e" for))]
      [(cons (Type-Map id type) r) (cond
                    [(symbol=? for id) type]
                    [else (type-lookup for r)])]))

(define (extend-type-env [ids : (Listof Symbol)] [types : (Listof Type)] [env : Type-Env]) : Type-Env
  (define new-env env)
  (for/list : (Listof Void) ([id ids] [ty types])
    (set! new-env (cons (Type-Map id ty) new-env)))
  new-env)
    


#|
============================================================
|#

;; Primitive Functions Definitions

; prim-add: adds one real to another, throws error
; if arity != 2 or if either input is not a real number
(define (prim-add [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-add (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (+ (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-add (format "Expected List of Two Values, got ~e" val))]))

; prim-mult: handles subtraction and unary negation
; if arity is not 1 or 2, or the inputs are not reals throws an error
(define (prim-sub [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-sub (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 1 arity) (- 0 (list-ref val 0))]
    [(= 2 arity) (- (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-sub (format "Expected List of Two Values, got ~e" val))]))

; prim-mult: multiplies one real by another, throws error if
; arity != 2 or if either input is not a real number
(define (prim-mult [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-mult (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (* (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-mult (format "Expected List of Two Values, got ~e" val))]))

; prim-div: multiplies one real by another, throws error if
; arity != 2 or if either input is not a real number
(define (prim-div [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-div (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity)
     (if (= (list-ref val 1) 0)
         (paig-error 'DivByZero 'prim-div (format "Can Not Divide By Zero, ~e" val))
         (/ (list-ref val 0) (list-ref val 1)))]
    [(paig-error 'ArityError 'prim-div (format "Expected List of Two Values, got ~e" val))]))

; prim-lte: compares two reals, returns true if first real is
; less than or equal to the second, false otherwise
(define (prim-lte [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-lte (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (<= (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-lte (format "Expected List of Two Values, got ~e" val))]))

; prim-num-eq: Takes as input a list of two reals and returns true if they are equal
(define (prim-num-eq [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (= 2 arity))
     (paig-error 'ArityError 'prim-num-eq (format "Expected List of Two Values, got ~e" val))] 
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-num-eq (format "Expected List of Two Reals, got ~e" val))]
    [else (equal? (list-ref val 0) (list-ref val 1))]))

; prim-str-eq: Takes as input a list of two strings and returns true if they are equal
(define (prim-str-eq [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (= 2 arity))
     (paig-error 'ArityError 'prim-str-eq (format "Expected List of Two Values, got ~e" val))] 
    [(not (andmap string? val))
     (paig-error 'TypeError 'prim-str-eq (format "Expected List of Two Strings, got ~e" val))]
    [else (equal? (list-ref val 0) (list-ref val 1))]))

; substring
; returns substring of an original string defined by [start, end)
(define (substr [val : (Listof Value)] [arity : Real]) : Value
  (cond
    [(not (= arity 3))(paig-error 'ArityError 'substring (format "Expected List of Three Values, got ~e" val))]
    [else
     (define str (list-ref val 0))
     (define start (list-ref val 1))
     (define end (list-ref val 2))
     (cond 
       [(not (string? str))(paig-error 'TypeError 'substring (format "First Arg Must Be String, got ~e" str))]
       [(not (natural? start))(paig-error 'TypeError 'substring (format "Second Arg Must Be Natural, got ~e" start))]
       [(not (natural? end))(paig-error 'TypeError 'substring (format "Third Arg Must Be Natural, got ~e" end))]
       [(> start end)(paig-error 'ValueError 'substring (format "Start Index (~e) > End Index (~e)" start end))]
       [(> end (string-length str))(paig-error 'ValueError 'substring
                                               (format "End Index Out Of Bounds, \
length ~e, given ~e" (string-length str) end))]
       [else (substring str start end)])]))

#|
============================================================
|#

;; Top-Environments

; macro defining an empty environment
(define top-env (list
                (Binding 'true #t)
                (Binding 'false #f)
                (Binding '+ (PrimV prim-add))
                (Binding '- (PrimV prim-sub))
                (Binding '* (PrimV prim-mult))
                (Binding '/ (PrimV prim-div))
                (Binding '<= (PrimV prim-lte))
                (Binding 'num-eq? (PrimV prim-num-eq))
                (Binding 'str-eq? (PrimV prim-str-eq))
                (Binding 'substring (PrimV substr))))

(define top-type-env (list
                      (Type-Map 'true (BoolT))
                      (Type-Map 'false (BoolT))
                      (Type-Map '+ (FuncT (list (NumT) (NumT)) (NumT)))
                      (Type-Map '- (FuncT (list (NumT) (NumT)) (NumT)))
                      (Type-Map '* (FuncT (list (NumT) (NumT)) (NumT)))
                      (Type-Map '/ (FuncT (list (NumT) (NumT)) (NumT)))
                      (Type-Map '<= (FuncT (list (NumT) (NumT)) (BoolT)))
                      (Type-Map 'num-eq? (FuncT (list (NumT) (NumT)) (BoolT)))
                      (Type-Map 'str-eq? (FuncT (list (StrT) (StrT)) (BoolT)))
                      (Type-Map 'substring (FuncT (list (StrT) (NumT) (NumT)) (StrT)))))

#|
============================================================
|#

;; Error Handler

; prints formatted error string given a set of error conditions
(define (paig-error [type : Symbol] [f : Symbol] [msg : String]) : Nothing
  (error 'PAIG "\n(~a) In ~a: ~a" type f msg))

#|
============================================================
|#

;; Parser Helper Functions

; verifies if a symbol is a reserved keyword
(define (reserved [s : Symbol]) : Boolean
  (match s
    [(or 'with 'as '? 'else: 'blam ':) #t]
    [other #f]))


; checks for duplicates in a list of symbols
; returns #t if one exists, otherwise #f
(define (has-duplicate [s : (Listof Symbol)]) : Boolean
  (match s
    [(cons f r) (if (ormap (λ ([arg : Symbol]) : Boolean (equal? f arg)) r) #t (has-duplicate r))]
    ['() #f]))


; returns first occurence of a reserved symbol in a list of symbols
(define (bad-symbol [s : (Listof Symbol)]) : Symbol
  (match s
    ['() (paig-error 'IOError 'bad-symbol "Reserved Symbol Used But Not Present in Symbol List")]
    [(cons f r) (if (reserved f) f (bad-symbol r))]))



#|
============================================================
|#

;; Interpreter Helper Functions


; searches for bound variable values in an environment
; returns the value if it exists
(define (lookup [for : Symbol] [env : Env]) : Value
    (match env
      ['() (paig-error 'IOError 'lookup (format "name not found: ~e" for))]
      [(cons (Binding name val) r) (cond
                    [(symbol=? for name) val]
                    [else (lookup for r)])]))

; extends the current environment to include bindings defined by names and args
(define (extend-env [args : (Listof Value)] [names : (Listof Symbol)] [env : Env]) : Env
  (append
   (map Binding names args)
   env))


#|
============================================================
|#

;; PrimV test cases

; validate all primitive operations
(check-equal? (prim-add  (list 3 4)  2) 7)
(check-equal? (prim-sub  (list 5 3)  2) 2)
(check-equal? (prim-sub  (list 3)  1) -3)
(check-equal? (prim-mult (list 2 10) 2) 20)
(check-equal? (prim-div  (list 15 3) 2) 5)
(check-equal? (prim-lte  (list -5 -1) 2) #t)
(check-equal? (prim-lte  (list -1 -1) 2) #t)
(check-equal? (prim-lte  (list 78 -1) 2) #f)
(check-equal? (prim-num-eq  (list 128 128) 2) #t)
(check-equal? (prim-num-eq  (list 128 324) 2) #f)
(check-equal? (prim-str-eq  (list "s" "s") 2) #t)
(check-equal? (prim-str-eq  (list "s" "f") 2) #f)
(check-equal? (substr (list "abcde" 2 4) 3) "cd")
(check-equal? (substr (list "abcde" 0 5) 3) "abcde")

;; PrimV error cases

; check for all arity and type errors that can happen in PrimV
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-add: "
                          "Input Must be Only Real Numbers, '(3 #f)"))
           (λ () (prim-add (list 3 #f) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-add: "
                          "Expected List of Two Values, got '(3 4 5)"))
           (λ () (prim-add (list 3 4 5) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-sub: "
                          "Input Must be Only Real Numbers, '(#t 3)"))
           (λ () (prim-sub (list #t 3) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-sub: "
                          "Expected List of Two Values, got '(3 2 1)"))
           (λ () (prim-sub (list 3 2 1) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-mult: "
                          "Input Must be Only Real Numbers, '(3 #t)"))
           (λ () (prim-mult (list 3 #t) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-mult: "
                          "Expected List of Two Values, got '(3 2 1)"))
           (λ () (prim-mult (list 3 2 1) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-div: "
                          "Input Must be Only Real Numbers, (list (CloV '() 0 (IdC 'a) '()) 2)"))
           (λ () (prim-div (list (CloV '() 0 (IdC 'a) '()) 2) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(DivByZero) In prim-div: "
                          "Can Not Divide By Zero, '(3 0)"))
           (λ () (prim-div (list 3 0) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-div: "
                          "Expected List of Two Values, got '(3 0 1)"))
           (λ () (prim-div (list 3 0 1) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-lte: "
                          "Input Must be Only Real Numbers, (list (CloV '() 0 (IdC 'a) '()) 2)"))
           (λ () (prim-lte (list -15 (PrimV prim-lte)) 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-lte: "
                          "Expected List of Two Values, got '(3 0 1)"))
           (λ () (prim-lte (list 3 0 1) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-num-eq: Expected List of Two Values, got '(1 2 4)"))
           (λ () (prim-num-eq (list 1 2 4) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-num-eq: Expected List of Two Reals, got '(1 \"s\")"))
           (λ () (prim-num-eq (list 1 "s") 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-str-eq: Expected List of Two Values, got '(\"s\" \"t\" \"u\")"))
           (λ () (prim-str-eq (list "s" "t" "u") 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-str-eq: Expected List of Two Strings, got '(1 \"s\")"))
           (λ () (prim-str-eq (list 1 "s") 2)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In substring: \
Third Arg Must Be Natural, got (PrimV #<procedure:prim-add>)"))
           (λ () (substr (list "" 5 (PrimV prim-add)) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In substring: Start Index (5) > End Index (3)"))
           (λ () (substr (list "" 5 3) 3)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In substring: End Index Out Of Bounds, length 3, given 4"))
           (λ () (substr (list "hey" 0 4) 3)))

#|
============================================================
|#

;; Parser Test Cases

; make sure all ASTs parse properly
(check-equal? (parse '13) (NumC 13))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{+ 4 5}) (AppC (IdC '+) (list (NumC 4) (NumC 5)) 2))
#;(check-equal?
 (parse
  '{blam ([a : num] [b : num] [c : num]) {+ a {- b c}}})
 (LamC '(a b c) (cast (list (NumT) (NumT) (NumT)) (Listof Type)) 3
       (AppC (IdC '+) (list (IdC 'a)
                            (AppC (IdC '-) (list (IdC 'b) (IdC 'c)) 2)) 2)))
(check-equal? (parse '{x ? y else: z}) (IfC (IdC 'x) (IdC 'y) (IdC 'z)))
(check-equal? (parse '{f a b c}) (AppC (IdC 'f) (list (IdC 'a) (IdC 'b) (IdC 'c)) 3))


;; Parser Error Test Cases

; if function definition contains duplicate parameter names, raise error
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In parse: "
                          "Function Defintion Contains Duplicate Symbols: '(blam (x x x) (+ x x))"))
           (λ () (parse '{blam ([x : num] [x : num] [x : num]) {+ x x}})))

; used reserved character as function defintion arguments
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: "
                                 "Reserved Symbol '? In Function Definition: '(blam (?) 2)"))
           (λ () (parse '{blam ([? : num]) 2})))
; cant a reserved symbol to an IdC
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: Reserved Symbol '? Can Not Be An ID"))
           (λ () (parse '{? 2})))
; cant bind a reserved symbol to a function name in a with statement
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: "
                                 "Reserved Symbol '? In With Statement: '(with ((+ 9 14) as ?) (98 as y) : (+ z y))"))
           (λ () (parse '{with [{+ 9 14} as [? : num]]
                               [98 as [y : num]] :
                               {+ z y}})))
; cant provide duplicate parameters to a with statement
(check-exn (regexp (regexp-quote "PAIG: \n(ArityError) In parse: "
                                 "With Statement Contains Duplicate Symbols: '(with ((+ 9 14) as z) (98 as z) : (z))"))
           (λ () (parse '{with [{+ 9 14} as [z : num]]
                               [98 as [z : num]] :
                               {z}})))
; if the paig gets an empty program, throws error
(check-exn (regexp (regexp-quote "PAIG: parse, Malformed Expression: '()"))
           (λ () (parse '{})))


; debug used to test expressions separate from functions
(define (debug-exp [exp : Sexp]) : Value
  (interp (parse exp) top-env))

#|
============================================================
|#

;; Interpreter Test Cases

; make sure programs evaluate properly
(check-equal? (debug-exp '{* 10 {+ -3.125 17}}) 138.75)
(check-equal? (debug-exp '{- {- {- {- {- 0}}}}}) 0)
(check-equal? (debug-exp '{+ {+ 1 2} {- 1 2}}) 2)
(check-equal? (debug-exp '{* 2.5 {+ 2 2}}) 10.0)
(check-equal? (debug-exp '{* 3 {- 3 4}}) -3)
(check-equal? (debug-exp '{-{+ 3 4}}) -7)
(check-equal? (debug-exp '{-{* 3 4}}) -12)
(check-equal? (debug-exp '{-{- 3 4}}) 1)
(check-equal? (debug-exp '{- 4}) -4)
(check-equal? (debug-exp '{-{- -12.5}}) -12.5)
(check-equal? (debug-exp '{/ 5 1}) 5)
(check-equal? (debug-exp '{* {+ {* -1.5 3} {+ {* 7 8} 2}} 3}) 160.5)
(check-equal? (debug-exp '{-{* {+ {* -1.5 3} {+ {* 7 8} 2}} 3}}) -160.5)
(check-equal? (debug-exp '{(<= 4 0) ? {+ 2 3} else: {+ 4 5}}) 9)
(check-equal? (debug-exp '{(<= -2.5 0) ? {* -1 2} else: 9}) -2)
(check-equal? (debug-exp '{(<= 0 0) ? 22.9 else: {* 18273 -123.123}}) 22.9)
(check-equal? (debug-exp '{{{blam ([x : num]) {blam ([y : num]) {+ x y}}} 4} 5}) 9)
(check-equal? (debug-exp '{{blam ([x : num]) {{blam ([y : num]) {+ x y}} 4}} 5}) 9)


;; Interpreter Error Test Cases

; verifies eager substitution
(check-exn (regexp (regexp-quote "PAIG: \n(DivByZero) In prim-div: Can Not Divide By Zero, '(5 0)"))
           (λ () (top-interp '{{blam ([x : num]) 5} {/ 5 0}})))
; if function application recieves non-function as input
(check-exn (regexp (regexp-quote "PAIG: \n(TypeError) In interp: "
                                 "Non-Function 2 Passed In Function Application: (AppC (NumC 2) '() 0)"))
           (λ () (interp (parse '{2}) top-env)))
; If conditional receives non-boolean as test
(check-exn (regexp (regexp-quote "PAIG: \n(TypeError) In interp: "
                                 "Non-Boolean Used as Condition in If Statement: (IfC (NumC 4) (NumC 3) (NumC 1))"))
           (λ () (interp (parse '{4 ? 3 else: 1}) top-env)))
; If binding can not be found in the env
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In lookup: name not found: 'none"))
           (λ () (lookup 'none '())))
; Function def and application have different num arguments
(check-exn (regexp (regexp-quote "PAIG: \n(ArityError) In interp: "
                                 "Incorrect Number of Funtion Arguments: (AppC (IdC 'f) (list (NumC 3)) 1)"))
           (λ () (interp (parse '{f 3})
                         (append top-env (list (Binding 'f (CloV (list 'a 'b) 2 (NumC -69) top-env)))))))


;; IdC Substitution

; tests environment substitution
(check-equal? (interp (parse 'true) top-env) #t)
(check-equal? (interp (parse 'false) top-env) #f)
(check-equal? (CloV? (interp (IdC 'thing) (append top-env (list (Binding 'thing (CloV (list 'a) 1 (NumC 1) '()))))))
              #t)
(check-equal? (PrimV? (interp (IdC 'thing) (append top-env (list (Binding 'thing (PrimV prim-add))))))
              #t)


;; Serialize Test Cases

; tests to make sure all values serialize properly
(check-equal? (serialize 12123.983) "12123.983")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (CloV '() 0 (NumC 0) '())) "#<procedure>")
(check-equal?
 (serialize
  (interp (parse '{mult 3 4})
          (append top-env
                  (list
                   (Binding 'mult
                            (CloV (list 'a 'x) 2 (AppC (IdC '*) (list (IdC 'a) (IdC 'x)) 2) top-env))))))
 "12")


;; Function Test Cases

; square returns the squared value of the input
(define square '{blam ([a : num]) {* a a}})
; taylor expansion of cosine using the first two terms
(define cosine '{{blam ([square : {num -> num}])
                      {{blam ([cos : {num -> num}]) 
                             {+ 56 {cos 0.5}}
                            }{blam ([x : num]) {+ {- 1 {/ {square x} 2}} {/ {* {square x} {square x}} 24}}}}
                      }{blam ([a : num]) {* a a}}})
                     
; adds two number a and b
(define add-function '{{blam ([add-function : {num num -> num}]) {add-function 1 3}}
                       {blam ([a : num] [b : num]) {+ a b}}}) 
; tests a bunch of parameters
(define many-params '{{blam ([many-params : {num num num num num num num num num num -> num}]) {many-params 1 2 3 4 5 6 7 8 9 10}}
                      {blam ([a : num] [b : num] [c : num] [d : num] [e : num] [f : num] [g : num] [h : num] [i : num] [j : num])
                            {+ {+ {+ {+ {+ {+ {+ {+ {+ a b} c} d} e} f} g} h} i} j}}})
; returns nine
(define nine '{{blam ([nine : {-> num}]) {nine}}
               {blam () 9}})

; recursively computes the int it was given
#;(define dumb-count '{{blam (dumb) {dumb 10 dumb}}
                     {blam (x y) {(<= x 0) ? 0 else: {+ 1 {y {- x 1} y}}}}})

(check-equal? (top-interp cosine) "56.877604166666664")
(check-equal? (top-interp add-function) "4")
(check-equal? (top-interp many-params) "55")
(check-equal? (top-interp nine) "9")
#;(check-equal? (top-interp dumb-count) "10")


;; Desugaring Test Cases

; Example with given by prof
(check-equal? (debug-exp '{with [{+ 9 14} as [z : num]]
                                [98 as [y : num]] :
                                {+ z y}}) 121)
; Lab 5 test code
#;(check-equal?
 (debug-exp
  '{with [{blam (f) {blam (a) {f a}}} as one]
         [{blam (f) {blam (a) {f {f a}}}} as two]
         [{blam (num1) {blam (num2) {blam (f) {blam (a) {{num1 f} {{num2 f} a}}}}}} as add]:
         {with [{{add one} two} as three]
               [{blam (a) {+ a a}} as double] :
               {{three double} 2}}}) 16)

; shadowing other functions
(check-equal? (debug-exp '{with [{blam ([a : num]) {+ 1 a}} as [f : {num -> num}]] :
                                {with [{blam ([a : num]) {* 5 a}} as [f : {num -> num}]] :
                                      {with [{blam ([a : num]) {- a 6}} as [f : {num -> num}]] :
                                            {f 6}}}}) 0)

(type-check (parse '{with [{blam ([a : num]) {+ 1 a}} as [f : {num -> num}]] :
                                {with [{blam ([a : num]) {* 5 a}} as [f : {num -> num}]] :
                                      {with [{blam ([a : num]) {- a 6}} as [f : {num -> num}]] :
                                            {f 6}}}})
            top-type-env)

; shadowing primitives
(check-equal? (debug-exp '{with [{blam ([a : num]) {+ 1 a}} as [+ : {num -> num}]] :
                                {+ 5}}) 6)


;; Helper Test Cases

; test cases for helper functions
(check-equal? (bad-symbol '(a b c d ?)) '?)
(check-equal? (bad-symbol '(+ blam / with)) 'blam)

(check-equal? (has-duplicate '(a a b c)) #t)
(check-equal? (has-duplicate '(a b c c)) #t)
(check-equal? (has-duplicate '(a b c)) #f)
(check-equal? (has-duplicate '(x x x)) #t)

(check-exn (regexp
            (regexp-quote "PAIG: \n(IOError) In bad-symbol: "
                          "Reserved Symbol Used But Not Present in Symbol List"))
           (λ () (bad-symbol '(a b c d e f))))





