#lang typed/racket

(require typed/rackunit)

; Full Project Implemented

#|
============================================================
|#

;; Data Types

; output data type
(define-type Value (U Real Boolean CloV PrimV String ArrV '()))

; closures
(struct CloV ([params : (Listof Symbol)]
              [num-params : Natural]
              [body : ExprC]
              [env : Env]) #:transparent)

; primitive functions 
(struct PrimV ([op : (-> (Listof Value) Natural Store Value)])#:transparent)

; array values (base is pointer to first value in store)
(struct ArrV ([base : Natural]
              [length : Natural]) #:transparent)


; Constructs

; real numbers
(struct NumC ([n : Real]) #:transparent)

; defines all types of expressions that the interpeter can evaluate
(define-type ExprC (U NumC IdC LamC AppC IfC StrC MutC))

; bindings: names that can be substituted for other expressions
(struct IdC ([s : Symbol])  #:transparent)

; lambda expressions
(struct LamC ([params : (Listof Symbol)]
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

; type that handles mutation
(struct MutC ([name : Symbol]
              [exp : ExprC])#:transparent)

#|
============================================================
|#

;; Interpreter Functions

; top-level function, runs a PAIG program given a list 
; of function s-expressions
(define (top-interp [s : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse s) top-env (make-initial-store memsize))))

; evaluates an AST substituting in functions as needed
(define (interp [e : ExprC] [env : Env] [store : Store]) : Value
  (match e
    [(NumC n) n]
    [(StrC s) s]
    [(IdC n) (fetch (lookup n env) store)]
    [(LamC p n b) (CloV p n b env)]
    [(MutC n e) (store-set! store (lookup n env) (interp e env store))]
    [(AppC f a n)
     (define fd (interp f env store))
     (define arg-values (for/list : (Listof Value) ([arg a]) (interp arg env store)))
     (match fd
       [(PrimV p) (p arg-values n store)]
       [(CloV c-params c-n c-body c-env)
        (cond
          [(= n c-n)
           (interp c-body
                  (extend-env arg-values c-params c-env store) store)]
          [else (paig-error 'ArityError 'interp
                            (format "Incorrect Number of Funtion Arguments: ~e" e))])]
       [other (paig-error 'TypeError 'interp
                          (format "Non-Function ~e Passed In Function Application: ~e" fd e))])]
    [(IfC test then else)
     (match (interp test env store)
       [(? boolean? b)
        (if b (interp then env store) (interp else env store))]
       [other (paig-error 'TypeError 'interp
                          (format "Non-Boolean Used as Condition in If Statement: ~e" e))])]))


; returns a string representation of a PAIG5 value
(define (serialize [val : Value]) : String
  (match val
    [(? real? r) (~v r)]
    [(? boolean? b) (if b "true" "false")]
    [(CloV p n b e) "#<procedure>"]
    [(PrimV p) "#<primop>"]
    [(ArrV b s) "#<array>"]
    [(? string? s) (~v s)]
    ['() "null"]))

#|
============================================================
|#

;; Assignment 7 Functions

;; While function, written in PAIG5.1
(define while
  '{with ["plumbus" as while]:
         {do {while := {blam (test body) {{test} ? {do {body} {while test body}} else: null}}}
           while}})

;; In-order function, written in PAIG5.1
(define in-order
  (quasiquote
   {with [null as length]
         [null as arr]:
         {blam (r l)
               {do {length := l}
                 {arr := r}
                 {do {(unquote while)
                      {blam () {{<= length 1}
                                ? false
                                else: {do {length := {- length 1}} true}}}
                      {blam () {{<= {aref arr {- length 1}} {aref arr length}}
                                ? null
                                else: {length := -1}}}}
                   {{equal? length -1} ? false else: true}}}}}))


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
     (if (reserved id) (paig-error 'IOError 'parse
                                   (format "Reserved Symbol ~e Can Not Be An ID" id))
         (IdC id))]
    [(list (? symbol? name) ':= expr) (MutC name (parse expr))]
    [(list s1 '? s2 'else: s3)
     (IfC (parse s1) (parse s2) (parse s3))]
    [(list 'blam (list (? symbol? paramlist) ...) body)
     (define params(cast paramlist (Listof Symbol)))
     (cond
       [(ormap reserved params)
        (paig-error 'IOError 'parse
                    (format "Reserved Symbol ~e In Function Definition: ~e"
                            (bad-symbol params) exp))]
       [(has-duplicate params)
        ((paig-error 'ArityError 'parse
                     (format "Function Defintion Contains Duplicate Symbols: ~e" exp)))]
       [else (LamC params (length params) (parse body))])]
    [(list 'with (list expr 'as (? symbol? id))... ': body)
     (define idlist (cast id (Listof Symbol)))
     (define exprlist (cast expr (Listof Sexp)))
     (cond
       [(ormap reserved idlist)
        (paig-error 'IOError 'parse (format "Reserved Symbol ~e In With Statement: ~e"
                                            (bad-symbol idlist) exp))]
       [(has-duplicate idlist)
        ((paig-error 'ArityError 'parse
                     (format "With Statement Contains Duplicate Symbols: ~e" exp)))]
       [else (AppC (LamC idlist (length idlist) (parse body))
                   (map parse exprlist)
                   (length exprlist))])]     
    [(list exp explist ...)
     (AppC (parse exp)
           (map parse explist)
           (length explist))]
    [other (paig-error 'IOError 'parse (format "Malformed Expression: ~e" other))]))


#|
============================================================
|#

;; Primitive Functions Definitions

; prim-add: adds one real to another, throws error
; if arity != 2 or if either input is not a real number
(define (prim-add [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-add (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (+ (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-add (format "Expected List of Two Values, got ~e" val))]))

; prim-mult: handles subtraction and unary negation
; if arity is not 1 or 2, or the inputs are not reals throws an error
(define (prim-sub [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-sub (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 1 arity) (- 0 (list-ref val 0))]
    [(= 2 arity) (- (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-sub (format "Expected List of Two Values, got ~e" val))]))

; prim-mult: multiplies one real by another, throws error if
; arity != 2 or if either input is not a real number
(define (prim-mult [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-mult (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (* (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-mult (format "Expected List of Two Values, got ~e" val))]))

; prim-div: multiplies one real by another, throws error if
; arity != 2 or if either input is not a real number
(define (prim-div [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
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
(define (prim-lte [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (andmap real? val))
     (paig-error 'TypeError 'prim-lte (format "Input Must be Only Real Numbers, ~e" val))]
    [(= 2 arity) (<= (list-ref val 0) (list-ref val 1))]
    [(paig-error 'ArityError 'prim-lte (format "Expected List of Two Values, got ~e" val))]))

; prim-equal: Takes as input a list of two values and returns true if they are equal
; By default returns false if either are closures or primitives
(define (prim-equal [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (= 2 arity))
     (paig-error 'ArityError 'prim-equal (format "Expected List of Two Values, got ~e" val))] 
    [(ormap CloV? val) #f]
    [(ormap PrimV? val) #f]
    [else (equal? (list-ref val 0) (list-ref val 1))]))

; prim-error:
; error message that can be called by a paig user
(define (prim-error [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(= 1 arity) (error 'user-error "~a" (serialize (first val)))]
    [else (error "user-error")]))

; do
; evaluates multiple expressions sequentially, returning the last one
(define (do [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (if (<= arity 0) (paig-error 'ArityError 'do "Do Directive Must Contain At Least One Expression") void)
  (list-ref val (- arity 1)))

; array
; constructs an array from a list of values, returns the array value
(define (array [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (if (<= arity 0)(paig-error 'ArityError 'array "Must Be Called with >= 1 Value") void)
  (define base (malloc arity store))
  (batch-store-set! store base val)
  (ArrV base arity))

; make-array
; takes a size and value (in that order) and constructs an array in the store
; with every location set to value
(define (make-array [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (if (not (= arity 2))(paig-error 'ArityError 'make-array (format "Expected List of Two Values, got ~e" val)) void)
  (define size (list-ref val 0))
  (define value (list-ref val 1))
  (cond
    [(or (not (natural? size))(<= size 0))(paig-error 'TypeError 'make-array (format "Array Size Must \
Be a Natural > 0, got ~e" size))]
    [else
     (define base (malloc size store))
     (batch-store-set! store base (make-list size value))
     (ArrV base size)]))

; aref
; references a position in the array and returns its value
; val[0] is the ArrV, val[1] is the position of the value to be returned
(define (aref [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (if (not (= arity 2))(paig-error 'ArityError 'aref (format "Expected List of Two Values, got ~e" val)) void)
  (define arr (list-ref val 0))
  (define index (list-ref val 1))
  (cond
    [(not (ArrV? arr))(paig-error 'TypeError 'aref (format "First Arg Must Be Array, got ~e" arr))]
    [(not (natural? index))(paig-error 'TypeError 'aref (format "Second Arg Must Be Natural, got ~e" index))]
    [(>= index (ArrV-length arr))(paig-error 'ValueError 'aref (format "Index Out Of Bounds, \
length ~e, given ~e" (ArrV-length arr) index))]
    [else (fetch (+ index (ArrV-base arr)) store)]))

; aset!
; references a position in the array and modifies its value, returns Null
; val[0] is the ArrV, val[1] is the position, val[2] is the new value
(define (aset! [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (if (not (= arity 3)) (paig-error 'ArityError 'aset! (format "Expected List of Three Values, got ~e" val)) void)
  (define arr (list-ref val 0))
  (define index (list-ref val 1))
  (define insert (list-ref val 2))
  (cond
    [(not (ArrV? arr))(paig-error 'TypeError 'aset! (format "First Arg Must Be Array, got ~e" arr))]
    [(not (natural? index))(paig-error 'TypeError 'aset! (format "Second Arg Must Be a Natural, got ~e" index))]
    [(>= index (ArrV-length arr))(paig-error 'ValueError 'aset! (format "Index Out Of Bounds,\
 length ~e, given ~e" (ArrV-length arr) index))]
    [else (store-set! store (+ index (ArrV-base arr)) insert)]))
  
; substring
; returns substring of an original string defined by [start, end)
(define (substr [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
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

; dump-array
; util-function that converts an array to a string for debugging purposes
(define (dump-array [val : (Listof Value)] [arity : Natural] [store : Store]) : Value
  (cond
    [(not (= arity 1))(paig-error 'ArityError 'dump-array (format "Expected One Value, got ~e" val))]
     [else
     (define arr (list-ref val 0))
     (cond 
       [(not (ArrV? arr))(paig-error 'TypeError 'dump-array "First Arg Must Be Arr")]
       [else
        (define items (make-vector (ArrV-length arr) (cast 0 Value)))
        (for/list : (Listof Void) ([i (in-range (ArrV-length arr))])
          (vector-set! items i (aref (list arr i) 2 store)))
        (~a items)])]))


#|
============================================================
|#

;; Environment Definitions

; binds a symbol to a value
(struct Binding ([name : Symbol] [location : Natural]) #:transparent)

; Environment is a list of bindings
(define-type Env (Listof Binding))

; macro defining an empty environment
(define top-env (list
                (Binding 'true 1)
                (Binding 'false 2)
                (Binding 'null 3)
                (Binding '+ 4)
                (Binding '- 5)
                (Binding '* 6)
                (Binding '/ 7)
                (Binding '<= 8)
                (Binding 'equal? 9)
                (Binding 'error 10)
                (Binding 'do 11)
                (Binding 'array 12)
                (Binding 'make-array 13)
                (Binding 'aref 14)
                (Binding 'aset! 15)
                (Binding 'substring 16)
                (Binding 'dump-array 17)))

#|
============================================================
|#

;; The Store

; structure defining the store (alias of Vectorof Value)
(define-type Store (Vectorof Value))

; list of all top-env values that exist in the store by default
(define top-env-values (list #t
                             #f
                             '()
                             (PrimV prim-add)
                             (PrimV prim-sub)
                             (PrimV prim-mult)
                             (PrimV prim-div)
                             (PrimV prim-lte)
                             (PrimV prim-equal)
                             (PrimV prim-error)
                             (PrimV do)
                             (PrimV array)
                             (PrimV make-array)
                             (PrimV aref)
                             (PrimV aset!)
                             (PrimV substr)
                             (PrimV dump-array)))

; make memory store
(define (make-initial-store [memsize : Natural]) : Store
  ; this is a dumb way to do this, but its the only way that works
  (define heap (make-vector memsize (cast 0 Value)))
  (define base-length (+ (length top-env-values) 1))
  (if (< memsize base-length) (paig-error 'SegFault 'make-initial-store (format "Initial \
Store Requires a Minium of ~e Memory" base-length)) void)
  (vector-set! heap 0 base-length)
  (define base 1)
  (for/list : (Listof Void) ([t top-env-values]) (vector-set! heap base t) (set! base (+ 1 base)))
  heap)

; allocates "size" amount of memory in the store
(define (malloc [size : Natural] [store : Store]) : Natural
  (define head (cast (vector-ref store 0) Natural))
  (define new-head (+ head size))
  (if (> new-head (vector-length store))
      (paig-error 'SegFault 'malloc (format "Store of Size ~e Ran Out of \
Memory When Allocating ~e Value(s)" (vector-length store) size))
      (vector-set! store 0 new-head))
  head)

; fetches value at index in the store
(define (fetch [loc : Natural] [store : Store]) : Value
  (vector-ref store loc))

; set the value in store at index to be val
(define (store-set! [store : Store] [index : Natural] [val : Value]) : Null
  (vector-set! store index val)
  '())

; set the values in store starting at index to be list of vals
(define (batch-store-set! [store : Store] [base : Natural] [vals : (Listof Value)]) : Null
  (for/list : (Listof Void) ([v vals]) (vector-set! store base v) (set! base (+ 1 base)))
  '())

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
    [(or ':= 'with 'as '? 'else: 'blam ':) #t]
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
; returns the location in the store if it exists
(define (lookup [for : Symbol] [env : Env]) : Natural
  (match env
      ['() (paig-error 'IOError 'lookup (format "name not found: ~e" for))]
      [(cons (Binding name loc) r)
       (cond
         [(symbol=? for name) loc]
         [else (lookup for r)])]))


; extends the current environment to include bindings defined by names and args
(define (extend-env [args : (Listof Value)] [names : (Listof Symbol)] [env : Env] [store : Store]) : Env
  (define new-env env)
  (define top 0)
  (for/list : (Listof Void)
    ([a args] [n names])
    (set! top (malloc 1 store))
    (set! new-env (cons (Binding n (cast top Natural)) new-env))
    (vector-set! store top a))
  new-env)



#|
============================================================
|#

;; PrimV test cases

; validate all primitive operations
; mtvec is a used as a mini store to test prim functions that require it
(define mtvec (make-vector 32 (cast 0 Value)))
(define check-vec (make-vector 32 (cast 0 Value)))
(vector-set! mtvec 0 1)

(check-equal? (prim-add  (list 3 4) 2 mtvec) 7)
(check-equal? (prim-sub  (list 5 3) 2 mtvec) 2)
(check-equal? (prim-sub  (list 3)  1 mtvec) -3)
(check-equal? (prim-mult (list 2 10) 2 mtvec) 20)
(check-equal? (prim-div  (list 15 3) 2 mtvec) 5)
(check-equal? (prim-lte  (list -5 -1) 2 mtvec) #t)
(check-equal? (prim-lte  (list -1 -1) 2 mtvec) #t)
(check-equal? (prim-lte  (list 78 -1) 2 mtvec) #f)
(check-equal? (prim-equal  (list 128 128) 2 mtvec) #t)
(check-equal? (prim-equal  (list #f #f) 2 mtvec) #t)
(check-equal? (prim-equal  (list #t 128) 2 mtvec) #f)
(check-equal? (prim-equal  (list 128 (CloV '() 0 (IdC 'a) '())) 2 mtvec) #f)
(check-equal? (prim-equal  (list (PrimV prim-mult) 128) 2 mtvec) #f)

(check-equal? (array (list 15 (PrimV prim-mult) (CloV '() 0 (IdC 'a) '()) #t "s") 5 mtvec) (ArrV 1 5))
(vector-copy! check-vec 0 (cast (vector 6 15 (PrimV prim-mult) (CloV '() 0 (IdC 'a) '()) #t "s") (Vectorof Value)))
(check-equal? mtvec check-vec)

(check-equal? (aref (list (ArrV 1 5) 0) 2 mtvec) 15)
(check-equal? (aref (list (ArrV 1 5) 1) 2 mtvec) (PrimV prim-mult))
(check-equal? (aref (list (ArrV 1 5) 2) 2 mtvec) (CloV '() 0 (IdC 'a) '()))
(check-equal? (aref (list (ArrV 1 5) 3) 2 mtvec) #t)
(check-equal? (aref (list (ArrV 1 5) 4) 2 mtvec) "s")

(check-equal? (serialize (aset! (list (ArrV 1 5) 0 25) 3 mtvec)) "null")
(vector-set! check-vec 1 25)
(check-equal? mtvec check-vec)

(check-equal? (serialize (aset! (list (ArrV 1 5) 3 #f) 3 mtvec)) "null")
(vector-set! check-vec 4 #f)
(check-equal? mtvec check-vec)

(check-equal? (make-array (list 12 -3) 2 mtvec) (ArrV 6 12))
(vector-set! check-vec 0 18)
(vector-copy! check-vec 6 (cast (make-vector 12 -3) (Vectorof Value)))
(check-equal? mtvec check-vec)

(check-equal? (serialize (aset! (list (ArrV 6 12) 5 -7) 3 mtvec)) "null")
(vector-set! check-vec 11 -7)
(check-equal? mtvec check-vec)

(check-equal? (substr (list "abcde" 2 4) 3 mtvec) "cd")
(check-equal? (substr (list "abcde" 0 5) 3 mtvec) "abcde")


;; PrimV error cases

; check for all arity and type errors that can happen in PrimV
; reset mtvec from earlier cases
(vector-fill! mtvec 0)

(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-add: "
                          "Input Must be Only Real Numbers, '(3 #f)"))
           (λ () (prim-add (list 3 #f) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-add: "
                          "Expected List of Two Values, got '(3 4 5)"))
           (λ () (prim-add (list 3 4 5) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-sub: "
                          "Input Must be Only Real Numbers, '(#t 3)"))
           (λ () (prim-sub (list #t 3) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-sub: "
                          "Expected List of Two Values, got '(3 2 1)"))
           (λ () (prim-sub (list 3 2 1) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-mult: "
                          "Input Must be Only Real Numbers, '(3 #t)"))
           (λ () (prim-mult (list 3 #t) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-mult: "
                          "Expected List of Two Values, got '(3 2 1)"))
           (λ () (prim-mult (list 3 2 1) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-div: "
                          "Input Must be Only Real Numbers, (list (CloV '() 0 (IdC 'a) '()) 2)"))
           (λ () (prim-div (list (CloV '() 0 (IdC 'a) '()) 2) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(DivByZero) In prim-div: "
                          "Can Not Divide By Zero, '(3 0)"))
           (λ () (prim-div (list 3 0) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-div: "
                          "Expected List of Two Values, got '(3 0 1)"))
           (λ () (prim-div (list 3 0 1) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In prim-lte: "
                          "Input Must be Only Real Numbers, (list (CloV '() 0 (IdC 'a) '()) 2)"))
           (λ () (prim-lte (list -15 (PrimV prim-lte)) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-lte: "
                          "Expected List of Two Values, got '(3 0 1)"))
           (λ () (prim-lte (list 3 0 1) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In prim-equal: \
Expected List of Two Values, got '(1 2 4)"))
           (λ () (prim-equal (list 1 2 4) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "user-error: #<primop>"))
           (λ () (top-interp '{{blam (e) {e e}} error} 32)))
(check-exn (regexp
            (regexp-quote "user-error"))
           (λ () (top-interp '{{blam (e) {e}} error} 32)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In do: \
Do Directive Must Contain At Least One Expression"))
           (λ () (do '() 0 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In array: Must Be Called with >= 1 Value"))
           (λ () (array '() 0 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In make-array: Expected List of Two Values, got '()"))
           (λ () (make-array '() 0 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In make-array: Array Size Must Be a Natural > 0, got -1"))
           (λ () (make-array (list -1 (PrimV prim-mult)) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In make-array: Array Size Must Be a Natural > 0, got 1.5"))
           (λ () (make-array (list 1.5 (PrimV prim-mult)) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In make-array: Array Size Must Be a Natural > 0, got \"s\""))
           (λ () (make-array (list "s" (PrimV prim-mult)) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In aref: Expected List of Two Values, \
got (list \"s\" 3 (PrimV #<procedure:prim-mult>))"))
           (λ () (aref (list "s" 3 (PrimV prim-mult)) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aref: First Arg Must Be Array, got \"s\""))
           (λ () (aref (list "s" 0) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aref: Second Arg Must Be Natural, got 1.5"))
           (λ () (aref (list (ArrV 5 5) 1.5) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aref: Second Arg Must Be Natural, got -1"))
           (λ () (aref (list (ArrV 5 5) -1) 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In aref: Index Out Of Bounds, length 5, given 8"))
           (λ () (aref (list (ArrV 5 5) 8) 2 mtvec)))
(check-exn (regexp
            (regexp-quote  "PAIG: \n(ArityError) In aset!: Expected List of \
Three Values, got '(\"peepee\" \"poopoo\")"))
           (λ () (aset! (list "peepee" "poopoo") 2 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aset!: First Arg Must Be Array, got \"peepee\""))
           (λ () (aset! (list "peepee" ";)" 8) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aset!: Second Arg Must Be a Natural, got \"s\""))
           (λ () (aset! (list (ArrV 5 5) "s" 8) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In aset!: Second Arg Must Be a Natural, got -1"))
           (λ () (aset! (list (ArrV 5 5) -1 8) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In aset!: Index Out Of Bounds, length 5, given 5"))
           (λ () (aset! (list (ArrV 5 5) 5 3) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In substring: \
Expected List of Three Values, got '(\"\" 5 3 \"other\")"))
           (λ () (substr (list "" 5 3 "other") 4 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In substring: First Arg Must Be String, got #t"))
           (λ () (substr (list #t 5 3) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In substring: Second Arg Must Be Natural, got #f"))
           (λ () (substr (list "" #f 3) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In substring: \
Third Arg Must Be Natural, got (PrimV #<procedure:prim-add>)"))
           (λ () (substr (list "" 5 (PrimV prim-add)) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In substring: Start Index (5) > End Index (3)"))
           (λ () (substr (list "" 5 3) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ValueError) In substring: End Index Out Of Bounds, length 3, given 4"))
           (λ () (substr (list "hey" 0 4) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In dump-array: Expected One Value, got '(\"hey\" 0 4)"))
           (λ () (dump-array (list "hey" 0 4) 3 mtvec)))
(check-exn (regexp
            (regexp-quote "PAIG: \n(TypeError) In dump-array: First Arg Must Be Arr"))
           (λ () (dump-array (list "hey") 1 mtvec)))

#|
============================================================
|#

;; Store Test Cases
(check-exn (regexp
            (regexp-quote "PAIG: \n(SegFault) In make-initial-store: \
Initial Store Requires a Minium of 18 Memory"))
           (λ () (make-initial-store 0)))

(define test-store (make-initial-store 64))
(define test-base (vector-ref test-store 0))

(check-equal? (malloc 5 test-store) 18)
(check-equal? (vector-ref test-store 0) (+ (cast test-base Natural) 5))

(check-exn (regexp
            (regexp-quote "PAIG: \n(SegFault) In malloc: Store of \
Size 64 Ran Out of Memory When Allocating 1000 Value(s)"))
           (λ () (malloc 1000 test-store)))


#|
============================================================
|#

;; Parser Test Cases

; make sure all ASTs parse properly
(check-equal? (parse '13) (NumC 13))
(check-equal? (parse 'a) (IdC 'a))
(check-equal? (parse '{+ 4 5}) (AppC (IdC '+) (list (NumC 4) (NumC 5)) 2))
(check-equal?
 (parse
  '{blam (a b c) {+ a {- b c}}})
 (LamC '(a b c) 3
       (AppC (IdC '+) (list (IdC 'a)
                            (AppC (IdC '-) (list (IdC 'b) (IdC 'c)) 2)) 2)))
(check-equal? (parse '{x ? y else: z}) (IfC (IdC 'x) (IdC 'y) (IdC 'z)))
(check-equal? (parse '{f a b c}) (AppC (IdC 'f) (list (IdC 'a) (IdC 'b) (IdC 'c)) 3))


;; Parser Error Test Cases

; if function definition contains duplicate parameter names, raise error
(check-exn (regexp
            (regexp-quote "PAIG: \n(ArityError) In parse: "
                          "Function Defintion Contains Duplicate Symbols: '(blam (x x x) (+ x x))"))
           (λ () (parse '{blam (x x x) {+ x x}})))

; used reserved character as function defintion arguments
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: "
                                 "Reserved Symbol '? In Function Definition: '(blam (?) 2)"))
           (λ () (parse '{blam (?) 2})))
; cant a reserved symbol to an IdC
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: Reserved Symbol '? Can Not Be An ID"))
           (λ () (parse '{? 2})))
; cant bind a reserved symbol to a function name in a with statement
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: "
                                 "Reserved Symbol '? In With Statement: '(with ((+ 9 14) as ?) (98 as y) : (+ z y))"))
           (λ () (parse '{with [{+ 9 14} as ?]
                               [98 as y] :
                               {+ z y}})))
; cant provide duplicate parameters to a with statement
(check-exn (regexp (regexp-quote "PAIG: \n(ArityError) In parse: "
                                 "With Statement Contains Duplicate Symbols: '(with ((+ 9 14) as z) (98 as z) : (z))"))
           (λ () (parse '{with [{+ 9 14} as z]
                               [98 as z] :
                               {z}})))
; if the paig gets an empty program, throws error
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In parse: Malformed Expression: '()"))
           (λ () (parse '{})))


#|
============================================================
|#


;; Interpreter Test Cases

; debug used to test expressions separate from functions
(define (debug-exp [exp : Sexp]) : Value
  (interp (parse exp) top-env (make-initial-store 1024)))

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
(check-equal? (debug-exp '{{{blam (x) {blam (y) {+ x y}}} 4} 5}) 9)
(check-equal? (debug-exp '{{blam (x) {{blam (y) {+ x y}} 4}} 5}) 9)


;; Interpreter Error Test Cases

; verifies eager substitution
(check-exn (regexp (regexp-quote "PAIG: \n(DivByZero) In prim-div: Can Not Divide By Zero, '(5 0)"))
           (λ () (top-interp '{{blam (x) 5} {/ 5 0}} 1024)))
; if function application recieves non-function as input
(check-exn (regexp (regexp-quote "PAIG: \n(TypeError) In interp: "
                                 "Non-Function 2 Passed In Function Application: (AppC (NumC 2) '() 0)"))
           (λ () (interp (parse '{2}) top-env (make-initial-store 1024))))
; If conditional receives non-boolean as test
(check-exn (regexp (regexp-quote "PAIG: \n(TypeError) In interp: "
                                 "Non-Boolean Used as Condition in If Statement: (IfC (NumC 4) (NumC 3) (NumC 1))"))
           (λ () (interp (parse '{4 ? 3 else: 1}) top-env (make-initial-store 1024))))
; If binding can not be found in the env
(check-exn (regexp (regexp-quote "PAIG: \n(IOError) In lookup: name not found: 'none"))
           (λ () (lookup 'none '())))
; User throws an error 
(check-exn (regexp (regexp-quote "user-error: \"1234\""))
           (λ () (top-interp '(+ 4 (error "1234")) 1024)))

(define arity-store (make-initial-store 1024))
; Function def and application have different num arguments
(check-exn (regexp (regexp-quote "PAIG: \n(ArityError) In interp: "
                                 "Incorrect Number of Funtion Arguments: (AppC (IdC 'f) (list (NumC 3)) 1)"))
           (λ () (interp (parse '{f 3})
                         (extend-env (list (CloV (list 'a 'b) 2 (NumC -69) top-env)) (list 'f) top-env arity-store)
                         arity-store)))


;; IdC Substitution

; tests environment substitution
(check-equal? (interp (parse 'true) top-env (make-initial-store 1024)) #t)
(check-equal? (interp (parse 'false) top-env (make-initial-store 1024)) #f)
(define clov-store (make-initial-store 1024))
(check-equal? (CloV? (interp (IdC 'thing) (extend-env (list (CloV (list 'a) 1 (NumC 1) '()))
                                                      (list 'thing) top-env clov-store) clov-store))
              #t)
(define prim-store (make-initial-store 1024))
(check-equal? (PrimV? (interp (IdC 'thing) (extend-env (list (PrimV prim-add))
                                                       (list 'thing) top-env prim-store) prim-store))
              #t)


;; Serialize Test Cases

; tests to make sure all values serialize properly
(check-equal? (serialize 12123.983) "12123.983")
(check-equal? (serialize #t) "true")
(check-equal? (serialize #f) "false")
(check-equal? (serialize (CloV '() 0 (NumC 0) '())) "#<procedure>")
(define temp-store (make-initial-store 1024))
(check-equal?
 (serialize
  (interp (parse '{mult 3 4})
          (extend-env
           (list (CloV (list 'a 'x) 2 (AppC (IdC '*) (list (IdC 'a) (IdC 'x)) 2) top-env))
           (list 'mult)
           top-env
           temp-store)
          temp-store))
 "12")


;; PAIG language Function Test Cases

; square returns the squared value of the input
(define square '{blam (a) {* a a}})
; taylor expansion of cosine using the first two terms
(define cosine '{{blam (square)
                      {{blam (cos) 
                             {+ 56 {cos 0.5}}
                            }{blam (x) {+ {- 1 {/ {square x} 2}} {/ {* {square x} {square x}} 24}}}}
                      }{blam (a) {* a a}}})
                     
; adds two number a and b
(define add-function '{{blam (add-function) {add-function 1 3}}
                       {blam (a b) {+ 1 3}}}) 
; tests a bunch of parameters
(define many-params '{{blam (many-params) {many-params 1 2 3 4 5 6 7 8 9 10}}
                      {blam (a b c d e f g h i j) {+ {+ {+ {+ {+ {+ {+ {+ {+ a b} c} d} e} f} g} h} i} j}}})
; returns nine
(define nine '{{blam (nine) {nine}}
               {blam () 9}})

; recursively computes the int it was given
(define dumb-count '{{blam (dumb) {dumb 10 dumb}}
                     {blam (x y) {(<= x 0) ? 0 else: {+ 1 {y {- x 1} y}}}}})

(check-equal? (top-interp cosine 1024) "56.877604166666664")
(check-equal? (top-interp add-function 1024) "4")
(check-equal? (top-interp many-params 1024) "55")
(check-equal? (top-interp nine 1024) "9")
(check-equal? (top-interp dumb-count 1024) "10")


;; Desugaring Test Cases

; Example with given by prof
(check-equal? (debug-exp '{with [{+ 9 14} as z]
                                [98 as y] :
                                {+ z y}}) 121)
; Lab 5 test code
(check-equal?
 (debug-exp
  '{with [{blam (f) {blam (a) {f a}}} as one]
         [{blam (f) {blam (a) {f {f a}}}} as two]
         [{blam (num1) {blam (num2) {blam (f) {blam (a) {{num1 f} {{num2 f} a}}}}}} as add]:
         {with [{{add one} two} as three]
               [{blam (a) {+ a a}} as double] :
               {{three double} 2}}}) 16)

; shadowing other functions
(check-equal? (debug-exp '{with [{blam (a) {+ 1 a}} as f] :
                                {with [{blam (a) {* 5 a}} as f] :
                                      {with [{blam (a) {- a 6}} as f] :
                                            {f 6}}}}) 0)

; shadowing primitives
(check-equal? (debug-exp '{with [{blam (a) {+ 1 a}} as +] :
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


;; PAIG 5.1 Functional Tests

(check-equal?
 (top-interp '{with [5 as x] :
                    {do {x := 7}
                      {x := true} x}} 64) "true")

(check-equal? (top-interp '{array 1 2 3 4 5} 32) "#<array>")
(check-equal? (top-interp '{make-array 12 true} 32) "#<array>")

(check-equal?
 (top-interp '{with ["bogus" as fact]
                   :
                   {do {fact := {blam (n) {{<= n 0} ? 1 else: {* n {fact {- n 1}}}}}}
                     {fact 12}}}
            32) "479001600")

(check-equal?
 (top-interp '{with ["bogus" as fact]
                    [{make-array 12 0} as arr]
                    :
                    {do {fact := {blam (n) {{<= n 0} ? 1 else: {* n {fact {- n 1}}}}}}
                      {aset! arr 0 {fact 0}}
                      {aset! arr 1 {fact 1}}
                      {aset! arr 2 {fact 2}}
                      {aset! arr 3 {fact 3}}
                      {aset! arr 4 {fact 4}}
                      {aset! arr 5 {fact 5}}
                      {aset! arr 6 {fact 6}}
                      {aset! arr 7 {fact 7}}
                      {aset! arr 8 {fact 8}}
                      {aset! arr 9 {fact 9}}
                      {aset! arr 10 {fact 10}}
                      {aset! arr 11 {fact 11}}
                      {dump-array arr}}}
             128) "\"#(1 1 2 6 24 120 720 5040 40320 362880 3628800 39916800)\"")


(check-equal?
 (top-interp (quasiquote {with [9 as x]
                              [75 as y]:
                              {do {(unquote while) {blam () {{<= x 0} ? false else: {do {x := {- x 1}} true}}}
                                                   {blam () {y := {+ y 1}}}}
                                y}}) 1024) "84")
(check-equal? (top-interp (quasiquote {(unquote in-order) {array 1 2 3 4 5} 5}) 1024) "true")
(check-equal? (top-interp (quasiquote {(unquote in-order) {array 1 2 7 4 5} 5}) 1024) "false")

