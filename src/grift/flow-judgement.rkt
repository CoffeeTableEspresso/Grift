#lang racket

#|
Implementation of flow judgement ("Ins and Outs of Gradual Type inference")
|#

(require "../language/forms.rkt")

(provide flow-judgement)

(module+ test
  (require rackunit))

(define (set-filter proc s)
  (cond
    [(set-empty? s) (set)]
    [(proc (set-first s)) (set-add (set-filter proc (set-rest s)) (set-first s))]
    [else (set-filter proc (set-rest s))]))

(define (1+ n)
  (+ 1 n))

(struct FromTo (from to) #:transparent)

(define (any? var)
  (or (Any? var)
      (AnyParam? var)
      (AnyReturn? var)
      (AnyVect? var)
      (AnyTup? var)))

(define (type-norm type var)
  (define (fn-type-norm arity params)
    (define counter
      (let ([n -1])
        (lambda ()
          (set! n (1+ n))
          n)))
    (Fn arity (map (lambda (x) (AnyParam var (counter))) params) (AnyReturn var)))
  (define (tup-type-norm len)
    (define counter
      (let ([n -1])
        (lambda ()
          (set! n (1+ n))
          n)))
    (STuple len (map (lambda (x) (AnyTup var (counter))) (make-list len #f))))
  (match type
    [(Dyn) (Dyn)]
    [(Unit) (Unit)]
    [(String) (String)]
    [(Void) (Void)]
    [(Bot) (Bot)]
    [(Int) (Int)]
    [(Float) (Float)]
    [(Bool) (Bool)]
    [(Character) (Character)]
    [(Fn arity params _) (fn-type-norm arity params)]
    [(GVect _) (GVect (AnyVect var))]
    [(STuple len _) (tup-type-norm len)]
    [else (error "TODO: implement type-norm for ~a and ~a" type var)]))

(module+ test
  (test-equal? "shape of Dyn is Dyn"
               (type-norm (Dyn) (Any 1))
               (Dyn))
  (test-equal? "shape of primitives is themselves"
               (type-norm (Int) (Any 1))
               (Int))
  (test-equal? "shape of functions is a function type with the same type"
               (type-norm (Fn 2 (list (Int) (Bool)) (Character)) (Any 1))
               (Fn 2
                   (list (AnyParam (Any 1) 0)
                         (AnyParam (Any 1) 1))
                   (AnyReturn (Any 1))))
  (test-equal? "shape of vectors is a vector indexed with the same type"
               (type-norm (GVect (Int)) (Any 2))
               (GVect (AnyVect (Any 2))))
  (test-equal? "shape of tuples is a tuple indexed with the same types"
               (type-norm (STuple 3 (list (Bool) (Int) (Dyn))) (Any 4))
               (STuple 3 (list (AnyTup (Any 4) 0)
                               (AnyTup (Any 4) 1)
                               (AnyTup (Any 4) 2))))
  )

(define (kindof? type var)
  (define (fn-kindof? cnt args ret var)
    (if (empty? args)
        (equal? ret (AnyReturn var))
        (and (equal? (first args)
                     (AnyParam var cnt))
             (fn-kindof? (1+ cnt)
                         (rest args)
                         ret
                         var))))
  (define (tup-kindof? cnt items var)
    (if (empty? items)
        #t
        (and (equal? (first items)
                     (AnyTup var cnt))
             (tup-kindof? (1+ cnt)
                          (rest items)
                          var))))
  (match type
    [(Unit) #t]
    [(Dyn) #t]
    [(String) #t]
    [(Void) #t]
    [(Bot) #t]
    [(Int) #t]
    [(Float) #t]
    [(Bool) #t]
    [(Character) #t]
    [(Fn _ params ret) (fn-kindof? 0 params ret var)]
    [(GVect vect-type) (equal? vect-type (AnyVect var))]
    [(STuple _ items) (tup-kindof? 0 items var)]
    [else #f]))

(module+ test
  (test-equal? "Dyn matches everything"
               (kindof? (Dyn) (Any 1))
               #t)
  (test-equal? "Primitives also match, trivially"
               (kindof? (Int) (Any 1))
               #t)
  (test-equal? "Function"
               (kindof? (Fn 1 (list (AnyParam (Any 1) 0)) (AnyReturn (Any 1))) (Any 1))
               #t)
  (test-equal? "Function"
               (kindof? (Fn 1 (list (AnyParam (Any 2) 0)) (AnyReturn (Any 1))) (Any 1))
               #f)
  (test-equal? "Function"
               (kindof? (Fn 1 (list (AnyParam (Any 1) 2)) (AnyReturn (Any 1))) (Any 1))
               #f)
  (test-equal? "Function"
               (kindof? (Fn 1 (list (AnyParam (Any 1) 0)) (AnyReturn (Any 2))) (Any 1))
               #f)
  (test-equal? "Vector"
               (kindof? (GVect (AnyVect (Any 1))) (Any 1))
               #t)
  (test-equal? "Vector"
               (kindof? (GVect (AnyVect (Any 1))) (Any 2))
               #f)
  (test-equal? "Tuple"
               (kindof? (STuple 3 (list (AnyTup (Any 1) 0)
                                        (AnyTup (Any 1) 1)
                                        (AnyTup (Any 1) 2)))
                        (Any 1))
               #t)
  (test-equal? "Tuple"
               (kindof? (STuple 3 (list (AnyTup (Any 1) 0)
                                        (AnyTup (Any 2) 1)
                                        (AnyTup (Any 1) 2)))
                        (Any 1))
               #f)
  )

(define (get-casts ast)
  (match ast
    [(list exprs ...)
     (foldl set-union (set) (map get-casts exprs))]
    [(cons first second)
     (set-union (get-casts first) (get-casts second))]
    [(Prog _ expr)
     (get-casts expr)]
    [(Define _ _ _ expr)
     (get-casts expr)]
    [(Uid _ _) (set)]
    [(Var _) (set)]
    [(Quote _) (set)]
    [(Observe expr _)
     (get-casts expr)]
    [(Repeat var start end acc init body)
     (get-casts (list var start end acc init body))]
    [(Let bindings body)
     (set-union (get-casts bindings) (get-casts body))]
    [(Lambda args body)
     (set-union (get-casts args) (get-casts body))]
    [(Op _ operands)
     (get-casts operands)]
    [(Gbox val)
     (get-casts val)]
    [(Gunbox b)
     (get-casts b)]
    [(Gbox-set! b val)
     (set-union (get-casts b) (get-casts val))]
    [(Create-tuple vals)
     (get-casts vals)]
    [(Tuple-proj t idx)
     (get-casts t)]
    [(Gvector len val)
     (set-union (get-casts len) (get-casts val))]
    [(Gvector-set! vect index val)
     (get-casts (list vect index val))]
    [(Gvector-ref vect idx)
     (set-union (get-casts vect) (get-casts idx))]
    [(Dyn-GVector-Ref expr index label)
     (set-union (get-casts expr) (get-casts index))]
    [(Dyn-GVector-Set! expr1 index expr2 type label)
     (get-casts (list expr1 expr2 index))]
    [(Dyn-Tuple-Proj tup idx lbl)
     (set-union (get-casts tup) (get-casts idx))]
    [(App fn args)
     (set-union (get-casts fn) (get-casts args))]
    [(Dyn-Fn-App expr expr* type* label*)
     (set-union (get-casts expr) (set))]
    [(If cond then else)
     (get-casts (list cond then else))]
    [(Begin effects value)
     (set-union (get-casts effects) (get-casts value))]
    [(Letrec bindings body)
     (set-union (get-casts bindings) (get-casts body))]
    [(Cast expr cast)
     (define from (Twosome-type1 cast))
     (define to (Twosome-type2 cast))
     (set-add (get-casts expr) (FromTo from to))]
    [else (error ast)]))

(define (find-inflows casts)
  (if (set-empty? casts)
      (hash)
      (match (set-first casts)
        [(FromTo from (Any n))
         (define rest-casts (find-inflows (set-rest casts)))
         (hash-set rest-casts n (set-add (hash-ref rest-casts n (set)) from))]
        [else (find-inflows (set-rest casts))])))

(module+ test
  (test-equal? "Basic example with 1 variable"
               (find-inflows (set (FromTo (Any 2) (Int))
                                  (FromTo (Int) (Any 1))
                                  (FromTo (Any 1) (Any 2))
                                  (FromTo (Bool) (Any 1))))
               (hash 1 (set (Int) (Bool)) 2 (set (Any 1))))
  (test-equal? "Basic example with 1 variable"
               (find-inflows (set (FromTo (Any 2) (Int))
                                  (FromTo (Any 2) (Any 1))
                                  (FromTo (Dyn) (Any 1))
                                  (FromTo (Any 1) (Any 2))
                                  (FromTo (Bot) (Any 1))))
               (hash 1 (set (Bot) (Dyn) (Any 2)) 2 (set (Any 1)))))

(define (type-union left right)
  (match (cons left right)
    [(cons t t) t] ; for primitives
    [(cons (Bot) t) t]
    [(cons t (Bot)) t]
    [(cons (Dyn) _) (Dyn)]
    [(cons _ (Dyn)) (Dyn)]
    [(cons (Fn n args1 ret1) (Fn n args2 ret2))       ; same arity
     (define new (Fn n (map type-union args1 args2) (type-union ret1 ret2)))
     new]
    [(cons (Fn a1 args1 ret1) (Fn a2 args2 ret2))     ; different arities
     (Dyn)]
    [(cons (GVect t1) (GVect t2))
     (GVect (type-union t1 t2))]
    [else (Dyn)]))   ; by default, dynamic. This should match all the cases where things fell through and didn't match anything else.

(module+ test
  (test-equal? "Bottom and anything"
               (type-union (Bot) (Int))
               (Int))
  (test-equal? "Dyn and whatever"
               (type-union (Dyn) (Bot))
               (Dyn))
  (test-equal? "Fn"
               (type-union (Fn 2 (list (Dyn) (Bot)) (Int))
                           (Fn 2 (list (Int) (Bool)) (Int)))
               (Fn 2 (list (Dyn) (Bool)) (Int)))
  (test-equal? "Fn different arity"
               (type-union (Fn 0 '() (Bool))
                           (Fn 1 (list (Int)) (Bool)))
               (Dyn)))

(define (find-types inflows)
  (define (uses-any? type key)
    (match type
      [(Any n) (equal? key n)]
      [(AnyParam v _) (uses-any? v key)]
      [(AnyReturn v) (uses-any? v key)]
      [(AnyVect v) (uses-any? v key)]
      [(AnyTup v _) (uses-any? v key)]
      [else #f]))
  (define (replacement t key)
    (match t
      [(Any (? (lambda (n) (equal? n key)))) (Dyn)]
      [(Any n) (hash-ref types n (Dyn))]
      [(AnyParam var idx)
       (define var-type (replacement var key))
       (if (Fn? var-type)
           (list-ref (Fn-fmls var-type) idx)
           (Dyn))]
      [(AnyReturn var)
       (define var-type (replacement var key))
       (if (Fn? var-type)
           (Fn-ret var-type)
           (Dyn))]
      [(AnyVect var)
       (define var-type (replacement var key))
       (if (GVect? var-type)
           (GVect-arg var-type)
           (Dyn))]
      [(? any?) (error "implement for ~a" t)]
      ; TODO Any... variants
      [(Fn arity args ret) (Fn arity (map (lambda (x) (replacement x key)) args) (replacement ret key))]
      [(GVect v) (GVect (replacement v key))]
      [(STuple num items) (STuple num (map (lambda (x) (replacement x key)) items))]
      [else t]))
  (define types (make-immutable-hash (map (lambda (key) `(,key . ,(Bot))) (hash-keys inflows))))
  (define keys (hash-keys inflows))
  (define (helper old)
    (for ([key keys])
      (for ([type (hash-ref inflows key)])
        (set! types (hash-set types key (type-union (replacement type key) (hash-ref types key))))))
    (if (equal? old types)
        types
        (helper types)))
  (helper types))

(module+ test
  #;(test-equal? "Cycle"
                 (find-types (hash 1 (set (Any 2) (Fn 0 '() (Int))) 2 (set (Any 1) (Fn 0 '() (Bool)))))
                 (hash 1 (Fn 0 '() (Dyn)) 2 (Fn 0 '() (Dyn))))
  (test-equal? "Self-referential"
               (find-types (hash 1 (set (Fn 2 (list (Any 1) (Any 2)) (Int))
                                        (Fn 2 (list (AnyParam (Any 1) 0) (AnyParam (Any 1) 1)) (AnyReturn (Any 1)))
                                        (AnyParam (Any 1) 0))
                                 2 (set (Int) (AnyParam (Any 1) 1))))
               (hash 1 (Fn 2 (list (Dyn) (Int)) (Int)) 2 (Int)))
  (test-equal? "Self-referential"
               (find-types (hash 1 (set (Fn 2 (list (Any 1) (Any 2)) (Int))
                                        (Fn 2 (list (AnyParam (Any 1) 0) (AnyParam (Any 1) 1)) (AnyReturn (Any 1)))
                                        (AnyParam (Any 1) 0))
                                 2 (set (Int))))
               (hash 1 (Dyn) 2 (Int)))
  )

(define (remove-casts ast types)
  (define (replace-type type types)
    (match type
      [(Any n)
       (hash-ref types n (Dyn))]  ; If not found, just use Dynamic
      [(AnyParam v idx)
       (define var (hash-ref types v (Dyn)))
       (if (not (Fn? var))
           (Dyn)
           (list-ref (Fn-fmls var) idx))]
      [(AnyVect v)
       (define var (hash-ref types v (Dyn)))
       (if (GVect? var)
           (GVect-arg var)
           (Dyn))]
      [(? any?) (error type)]
      [(Fn n fmls ret)
       (Fn n (map (lambda (t) (replace-type t types)) fmls) (replace-type ret types))]
      [(GVect t) (GVect (replace-type t types))]
      [(STuple len args)
       (STuple len (map (lambda (t) (replace-type t types)) args))]
      [else type]))
  (match ast
    [(list exprs ...)
     (map (lambda (node) (remove-casts node types)) exprs)]
    [(cons first second)
     (cons (remove-casts first types) (remove-casts second types))]
    [(Prog a expr)
     (Prog a (remove-casts expr types))]
    [(Define rec? id type expr)
     (Define rec? id type (remove-casts expr types))]
    [(Repeat var start end acc init body)
     (Repeat (remove-casts var types)
             (remove-casts start types)
             (remove-casts end types)
             (remove-casts acc types)
             (remove-casts init types)
             (remove-casts body types))]
    [(Uid _ _) ast]
    [(Var _) ast]
    [(Quote _) ast]
    [(Observe expr a)
     (Observe (remove-casts expr types) a)]
    [(Let bindings body)
     (Let (remove-casts bindings types) (remove-casts body types))]
    [(Lambda args body)
     (Lambda (remove-casts args types) (remove-casts body types))]
    [(Op op operands)
     (Op op (remove-casts operands types))]
    [(Gbox val)
     (Gbox (remove-casts val types))]
    [(Gunbox b)
     (Gunbox (remove-casts b types))]
    [(Gbox-set! b val)
     (Gbox-set! (remove-casts b types)
                (remove-casts val types))]
    [(Create-tuple vals)
     (Create-tuple (remove-casts vals types))]
    [(Tuple-proj t idx)
     (Tuple-proj (remove-casts t types) idx)]
    [(Gvector len val)
     (Gvector (remove-casts len types)
              (remove-casts val types))]
    [(Gvector-set! vect idx val)
     (Gvector-set! (remove-casts vect types)
                   (remove-casts idx types)
                   (remove-casts val types))]
    [(Gvector-ref vect idx)
     (Gvector-ref (remove-casts vect types)
                  (remove-casts idx types))]
    [(App fn args)
     (App (remove-casts fn types) (remove-casts args types))]
    [(Dyn-GVector-Set! expr1 index expr2 type label)
     ;(println "Dyn")
     ;(println expr1)
     ;(println expr2)
     ;(println index)
     ;(println label)
     (println (Dyn-GVector-Set! (remove-casts expr1 types)
                       (remove-casts index types)
                       (remove-casts expr2 types)
                       (replace-type type types)
                       label))
     (Dyn-GVector-Set! (remove-casts expr1 types)
                       (remove-casts index types)
                       (remove-casts expr2 types)
                       (replace-type type types)
                       label)]
    [(Dyn-Fn-App expr expr* type* label*)
     (Dyn-Fn-App (remove-casts expr types)
                 (map (lambda (node) (remove-casts node types)) expr*)
                 (map (lambda (t) (replace-type t types)) type*)
                 label*)]
    [(Dyn-GVector-Ref vect index label)
     (Dyn-GVector-Ref (remove-casts vect types)
                      (remove-casts index types)
                      label)]
    [(Dyn-Tuple-Proj tup idx lbl)
     (Dyn-Tuple-Proj (remove-casts tup types)
                     (remove-casts idx types)
                     lbl)]
    [(If cond then else)
     (If (remove-casts cond types) (remove-casts then types) (remove-casts else types))]
    [(Begin effects value)
     (Begin (remove-casts effects types) (remove-casts value types))]
    [(Letrec bindings body)
     (Letrec (remove-casts bindings types) (remove-casts body types))]
    [(Cast expr cast)
     (define from (replace-type (Twosome-type1 cast) types))
     (define to (replace-type (Twosome-type2 cast) types))
     (define label (Twosome-lbl cast))
     (Cast (remove-casts expr types)
           (Twosome from to label))]
    [else (error ast)]))

(define (flow-judgement-helper casts)
  (define (helper casts)
    (define new-casts (set))
    (define k (set-filter (lambda (c)
                            (define from (FromTo-from c))
                            (define to (FromTo-to c))
                            (and (any? to)
                                 (kindof? from to)))
                          casts))
    (for ([c casts])                             
      (define from (FromTo-from c))
      (define to (FromTo-to c))
      (cond
        ; F-Base & F-Comp are handled already by how we construct the initial set of casts.
        [(and (Any? from) (Any? to))       ; F-Pull
         (define (helper kinds)
           (if (set-empty? kinds)
               (set)
               (set-add (helper (set-rest kinds)) (FromTo (set-first kinds) to))
               ))
         (set! new-casts (set-union new-casts (helper (set-map (set-filter (lambda (c)
                                                                             (equal? (FromTo-to c) from)) k) FromTo-from))))] 
        [(and (not (any? from)) (any? to))   ; F-Factor
         (set! new-casts (set-union new-casts (set (FromTo (type-norm from to) to)
                                                   (FromTo from (type-norm from to)))))]
        [(and (any? from) (not (any? to)))   ; F-Tran
         (define (helper kinds)
           (if (set-empty? kinds)
               (set)
               (set-add (helper (set-rest kinds)) (FromTo (set-first kinds) to))
               ))
         (define casts-kind->to (set-filter (lambda (c)
                                              (equal? (FromTo-to c) from)) k))
         (define kinds (set-map casts-kind->to FromTo-from))
         (define dyn-consistent-kinds (set-filter (lambda (kind)
                                                    (consistent? kind to))
                                                  kinds))
         (set! new-casts (set-union new-casts (helper dyn-consistent-kinds)))]
        [(and (Dyn? from) (Fn? to))          ; F-ExpFunL
         (define n (length (Fn-fmls to)))
         (set! new-casts (set-add new-casts (FromTo (Fn n (build-list n (lambda (i) (Dyn))) (Dyn)) to)))]
        [(and (Dyn? from) (GRef? to))        ; F-ExpBoxL
         (set! new-casts (set-add new-casts (FromTo (GRef (Dyn)) to)))]
        [(and (Dyn? from) (MRef? to))        ; F-ExpBoxL
         (set! new-casts (set-add new-casts (FromTo (MRef (Dyn)) to)))]
        [(and (Dyn? from) (GVect? to))       ; F-ExpVectL
         (set! new-casts (set-add new-casts (FromTo (GVect (Dyn)) to)))]
        [(and (Dyn? from) (MVect? to))       ; F-ExpVectL
         (set! new-casts (set-add new-casts (FromTo (MVect (Dyn)) to)))]
        [(and (Dyn? from) (STuple? to))      ; F-ExpTupL
         (define n (STuple-num to))
         (set! new-casts (set-add new-casts (FromTo (STuple n (build-list n (lambda (x) (Dyn)))) to)))]
        [(and (Fn? from) (Dyn? to))          ; F-ExpFunR
         (define n (length (Fn-fmls from)))
         (set! new-casts (set-add new-casts (FromTo from (Fn n (build-list n (lambda (i) (Dyn))) (Dyn)))))]
        [(and (GRef? from) (Dyn? to))        ; F-ExpBoxR
         (set! new-casts (set-add new-casts (FromTo from (GRef (Dyn)))))]
        [(and (MRef? from) (Dyn? to))        ; F-ExpBoxR
         (set! new-casts (set-add new-casts (FromTo from (MRef (Dyn)))))]
        [(and (GVect? from) (Dyn? to))       ; F-ExpVectR
         (set! new-casts (set-add new-casts (FromTo from (GVect (Dyn)))))]
        [(and (MVect? from) (Dyn? to))       ; F-ExpVectR
         (set! new-casts (set-add new-casts (FromTo from (MVect (Dyn)))))]
        [(and (STuple? from) (Dyn? to))      ; F-ExpTupR
         (define n (STuple-num from))
         (set! new-casts (set-add new-casts (FromTo from (STuple n (build-list n (lambda (x) (Dyn)))))))]
        [(and (Fn? from) (Fn? to) (equal? (Fn-arity to) (Fn-arity from)))  ; F-SplitFun
         (define new-casts-param (list->set (map FromTo (Fn-fmls to) (Fn-fmls from))))
         (define new-cast-ret (FromTo (Fn-ret from) (Fn-ret to)))
         (set! new-casts (set-union new-casts new-casts-param))
         (set! new-casts (set-add new-casts new-cast-ret))] 
        [(and (GRef? from) (GRef? to))       ; F-SplitBox
         (set! new-casts (set-add new-casts (FromTo (GRef-arg from) (GRef-arg to))))]
        [(and (MRef? from) (MRef? to))       ; F-SplitBox
         (set! new-casts (set-add new-casts (FromTo (MRef-arg from) (MRef-arg to))))]
        [(and (GVect? from) (GVect? to)) ; F-SplitVect
         (set! new-casts (set-add new-casts (FromTo (GVect-arg from) (GVect-arg to))))]
        [(and (MVect? from) (MVect? to)) ; F-SplitVect
         (set! new-casts (set-add new-casts (FromTo (MVect-arg from) (MVect-arg to))))]
        [(and (STuple? from) (STuple? to) (>= (STuple-num to) (STuple-num from)))
         (set! new-casts (set-union new-casts (list->set (map FromTo (STuple-items to) (STuple-items from)))))]
        ))
    (if (subset? new-casts casts)
        (set-filter (lambda (c) (not (equal? (FromTo-from c)
                                             (FromTo-to c)))) casts)
        (helper (set-union new-casts casts))))
  (define new-casts (helper casts))
  new-casts)

(define (flow-judgement ast)
  (println "running flow judgement!")
  ;(println ast)
  (define casts (get-casts ast))
  ;(println casts)
  (define new-casts (flow-judgement-helper casts))
  ;(println new-casts)
  (define inflows (find-inflows new-casts))
  ;(println inflows)
  (define types (find-types inflows))
  ;(println types)
  (define less-casts (remove-casts ast types))
  ;(println less-casts)
  less-casts)
