#lang racket

#|
Implementation of flow judgement ("Ins and Outs of Gradual Type inference")
|#

(require "../language/forms.rkt")

(provide flow-judgement)

(define (set-filter proc s)
  (cond
    [(set-empty? s) (set)]
    [(proc (set-first s)) (set-add (set-filter proc (set-rest s)) (set-first s))]
    [else (set-filter proc (set-rest s))]))

(define (1+ n)
  (+ 1 n))

(struct FromTo (from to) #:transparent)
(struct AnyParam (var index) #:transparent) ; index is which paramter it is
(struct AnyReturn (var) #:transparent)
(struct AnyField (var key) #:transparent) ; key is which field is being accessed from the obj

(define (any? var)
  (or (Any? var)
      (AnyParam? var)
      (AnyReturn? var)
      (AnyField? var)))

(define (type-norm type var)
  (define (fn-type-norm arity params ret)
    (define counter
      (let ([n 0])
        (lambda ()
          (set! n (1+ n))
          n)))
    (Fn arity (map (lambda (x) (AnyParam var (counter))) params) (AnyReturn var)))
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
    [(Fn arity params ret) (fn-type-norm arity params ret)]
    [else 'TODO]))

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
    [(Fn arity params ret) (fn-kindof? 1 params ret var)]
    [else #f])) ; TODO rest of these

(define (get-casts ast)
  (match ast
    [(list exprs ...)
     (foldl set-union (set) (map get-casts exprs))]
    [(cons first second)
     (set-union (get-casts first) (get-casts second))]
    [(Prog _ expr)
     (get-casts expr)]
    [(Uid _ _) (set)]
    [(Var _) (set)]
    [(Quote _) (set)]
    [(Observe expr _)
     (get-casts expr)]
    [(Let bindings body)
     (set-union (get-casts bindings) (get-casts body))]
    [(Lambda args body)
     (set-union (get-casts args) (get-casts body))]
    [(Op _ operands)
     (get-casts operands)]
    [(App fn args)
     (set-union (get-casts fn) (get-casts args))]
    [(Dyn-Fn-App expr expr* type* label*)
     (set-union (get-casts expr) (set))
     ]
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

(define (type-union left right)
  (match (cons left right)
    [(cons (Bot) t) t]
    [(cons t (Bot)) t]
    [(cons (Dyn) _) (Dyn)]
    [(cons _ (Dyn)) (Dyn)]
    [else (error 'TODO)]))

(define (find-types inflows)
  (define types (make-immutable-hash (map (lambda (key) `(,key . ,(Bot))) (hash-keys inflows))))
  types
  (define (helper keys)
    (for ([key keys])
      (for ([type (hash-ref inflows key)])
         (set! types (hash-set types key (type-union type (hash-ref types key))))))
    types)
  (helper (hash-keys inflows)))

(define (remove-casts ast types)
  (define (replace-type type types)
    (match type
      [(Any n)
       (hash-ref types n (Dyn))]  ; If not found, just use Dynamic
      [(Fn n fmls ret)
       (Fn n (map (lambda (t) (replace-type t types)) fmls) (replace-type ret types))]
      [else type]))
  (match ast
    [(list exprs ...)
     (map (lambda (node) (remove-casts node types)) exprs)]
    [(cons first second)
     (cons (remove-casts first types) (remove-casts second types))]
    [(Prog a expr)
     (Prog a (remove-casts expr types))]
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
    [(App fn args)
     (App (remove-casts fn types) (remove-casts args types))]
    [(Dyn-Fn-App expr expr* type* label*)
     (Dyn-Fn-App (remove-casts expr types)
                 (map (lambda (node) (remove-casts node types)) expr*)
                 (map (lambda (t) (replace-type t types)) type*)
                 label*)]
    [(If cond then else)
     (If (remove-casts cond types) (remove-casts then types) (remove-casts else types))]
    [(Begin effects value)
     (Begin (remove-casts effects types) (remove-casts value types))]
    [(Letrec bindings body)
     (Letrec (remove-casts bindings types) (remove-casts body types))]
    [(Cast expr cast)
    ; (println ast)
     (define from (Twosome-type1 cast))
     (define to (Twosome-type2 cast))
     (define label (Twosome-lbl cast))
     (cond
       [(Any? from)
        (define from-any (hash-ref types (Any-uid from) (Dyn)))
        (if (equal? from-any to)
            (remove-casts expr types)
            (Cast (remove-casts expr types) (Twosome (replace-type from-any types)
                                                     (replace-type to types)
                                                     label)))]
       [(Any? to)
        (define to-any (hash-ref types (Any-uid to) (Dyn)))
        (if (equal? from to-any)
            (remove-casts expr types)
            (Cast (remove-casts expr types) (Twosome (replace-type from types)
                                                     (replace-type to-any types)
                                                     label)))]
       [else (Cast (remove-casts expr types) (Twosome (replace-type from types)
                                                      (replace-type to types)
                                                      label))])]
    [else (error ast)]))

(define (flow-judgement ast)
  (println "running flow judgement!")
  (define casts (get-casts ast))
 ; (println casts)
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
        [(and (Any? from) (Any? to))
         (define (helper kinds)
           (if (set-empty? kinds)
               (set)
               (set-add (helper (set-rest kinds)) (FromTo (set-first kinds) to))
               ))
         (set! new-casts (set-union new-casts (helper (set-map (set-filter (lambda (c)
                                                                             (equal? (FromTo-to c) from)) k) FromTo-from))))] ; F-Pull
        [(and (not (Any? from)) (Any? to))
         (set! new-casts (set-union new-casts (set (FromTo (type-norm from to) to)
                                                   (FromTo from (type-norm from to)))))] ; F-Factor
        [(and (Any? from) (not (Any? to)))
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
         (set! new-casts (set-union new-casts (helper dyn-consistent-kinds)))] ; F-Tran
        [(and (Dyn? from) (Fn? to))
         (define n (length (Fn-fmls to)))
         (set! new-casts (set-add new-casts (FromTo (Fn n (build-list n (lambda (i) (Dyn))) (Dyn)) to)))];[] ; F-ExpFunL
        #;[(and (Dyn? from) (t-obj? to))
           (define (obj-with-anys o)
             (define keys (hash-keys (t-obj-pairs o)))
             (define tmp (hash))
             (for ([k keys])
               (set! tmp (hash-union tmp (hash k (t-dyn)))))
             (t-obj tmp)
             )
           (set! new-casts (set-add new-casts (FromTo (obj-with-anys to) to)))] ; F-ExpObjL
        [(and (Fn? from) (Dyn? to))
         (define n (length (Fn-fmls from)))
         (set! new-casts (set-add new-casts (FromTo from (Fn n (build-list n (lambda (i) (Dyn))) (Dyn)))))] ; F-ExpFunR
        #;[(and (Dyn? to) (t-obj? from))
           (define (obj-with-anys o)
             (define keys (hash-keys (t-obj-pairs o)))
             (define tmp (hash))
             (for ([k keys])
               (set! tmp (hash-union tmp (hash k (t-dyn)))))
             (t-obj tmp)
             )
           (set! new-casts (set-add new-casts (FromTo from (obj-with-anys from))))] ; F-ExpObjR
        [(and (Fn? from) (Fn? to) (equal? (Fn-arity to) (Fn-arity from)))
         (define new-casts-param (list->set (map FromTo (Fn-fmls from) (Fn-fmls to))))
         (define new-cast-ret (FromTo (Fn-ret from) (Fn-ret to)))
         (set! new-casts (set-union new-casts new-casts-param))
         (set! new-casts (set-add new-casts new-cast-ret))] ; F-SplitFun
        #;[(and (t-obj? from) (t-obj? to) (hash-keys-subset? (t-obj-pairs to) (t-obj-pairs from)))
           (define to-h (t-obj-pairs to))
           (define from-h (t-obj-pairs from))
           (for ([key (hash-keys to-h)])
             (define new-cast (FromTo (hash-ref from-h key) (hash-ref to-h key)))
             (set! new-casts (set-add new-casts new-cast)))]  ; F-SplitObj
        ))
    (if (subset? new-casts casts)
        (set-filter (lambda (c) (not (equal? (FromTo-from c)
                                             (FromTo-to c)))) casts)
        (helper (set-union new-casts casts))))
  (define new-casts (helper casts))
  ; (println new-casts)
  (define inflows (find-inflows new-casts))
  (define types (find-types inflows))
  (define less-casts (remove-casts ast types))
 ; (println less-casts)
  less-casts)
