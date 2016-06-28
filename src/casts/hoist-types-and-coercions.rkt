#lang typed/racket/base
#|-----------------------------------------------------------------------------+
|Pass: src/casts/hoist-types-and-coercions                                     |
+------------------------------------------------------------------------------+
|Author:                                                                       |
| (original hoist-types)  Deyaaeldeen Almahallawi (dalmahal@indiana.edu)       |
| (hoist coercions added) Andre Kuhlenschmidt (akuhlens@indiana.edu)           |
+------------------------------------------------------------------------------+
|Description: Hoist the allocation of all types and static coercions to the 
| initialization of the program. Unify there allocations so that any two
| structurally similar structures are the same runtime object. Coercions may
| still allocate new coercions that are equivalent to the hoisted so pointer
| equality is less meaninfull in this case. But it should limit greatly the
| amount of allocation occuring at runtime for coercions. 
+------------------------------------------------------------------------------+
|Input Grammar Cast or Coercion Language 3
|Output Grammar Cast or Coercion Language 3.1
+-----------------------------------------------------------------------------|#
;; The define-pass syntax
(require "../helpers.rkt"
         "../growable-vector.rkt"
         "../unique-counter.rkt"
         "../errors.rkt"
         "../configuration.rkt"
         "../language/cast-or-coerce3.rkt"
         "../language/lambda0.rkt"
         racket/match
         racket/list)

;; Only the pass is provided by this module
(provide hoist-types-and-coercions)

(: hoist-types-and-coercions :
   Cast-or-Coerce3-Lang Config -> Lambda0-Lang)
(define (hoist-types-and-coercions prgm config)
  (match-define (Prog (list prgm-name next-unique-number prgm-type) exp)
    prgm)

  ;; All mutable state of the pass
  (define unique-state : Unique-Counter (make-unique-counter next-unique-number))
  (define type-table   : Type-Table   (make-type-table))
  (define crcn-table   : Crcn-Table   (make-crcn-table))
  
  (define type->immediate
    (identify-type! unique-state type-table))
  
  (define coercion->immediate
    (identify-coercion! unique-state type-table crcn-table))
  
  ;; Map through the expression mutating the above state to collect
  ;; all type and coercions.
  (define new-exp : L0-Expr
    (map-hoisting-thru-Expr type->immediate coercion->immediate exp))

  ;; Compose the mapping with extracting the state of the computation
  ;; to build a new program.
  
  (Prog (list prgm-name (unique-counter-next! unique-state) prgm-type)
        (Let-Static* (type-table->list type-table)
                     (crcn-table->list crcn-table)
                     new-exp)))

;; Type Index maps types to the identifiers for there binding site.

;; Type-Table a two part table that allow for types to be easily
;; hash-cons together. The car is a map of types to names and the cdr
;; is a reference to a vector that stores bindings for types in order
;; of their dependency where the bindings at index 0 don't depend on
;; any other binding, but the bindings at 5 depend on level 4 bindings
;; and possibly lower bindings. The boxing of the vector allows
;; for a larger vector to be used if the dependency tree grows too
;; deep.

;; Type And Coercion State Setup

(define-type Type-Table (Pair Type-Index Sorted-Bnd-Type*))

(define-type Type-Index (HashTable Compact-Type (Static-Id Uid)))

(define-type Sorted-Bnd-Type* (GVectorof Bnd-Type*))

(define-type Crcn-Table (Pair Crcn-Index Sorted-Bnd-Crcn*))

(define-type Crcn-Index (HashTable Compact-Coercion (Static-Id Uid)))

(define-type Sorted-Bnd-Crcn* (GVectorof Bnd-Crcn*))

(: make-type-table : -> Type-Table)
(define (make-type-table)
  (cons (ann (make-hash) Type-Index)
        (ann (make-gvector 8 '()) Sorted-Bnd-Type*)))

(: make-crcn-table : -> Crcn-Table)
(define (make-crcn-table)
  (cons (ann (make-hash) Crcn-Index) 
        (ann (make-gvector 8 '()) Sorted-Bnd-Crcn*)))

(: type-table->list (Type-Table -> Bnd-Type*))
(define (type-table->list tt)
  (append* (gvector->list (cdr tt))))

(: crcn-table->list : Crcn-Table -> Bnd-Crcn*)
(define (crcn-table->list x)
  (append* (gvector->list (cdr x))))


(define-type (Sorted-Bnd* A) (GVectorof (Listof (Pair Uid A))))

(: sorted-bnd*-add! (All (A) (Sorted-Bnd* A) Nat (Pair Uid A) -> Void))
(define (sorted-bnd*-add! bnd* rank new-bnd)
  (define old-bnd* : (Listof (Pair Uid A)) 
    (if (< rank (gvector-length bnd*))
        (gvector-ref bnd* rank)
        '()))
  (gvector-set! bnd* rank (cons new-bnd old-bnd*)))

;; This factors out the common code between type and
;; coercion registration
(: table-identify!
   (All (A)
    (Unique-Counter (HashTable A (Static-Id Uid)) (Sorted-Bnd* A)
     -> (Nat A -> (Values (Static-Id Uid) Nat)))))
(define ((table-identify! unique table sorted-bnd*) rank-1 val)
  (define sid? : (Option (Static-Id Uid)) (hash-ref table val #f))
  (define rank : Nat (add1 rank-1))
  (cond
    [sid? (values sid? rank)]
    [else
     (define uid (Uid "static" (unique-counter-next! unique)))
     (define tid (Static-Id uid))
     (sorted-bnd*-add! sorted-bnd* rank (cons uid val))
     (hash-set! table val tid)
     (values tid rank)]))

;; Make all types of equal structure the same structure
;; this is essentially a compile time hash-consing of the types
(: identify-type! (Unique-Counter Type-Table -> (Schml-Type -> Prim-Type)))
(define (identify-type! us tt)
  (match-define (cons ti sb) tt)

  (: ti! : Nat Compact-Type -> (Values (Static-Id Uid) Nat))
  (define ti! (table-identify! us ti sb))
  
  (lambda ([type : Schml-Type]) : Prim-Type
    ;; Here the Nonnegative Integer creates a partial order which
    ;; Identifies the order in which types can be constructed.
    ;; It can be seen as counting the number of types that must be
    ;; constructed before this type can be constructed.
    (: recur (Schml-Type -> (Values Prim-Type Nat)))
    (define (recur t)
      (match t
        [(Dyn)  (values DYN-TYPE  0)]
        [(Unit) (values UNIT-TYPE 0)]
        [(Int)  (values INT-TYPE  0)]
        [(Bool) (values BOOL-TYPE 0)]
        [(Fn ar (app recur* t* m) (app recur t n))
         (ti! (max m n) (Fn ar t* t))]
        [(GRef (app recur t n))
         (ti! n (GRef t))]
        [(MRef (app recur t n))
         (ti! n (MRef t))]
        [(GVect (app recur t n))
         (ti! n (GVect t))]
        [(MVect (app recur t n))
         (ti! n (MVect t))]
        [other (error 'hoist-types/identify-type! "unmatched ~a" other)]))
    (: recur* ((Listof Schml-Type) -> (Values (Listof Prim-Type) Nat)))
    (define (recur* t*)
      (match t*
        ['() (values '() 0)]
        [(cons (app recur t m) (app recur* t* n))
         (values (cons t t*) (max n m))]))
    ;; Discard the rank
    (let-values ([(t r) (recur type)])
      t)))

(: identify-coercion! : Unique-Counter Type-Table Crcn-Table
   -> (Schml-Coercion -> Immediate-Coercion))
(define (identify-coercion! us tt ct)
  ;; This is basically the same as identify-type! above.
  (match-define (cons ci sb*) ct)
  (define ti! (identify-type! us tt))

  (: ci! : Nat Compact-Coercion -> (values (Static-Id Uid) Nat))
  (define ci! (table-identify! us ci sb*))
  
  (lambda ([crcn : Schml-Coercion])
    : Immediate-Coercion
    (: recur : Schml-Coercion -> (Values Immediate-Coercion Nat))
    (define (recur c)
      (match c
        [(Identity)
         (values (Identity) 0)]
        [(Failed l)
         (ci! 0 (Failed l))]
        [(Project (app ti! t) l)
         (ci! 0 (Project t l))]
        [(Inject (app ti! t))
         (ci! 0 (Inject t))]
        [(Sequence (app recur f m) (app recur s n))
         (ci! (max m n) (Sequence f s))]
        [(Fn i (app recur* a* m) (app recur r n))
         (ci! (max m n) (Fn i a* r))]
        [(Ref (app recur r m) (app recur w n))
         (ci! (max m n) (Ref r w)) ]
        [other (error 'hoist-types/coercion "unmatched ~a" other)]))
    (: recur* (Schml-Coercion* -> (Values (Listof Immediate-Coercion) Nat)))
    (define (recur* t*)
      (match t*
        ['() (values '() 0)]
        [(cons (app recur t m) (app recur* t* n))
         (values (cons t t*) (max n m))]))
    (let-values ([(c r) (recur crcn)])
      c)))
    
(: map-hoisting-thru-Expr :
   (Schml-Type -> Prim-Type)
   (Schml-Coercion -> Immediate-Coercion)
   CoC3-Expr
   -> L0-Expr)
;; Recur through all valid language forms collecting the types
;; in the type table and replacing them with references to the
;; global identifiers
(define (map-hoisting-thru-Expr type->imdt crcn->imdt exp)
  ;; Recur through expression replacing types with their primitive counterparts
  (: recur (CoC3-Expr -> L0-Expr))
  (define (recur exp)
    ;;(printf "ht: ~a\n" exp) (flush-output (current-output-port))
    (match exp
      ;; Interesting cases
      [(Type (app type->imdt t)) (Type t)]
      [(Quote-Coercion (app crcn->imdt c)) (Quote-Coercion c)]
      ;; Every other case is just a boring flow agnostic tree traversal
      [(Code-Label u)
       (Code-Label u)]
      [(Labels (app recur-bnd-code* b*) (app recur e))
       (Labels b* e)]
      [(App-Code (app recur e) (app recur* e*))
       (App-Code e e*)]
      [(Lambda f* (Castable c (app recur e)))
       (Lambda f* (Castable c e))]
      [(Fn-Caster (app recur e))
       (Fn-Caster e)]
      [(App-Fn (app recur e) (app recur* e*))
       (App-Fn e e*)]
      [(App-Fn-or-Proxy u (app recur e) (app recur* e*))
       (App-Fn-or-Proxy u e e*)]
      [(Fn-Proxy i (app recur e1) (app recur e2))
       (Fn-Proxy i e1 e2)]
      [(Fn-Proxy-Huh (app recur e))
       (Fn-Proxy-Huh e)]
      [(Fn-Proxy-Closure (app recur e))
       (Fn-Proxy-Closure e)]
      [(Fn-Proxy-Coercion (app recur e))
       (Fn-Proxy-Coercion e)]
      [(Compose-Coercions (app recur e1) (app recur e2))
       (Compose-Coercions e1 e2)]
      [(Id-Coercion-Huh (app recur e))
       (Id-Coercion-Huh e)]
      [(Fn-Coercion-Huh (app recur e))
       (Fn-Coercion-Huh e)]
      [(Make-Fn-Coercion u (app recur e1)(app recur e2)(app recur e3))
       (Make-Fn-Coercion u e1 e2 e3)]
      [(Compose-Fn-Coercion u (app recur e1) (app recur e2))
       (Compose-Fn-Coercion u e1 e2)]
      [(Fn-Coercion (app recur* e*)(app recur e))
       (Fn-Coercion e* e)]
      [(Fn-Coercion-Arg (app recur e1)(app recur e2))
       (Fn-Coercion-Arg e1 e2)]
      [(Fn-Coercion-Return (app recur e))
       (Fn-Coercion-Return e)]
      [(Ref-Coercion (app recur e1) (app recur e2))
       (Ref-Coercion e1 e2)]
      [(Ref-Coercion-Huh (app recur e))
       (Ref-Coercion-Huh e)]
      [(Ref-Coercion-Read (app recur e))
       (Ref-Coercion-Read e)]
      [(Ref-Coercion-Write (app recur e))
       (Ref-Coercion-Write e)]
      [(Sequence-Coercion (app recur e1) (app recur e2))
       (Sequence-Coercion e1 e2)]
      [(Sequence-Coercion-Huh (app recur e))
       (Sequence-Coercion-Huh e)]
      [(Sequence-Coercion-Fst (app recur e))
       (Sequence-Coercion-Fst e)]
      [(Sequence-Coercion-Snd (app recur e))
       (Sequence-Coercion-Snd e)]
      [(Project-Coercion (app recur e1) (app recur e2))
       (Project-Coercion e1 e2)]
      [(Project-Coercion-Huh (app recur e))
       (Project-Coercion-Huh e)]
      [(Project-Coercion-Type (app recur e))
       (Project-Coercion-Type e)]
      [(Project-Coercion-Label (app recur e))
       (Project-Coercion-Label e)]
      [(Inject-Coercion (app recur e))
       (Inject-Coercion e)]
      [(Inject-Coercion-Type (app recur e))
       (Inject-Coercion-Type e)]
      [(Inject-Coercion-Huh (app recur e))
       (Inject-Coercion-Huh e)]
      [(Failed-Coercion (app recur e))
       (Failed-Coercion e)]
      [(Failed-Coercion-Huh (app recur e))
       (Failed-Coercion-Huh e)]
      [(Failed-Coercion-Label (app recur e))
       (Failed-Coercion-Label e)]
      [(Type-Dyn-Huh (app recur e))
       (Type-Dyn-Huh e)] 
      [(Type-Fn-arg (app recur e) (app recur i))
       (Type-Fn-arg e i)]
      [(Type-Fn-return (app recur e))
       (Type-Fn-return e)]
      [(Type-Fn-arity (app recur e))
       (Type-Fn-arity e)]
      [(Type-Fn-Huh (app recur e))
       (Type-Fn-Huh e)]
      [(Type-GRef-Of (app recur e))
       (Type-GRef-Of e)]
      [(Type-GVect-Of (app recur e))
       (Type-GVect-Of e)]
      [(Type-GRef-Huh (app recur e))
       (Type-GRef-Huh e)]
      [(Type-GVect-Huh (app recur e))
       (Type-GVect-Huh e)]
      [(Type-Tag (app recur e))
       (Type-Tag e)]
      [(Tag s)
       (Tag s)]
      [(Dyn-tag (app recur e))
       (Dyn-tag e)]
      [(Dyn-immediate (app recur e))
       (Dyn-immediate e)]
      [(Dyn-type (app recur e))
       (Dyn-type e)]
      [(Dyn-value (app recur e))
       (Dyn-value e)]
      [(Dyn-make (app recur e1) (app recur e2))
       (Dyn-make e1 e2)]
      [(Letrec (app recur-bnd* b*) (app recur e))
       (Letrec b* e)]
      [(Let (app recur-bnd* b*) (app recur e))
       (Let b* e)]
      [(Var i)
       (Var i)]
      [(If (app recur t) (app recur c) (app recur a))
       (If t c a)]
      [(Begin (app recur* e*) (app recur e))
       (Begin e* e)]
      [(Repeat i (app recur e1) (app recur e2) (app recur e3))
       (Repeat i e1 e2 e3)]
      [(Op p (app recur* e*))
       (Op p e*)]
      [(Quote k) (Quote k)]
      [(Blame (app recur e))
       (Blame e)]
      [(Observe (app recur e) t)
       (Observe e t)]
      [(Unguarded-Box (app recur exp))
       (Unguarded-Box exp)]
      [(Unguarded-Box-Ref (app recur exp))
       (Unguarded-Box-Ref exp)]
      [(Unguarded-Box-Set! (app recur exp1) (app recur exp2))
       (Unguarded-Box-Set! exp1 exp2)]
      [(Unguarded-Vect (app recur exp1) (app recur exp2))
       (Unguarded-Vect exp1 exp2)]
      [(Unguarded-Vect-Ref (app recur exp1) (app recur exp2))
       (Unguarded-Vect-Ref exp1 exp2)]
      [(Unguarded-Vect-Set! (app recur exp1) (app recur exp2) (app recur exp3))
       (Unguarded-Vect-Set! exp1 exp2 exp3)]
      [(Guarded-Proxy-Huh (app recur exp))
       (Guarded-Proxy-Huh exp)]
      [(Guarded-Proxy (app recur e1) r)
       (match r
         [(Twosome (app recur e2) (app recur e3) (app recur e4))
          (Guarded-Proxy e1 (Twosome e2 e3 e4))]
         [(Coercion (app recur e2))
          (Guarded-Proxy e1 (Coercion e2))])]
      [(Guarded-Proxy-Ref (app recur exp))
       (Guarded-Proxy-Ref exp)]
      [(Guarded-Proxy-Source (app recur exp))
       (Guarded-Proxy-Source exp)]
      [(Guarded-Proxy-Target (app recur exp))
       (Guarded-Proxy-Target exp)]
      [(Guarded-Proxy-Blames (app recur exp))
       (Guarded-Proxy-Blames exp)]
      [(Guarded-Proxy-Coercion (app recur exp))
       (Guarded-Proxy-Coercion exp)]
      [(? string? x) (error 'hoist-types/string)]
      [other (error 'hoist-types/expr "unmatched ~a" other)]))
  ;; Recur through other type containing ast forms
  (: recur* (CoC3-Expr* -> L0-Expr*))
  (define (recur* e*) (map recur e*))
  
  (: recur-bnd* (CoC3-Bnd* -> L0-Bnd*))
  (define (recur-bnd* b*)
    (map (lambda ([b : CoC3-Bnd])
           (cons (car b) (recur (cdr b))))
         b*))

  (: recur-bnd-code* (CoC3-Bnd-Code* -> L0-Bnd-Code*))
  (define (recur-bnd-code* b*)
    (map (lambda ([b : CoC3-Bnd-Code])
           (match-let ([(cons a (Code u* e)) b])
             (cons a (Code u* (recur e)))))
         b*))
  
  ;; Body of ht-expr just start the expression traversal
  (recur exp))


;; A few simple tests to make sure the pass isn't completely broken
(module+ test)