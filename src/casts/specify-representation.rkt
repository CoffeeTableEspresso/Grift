#lang typed/racket/base/no-check
#|------------------------------------------------------------------------------+
|Pass: src/casts/specify-representation
+-------------------------------------------------------------------------------+
|Author: Andre Kuhlenshmidt (akuhlens@indiana.edu)                              |
+-------------------------------------------------------------------------------+
Description: This pass exposes the memory layout of aspects of the program.
After this pass language complexity decreases greatly! But all operations are
exposed as the effects that they truelly are. Lets bindings become assignments,
but a static single assignment is implicitly maintained.
+------------------------------------------------------------------------------|#
;; The define-pass syntax
(require
 (for-syntax
  racket/list  
  syntax/parse 
  racket/syntax
  "../language/forms.rkt")
 racket/list
 racket/match
 "../configuration.rkt"
 "../errors.rkt"
 "../logging.rkt"
 "../language/forms.rkt"
 "../language/syntax.rkt"
 "./memory-layout-helpers.rkt"
 "./constants-and-codes.rkt")

;; Only the pass is provided by this module
(provide
 specify-representation)

(: specify-representation (Cast-or-Coerce6-Lang -> Data0-Lang))
(define (specify-representation prgm)
  (match-define
    (Prog (list name next type)
      (Static* (list
                mu-type-bnd*
                type-bnd*
                mu-crcn-bnd*
                crcn-bnd*
                code-bnd*
                closure*
                const-bnd*)
               exp))
    prgm)
  (define unique (make-unique-counter next))
  (parameterize ([current-unique-counter unique])
    (set-box! boxed-bnd-code* '())
    (set-box! mk-fn-coercion-code-label? #f)
    (set-box! mk-tuple-coercion-code-label? #f)
    (set-box! coerce-tuple-code-label? #f)
    (set-box! cast-tuple-code-label? #f)
    (set-box! hashcons-type-code-label? #f)
    (set-box! access-type-hashcode-label? #f)
    (set-box! calculate-type-hashcode-label? #f)

    (define const-id* : Uid* (map (inst car Uid Any) const-bnd*))
    (define init-const* : (Listof D0-Expr)
      (for/list ([b const-bnd*])
        (Assign (car b) (sr-expr (hash) empty-index-map (cdr b))))) 
    (define new-exp : D0-Expr (sr-expr (hash) empty-index-map exp))
    (define new-code* : (Bnd* (Fun D0-Expr))
      (for/list ([b code-bnd*])
        (match-define (cons l (Code p* e)) b)
        (cons l (Code p* (sr-expr (hash) empty-index-map e)))))
    (define-values (static-closure-code*
                    static-closure-id*
                    static-closure-alloc*
                    static-closure-init*)
      (sr-closures closure*))
    (define-values (alloc-mu-type* init-mu-type*)
      (for/lists ([alloc-mu-type* : D0-Expr*] [init-mu-type* : D0-Expr*])
                 ([mu-type-bnd mu-type-bnd*])
        (allocate-bound-mu-type mu-type-bnd)))
    (define-values (alloc-mu-crcn* init-mu-crcn*)
      (for/lists ([alloc-mu-crcn* : D0-Expr*] [init-mu-crcn* : D0-Expr*])
                 ([mu-crcn-bnd mu-crcn-bnd*])
        (allocate-bound-mu-crcn mu-crcn-bnd)))
    (define init-type*  : D0-Expr* (map allocate-bound-type type-bnd*))
    (define init-crcn*  : D0-Expr* (map allocate-bound-coercion crcn-bnd*))
    (define mu-type-id* : Uid*     (map (inst car Uid Any) mu-type-bnd*))
    (define type-id*    : Uid*     (map (inst car Uid Any) type-bnd*))
    (define mu-crcn-id* : Uid*     (map (inst car Uid Any) mu-crcn-bnd*))
    (define crcn-id*    : Uid*     (map (inst car Uid Any) crcn-bnd*))
    (define new-next    : Nat      (unique-counter-next! unique))
    (define bnd-code*   : D0-Bnd-Code* (unbox boxed-bnd-code*))
    (Prog (list name new-next type)
      (GlobDecs (append mu-type-id* type-id*
                        mu-crcn-id* crcn-id*
                        static-closure-id*
                        const-id*)
        (Labels (append bnd-code*
                        new-code*
                        static-closure-code*)
          (Begin (append alloc-mu-type*
                         init-type*
                         init-mu-type*
                         alloc-mu-crcn*
                         init-crcn*
                         init-mu-crcn*
                         static-closure-alloc*
                         static-closure-init*
                         init-const*)
                 new-exp))))))

;; Env must be maintained as a mapping from uids to how to access those
;; values. This is important because uid references to variable inside a
;; closure must turn into memory loads.

(define-type IndexMap (Uid Uid -> Nat))

(: mk-fn-coercion-code-label? (Boxof (Option (Code-Label Uid))))
(define mk-fn-coercion-code-label? (box #f))

(: coerce-tuple-code-label? (Boxof (Option (Code-Label Uid))))
(define coerce-tuple-code-label? (box #f))

(: cast-tuple-code-label? (Boxof (Option (Code-Label Uid))))
(define cast-tuple-code-label? (box #f))

(: mk-tuple-coercion-code-label? (Boxof (Option (Code-Label Uid))))
(define mk-tuple-coercion-code-label? (box #f))



(: tuple-type-glb ((Code-Label Uid) -> ((Var Uid) (Var Uid) -> D0-Expr)))
(define ((tuple-type-glb tglb-label) t1 t2)
  (define-track-next-uid!$ hrt)
  (begin$
    (assign$ t1-count
      (sr-tagged-array-ref t1 TYPE-TUPLE-TAG TYPE-TUPLE-COUNT-INDEX))
    (assign$ t2-count
      (sr-tagged-array-ref t2 TYPE-TUPLE-TAG TYPE-TUPLE-COUNT-INDEX))
    (assign$ smaller-count (If (op$ < t1-count t2-count) t1-count t2-count))
    (assign$ bigger-count (If (op$ > t1-count t2-count) t1-count t2-count))
    (assign$ rt (op$ Alloc (op$ + bigger-count TYPE-TUPLE-ELEMENTS-OFFSET)))
    (assign$ iters (op$ + TYPE-TUPLE-ELEMENTS-OFFSET smaller-count))
    (assign$ tagged-rt (sr-tag-value rt TYPE-TUPLE-TAG))
    (repeat$ (i TYPE-TUPLE-ELEMENTS-OFFSET iters) (_ UNIT-IMDT)
      (assign$ t1a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
      (assign$ t2a (sr-tagged-array-ref t2 TYPE-TUPLE-TAG i))
      (assign$ t-glb (app-code$ tglb-label t1a t2a))
      (sr-array-set! rt i t-glb))
    (cond$
     [(op$ > t1-count t2-count)
      (assign$ iters (op$ + t1-count TYPE-TUPLE-ELEMENTS-OFFSET))
      (assign$ i-init (op$ + t2-count TYPE-TUPLE-ELEMENTS-OFFSET))
      (repeat$ (i i-init iters) (_ UNIT-IMDT)
        (assign$ t1a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
        (sr-array-set! rt i t1a))]
     [(op$ < t1-count t2-count)
      (assign$ iters (op$ + t2-count TYPE-TUPLE-ELEMENTS-OFFSET))
      (assign$ i-init (op$ + t1-count TYPE-TUPLE-ELEMENTS-OFFSET))
      (repeat$ (i i-init iters) (_ UNIT-IMDT)
        (assign$ t2a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
        (sr-array-set! rt i t2a))]
     [else UNIT-IMDT])
    (sr-array-set! rt TYPE-TUPLE-COUNT-INDEX bigger-count)
    (Assign hrt (hashcons-type tagged-rt))
    (Var hrt)))

(: fn-type-glb ((Code-Label Uid) -> ((Var Uid) (Var Uid) -> D0-Expr)))
(define ((fn-type-glb tglb-label) t1 t2)
  (define-track-next-uid!$ hrt)
  (begin$
    (assign$ arity (sr-tagged-array-ref t1 TYPE-FN-TAG TYPE-FN-ARITY-INDEX))
    (assign$ rt (op$ Alloc (op$ + arity TYPE-FN-FMLS-OFFSET)))
    (assign$ iters (op$ + TYPE-FN-FMLS-OFFSET arity))
    (assign$ tagged-rt (sr-tag-value rt TYPE-FN-TAG))
    (assign$ t1-rt (sr-tagged-array-ref t1 TYPE-FN-TAG TYPE-FN-RETURN-INDEX))
    (assign$ t2-rt (sr-tagged-array-ref t2 TYPE-FN-TAG TYPE-FN-RETURN-INDEX))
    (assign$ t-rt (app-code$ tglb-label t1-rt t2-rt))
    (repeat$ (i TYPE-FN-FMLS-OFFSET iters) (_ UNIT-IMDT)
      (assign$ t1a (sr-tagged-array-ref t1 TYPE-FN-TAG i))
      (assign$ t2a (sr-tagged-array-ref t2 TYPE-FN-TAG i))
      (assign$ t-glb (app-code$ tglb-label t1a t2a))
      (sr-array-set! rt i t-glb))
    (sr-array-set! rt TYPE-FN-ARITY-INDEX arity)
    (sr-array-set! rt TYPE-FN-RETURN-INDEX t-rt)
    (Assign hrt (hashcons-type tagged-rt))
    (Var hrt)))

(: get-mk-fn-crcn! (Uid -> (Code-Label Uid)))
(define (get-mk-fn-crcn! mk-crcn)
  (: make-code! (Uid -> (Code-Label Uid)))
  (define (make-code! mk-crcn)
    (define-track-next-uid!$ mk-fn-crcn)
    (define mk-fn-crcn-label (Code-Label mk-fn-crcn))
    (define mk-crcn-label (Code-Label mk-crcn))
    (define mk-fn-crcn-c : D0-Code
      (code$ (t1 t2 l)
        (assign$ arity (sr-tagged-array-ref t2 TYPE-FN-TAG TYPE-FN-ARITY-INDEX))
        (assign$ tagged-arity
          (op$ + (op$ %<< arity COERCION-SECOND-TAG-SHIFT)
               COERCION-FN-SECOND-TAG))
        (assign$ t1r (sr-tagged-array-ref t1 TYPE-FN-TAG TYPE-FN-RETURN-INDEX))
        (assign$ t2r (sr-tagged-array-ref t2 TYPE-FN-TAG TYPE-FN-RETURN-INDEX))
        (assign$ cr (app-code$ mk-crcn-label t1r t2r l))
        (assign$ crcn (op$ Alloc (op$ + arity COERCION-FN-FMLS-OFFSET)))
        (assign$ iters (op$ + TYPE-FN-FMLS-OFFSET arity))
        (sr-array-set! crcn COERCION-FN-ARITY-INDEX tagged-arity)
        (sr-array-set! crcn COERCION-FN-RETURN-INDEX cr)
        (repeat$ (i TYPE-FN-FMLS-OFFSET iters) (_ UNIT-IMDT)
          (assign$ t1a (sr-tagged-array-ref t1 TYPE-FN-TAG i))
          (assign$ t2a (sr-tagged-array-ref t2 TYPE-FN-TAG i))
          (assign$ val-crcn (app-code$ mk-crcn-label t2a t1a l))
          (assign$ c-i (op$ + (op$ - i TYPE-FN-FMLS-OFFSET)
                            COERCION-FN-FMLS-OFFSET))
          (sr-array-set! crcn c-i val-crcn))
        (sr-tag-value crcn COERCION-MEDIATING-TAG)))
    (add-new-code! (cons mk-fn-crcn mk-fn-crcn-c))
    (set-box! mk-fn-coercion-code-label? mk-fn-crcn-label)
    mk-fn-crcn-label)
  (let ([cl? (unbox mk-fn-coercion-code-label?)])
    (or cl? (make-code! mk-crcn))))

(: get-coerce-tuple! (Uid -> (Code-Label Uid)))
(define (get-coerce-tuple! coerce)
  (: make-code! (Uid -> (Code-Label Uid)))
  (define (make-code! coerce)
    (define-track-next-uid!$ coerce-tuple)
    (define coerce-tuple-label (Code-Label coerce-tuple))
    (define coerce-label (Code-Label coerce))
    (define coerce-tuple-c : D0-Code
      (code$ (val crcn suspend-monotonic-heap-casts?)
        (assign$ tagged-count
          (sr-tagged-array-ref
           crcn COERCION-MEDIATING-TAG COERCION-TUPLE-COUNT-INDEX))
        (assign$ count (op$ %>> tagged-count COERCION-SECOND-TAG-SHIFT))
        (assign$ iters (op$ + COERCION-TUPLE-ELEMENTS-OFFSET count))
        (assign$ new-val (op$ Alloc count))
        (repeat$ (i COERCION-TUPLE-ELEMENTS-OFFSET iters) (_ UNIT-IMDT)
          (assign$ val-i (op$ - i COERCION-TUPLE-ELEMENTS-OFFSET))
          (assign$ vala (op$ Array-ref val val-i))
          (assign$ crcna (sr-tagged-array-ref crcn COERCION-MEDIATING-TAG i))
          (assign$ casted-vala (app-code$ coerce-label vala crcna suspend-monotonic-heap-casts?))
          (op$ Array-set! new-val val-i casted-vala))
        new-val))
    (add-new-code! (cons coerce-tuple coerce-tuple-c))
    (set-box! coerce-tuple-code-label? coerce-tuple-label)
    coerce-tuple-label)
  (let ([cl? (unbox coerce-tuple-code-label?)])
    (or cl? (make-code! coerce))))

(: get-cast-tuple! (Uid -> (Code-Label Uid)))
(define (get-cast-tuple! cast)
  (: make-code! (Uid -> (Code-Label Uid)))
  (define (make-code! cast)
    (define-track-next-uid!$ cast-tuple)
    (define cast-tuple-label (Code-Label cast-tuple))
    (define cast-label (Code-Label cast))
    (define cast-tuple-c : D0-Code
      (code$ (val t1 t2 l suspend-monotonic-heap-casts?)
        (assign$ count
          (sr-tagged-array-ref t2 TYPE-TUPLE-TAG TYPE-TUPLE-COUNT-INDEX))
        (assign$ new-val (op$ Alloc count))
        (assign$ iters (op$ + TYPE-TUPLE-ELEMENTS-OFFSET count))
        (repeat$ (i TYPE-TUPLE-ELEMENTS-OFFSET iters) (_ UNIT-IMDT)
          (assign$ val-i (op$ - i TYPE-TUPLE-ELEMENTS-OFFSET))
          (assign$ vala (op$ Array-ref val val-i))
          (assign$ t1a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
          (assign$ t2a (sr-tagged-array-ref t2 TYPE-TUPLE-TAG i))
          (assign$ casted-vala (app-code$ cast-label vala t1a t2a l suspend-monotonic-heap-casts?))
          (op$ Array-set! new-val val-i casted-vala))
        new-val))
    (add-new-code! (cons cast-tuple cast-tuple-c))
    (set-box! cast-tuple-code-label? cast-tuple-label)
    cast-tuple-label)
  (let ([cl? (unbox cast-tuple-code-label?)])
    (or cl? (make-code! cast))))

(: get-mk-tuple-crcn! (Uid -> (Code-Label Uid)))
(define (get-mk-tuple-crcn! mk-crcn)
  (: make-code! (Uid -> (Code-Label Uid)))
  (define (make-code! mk-crcn)
    (define-track-next-uid!$ mk-tuple-crcn)
    (define mk-tuple-crcn-label (Code-Label mk-tuple-crcn))
    (define mk-crcn-label (Code-Label mk-crcn))
    (define mk-tuple-crcn-c : D0-Code
      ;; mk-tuple-crcn creates a coercion out of two tuple types, it also checks
      ;; if the two types are identical, so that it can generate a simple
      ;; identity coercion without allocating unnecessary tuple coercion of
      ;; identities. It expects the length of the first tuple to be greater than
      ;; or equal to the length of the second.
      (code$ (t1 t2 l)
        (assign$ t1-count
          (sr-tagged-array-ref t1 TYPE-TUPLE-TAG TYPE-TUPLE-COUNT-INDEX))
        (assign$ t2-count
          (sr-tagged-array-ref t2 TYPE-TUPLE-TAG TYPE-TUPLE-COUNT-INDEX))
        (assign$ crcn UNIT-IMDT)
        (assign$ id? TRUE-IMDT)
        (assign$ iters (op$ + TYPE-TUPLE-ELEMENTS-OFFSET t2-count))
        (repeat$ (i TYPE-TUPLE-ELEMENTS-OFFSET iters) (_ UNIT-IMDT)
          (assign$ t1a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
          (assign$ t2a (sr-tagged-array-ref t2 TYPE-TUPLE-TAG i))
          (assign$ val-crcn (app-code$ mk-crcn-label t1a t2a l))
          (cond$
           [id?
            (assign$ tmp-id?
              (sr-check-tag=?
               val-crcn COERCION-TAG-MASK COERCION-IDENTITY-TAG))
            (cond$
             [(op$ not tmp-id?)
              (assign$ tagged-count
                (op$ + (op$ %<< t1-count COERCION-SECOND-TAG-SHIFT)
                     COERCION-TUPLE-SECOND-TAG))
              (assign$ c-i (op$ + (op$ - i TYPE-TUPLE-ELEMENTS-OFFSET)
                                COERCION-TUPLE-ELEMENTS-OFFSET))
              (Assign (Var-id crcn)
                (op$ Alloc (op$ + t1-count COERCION-TUPLE-ELEMENTS-OFFSET)))
              (sr-array-set! crcn COERCION-TUPLE-COUNT-INDEX tagged-count)
              (repeat$ (j COERCION-TUPLE-ELEMENTS-OFFSET c-i) (_ UNIT-IMDT)
                (sr-array-set! crcn j COERCION-IDENTITY-IMDT))
              (sr-array-set! crcn c-i val-crcn)
              (Assign (Var-id id?) FALSE-IMDT)]
             [else UNIT-IMDT])]
           [else
            (assign$ c-i (op$ + (op$ - i TYPE-TUPLE-ELEMENTS-OFFSET)
                              COERCION-TUPLE-ELEMENTS-OFFSET))
            (sr-array-set! crcn c-i val-crcn)]))
        (cond$
         [id? COERCION-IDENTITY-IMDT]
         [else
          (assign$ iters (op$ + t1-count TYPE-TUPLE-ELEMENTS-OFFSET))
          (assign$ i-init (op$ + t2-count TYPE-TUPLE-ELEMENTS-OFFSET))
          (repeat$ (i i-init iters) (_ UNIT-IMDT)
            (assign$ t1a (sr-tagged-array-ref t1 TYPE-TUPLE-TAG i))
            (assign$ c-i (op$ + (op$ - i TYPE-TUPLE-ELEMENTS-OFFSET)
                              COERCION-TUPLE-ELEMENTS-OFFSET))
            (sr-array-set! crcn c-i COERCION-IDENTITY-IMDT))
          (sr-tag-value crcn COERCION-MEDIATING-TAG)])))
    (add-new-code! (cons mk-tuple-crcn mk-tuple-crcn-c))
    (set-box! mk-tuple-coercion-code-label? mk-tuple-crcn-label)
    mk-tuple-crcn-label)
  (let ([cl? (unbox mk-tuple-coercion-code-label?)])
    (or cl? (make-code! mk-crcn))))

(: sr-expr (Env IndexMap CoC6-Expr -> D0-Expr))
(define (sr-expr env cenv exp)

  (: recur-curry-env (Env IndexMap -> (CoC6-Expr -> D0-Expr)))
  (define ((recur-curry-env env cenv) exp)
    (recur/env exp env cenv))

  (: recur/env (CoC6-Expr Env IndexMap -> D0-Expr))
  (define (recur/env exp env cenv)
    (: recur* (CoC6-Expr* -> D0-Expr*))
    (define (recur* e*) (map recur e*))
    (: recur (CoC6-Expr -> D0-Expr))
    (define (recur e)
      (match e
        [(Let (app (sr-bnd* recur) b*) e)
         (let* ([id* (map (inst car Uid Any) b*)]
                [rhs* (map (inst cdr Any D0-Expr) b*)]
                [a* (map (inst Assign Uid D0-Expr) id* rhs*)]
                [env (extend* env id* (map var id*))])
           (Begin a* (recur/env e env cenv)))]
        [(If (app recur t) (app recur c) (app recur a))
         (If t c a)]
        [(Switch e c* d)
         (Switch (recur e) (map-switch-case* recur c*) (recur d))]
        [(Op p (app recur* e*))
         (unless (symbol? p)
           (error 'specify-representation "found non-symbol primitive ~a" p))
         (Op p e*)]
        [(and (No-Op) nop) nop]
        [(Quote k)
         (cond
           [(null? k)    UNIT-IMDT]
           [(boolean? k) (if k TRUE-IMDT FALSE-IMDT)]
           [(data-literal? k) (Quote k)]
           [else
            (error 'specify-representation/quote "invalid: ~a" k)])]
        ;; Closure Representation
        [(Closure-App (app recur e) (app recur e^) (app recur* e*))
         (App-Code e (cons e^ e*))]
        [(Let-Closures c* e)
         (define-values (code* id* alloc* init*) (sr-closures c*))
         (define rec-e (recur e))
         (define alloc-e
           (cond
             [(null? alloc*) rec-e]
             [else (Begin alloc* (Begin init* rec-e))])) 
         (cond
           [(null? code*) alloc-e]
           [else (Labels code* alloc-e)])]
        [(Closure-Caster (app recur e))
         (op$ Array-ref (op$ binary-and CLOSURE-VALUE-MASK e) CLOS-CSTR-INDEX)]
        [(Closure-Code (app recur e))
         (op$ Array-ref (op$ binary-and CLOSURE-VALUE-MASK e) CLOS-CODE-INDEX)]
        [(Closure-Ref (app recur e) i)
         (op$ Array-ref
              (op$ binary-and e CLOSURE-VALUE-MASK)
              (Quote (+ data:CLOS-FVAR-OFFSET i)))]
        [(and v (Var _)) v]
        [(Global s) (Global s)]
        [(Assign u/s (app recur e)) (Assign u/s e)]
        [(Labels (app (sr-bnd-code* recur/env) b*) e)
         (let* ([u* (map (inst car Uid Any) b*)]
                [l* (map label u*)])
           (Labels b* (recur/env e (extend* env u* l*) cenv)))]
        [(App-Code e e*) (App-Code (recur e) (recur* e*))]
        [(Code-Label u) (Code-Label u)]
        ;; Type Representation
        [(Type t) (sr-prim-type t)]
        [(Type-Fn-Huh (app recur e)) (type-fn? e)] 
        [(Type-Fn-arity (app recur e)) (type-fn-arity-access e)]
        [(Type-Fn-return (app recur e)) (type-fn-return-access e)]
        [(Type-Fn-arg (app recur e1) (app recur e2)) (type-fn-fmls-access e1 e2)]
        [(Type-Mu-Huh (app recur e)) (type-mu? e)]
        [(Type-Mu-Body (app recur e)) (type-mu-body-access e)]
        [(Type-GRef-Huh (app recur e)) (type-gref? e)]
        [(Type-GRef-Of (app recur e)) (type-gref-type-access e)]
        [(Type-GVect-Huh (app recur e)) (type-gvect? e)]
        [(Type-GVect-Of (app recur e)) (type-gvect-type-access e)]
        [(Type-Dyn-Huh (app recur e))
         (Op '= (list TYPE-DYN-RT-VALUE e))]
        
        [(Type-Tag (app recur e))
         (Op 'binary-and (list e TYPE-TAG-MASK))]
        ;; Coercions
        ;; Projection Coercions
        [(Quote-Coercion c) (sr-immediate-coercion c)]
        [(Project-Coercion (app recur t) (app recur l))
         (sr-alloc "project_coercion" COERCION-PROJECT-TAG
                   `(("type" . ,t) ("label" . ,l)))]
        [(Project-Coercion-Huh (app recur e))
         (sr-check-tag=? e COERCION-TAG-MASK COERCION-PROJECT-TAG)]
        [(Project-Coercion-Type (app recur e))
         (sr-tagged-array-ref e COERCION-PROJECT-TAG COERCION-PROJECT-TYPE-INDEX)]
        [(Project-Coercion-Label (app recur e))
         (sr-tagged-array-ref e COERCION-PROJECT-TAG COERCION-PROJECT-LABEL-INDEX)]
        ;; Injection Coercions
        [(Inject-Coercion (app recur t))
         (sr-alloc "inject_coercion" COERCION-INJECT-TAG `(("type" . ,t)))]
        [(Inject-Coercion-Huh (app recur e))
         (sr-check-tag=? e COERCION-TAG-MASK COERCION-INJECT-TAG)]
        [(Inject-Coercion-Type (app recur e))
         (sr-tagged-array-ref e COERCION-INJECT-TAG COERCION-INJECT-TYPE-INDEX)]
        ;; Sequence Coercions
        [(Sequence-Coercion (app recur f) (app recur s))
         (sr-alloc "sequence_coercion" COERCION-SEQUENCE-TAG
                   `(("first" . ,f) (,"second" . ,s)))]
        [(Sequence-Coercion-Huh (app recur e))
         (sr-check-tag=? e COERCION-TAG-MASK COERCION-SEQUENCE-TAG)]
        [(Sequence-Coercion-Fst (app recur e))
         (sr-tagged-array-ref e COERCION-SEQUENCE-TAG COERCION-SEQUENCE-FST-INDEX)]
        [(Sequence-Coercion-Snd (app recur e))
         (sr-tagged-array-ref e COERCION-SEQUENCE-TAG COERCION-SEQUENCE-SND-INDEX)]
        ;; Identity Coercions can only be created by coercion quoting
        ;; But  their representation is just (Quote ID-COERCION-TAG)
        [(Id-Coercion-Huh (app recur e)) (build-id-coercion-huh e)]
        [(HC (app recur p?) (app recur t1) (app recur lbl)
             (app recur i?) (app recur t2)
             (app recur m))
         (define tag-expr : D0-Expr
           (match* (p? i?)
             [((Quote (? boolean? p?)) (Quote (? boolean? i?)))
              (define p (if p? data:HC-PRJ-TAG-MASK 0))
              (define i (if i? data:HC-INJ-TAG-MASK 0))
              (Quote (bitwise-ior p i))]
             [(p? i?)
              (begin$
                (assign$ prj-bit (If p? HC-PRJ-TAG-MASK ZERO-IMDT))
                (assign$ inj-bit (If i? HC-INJ-TAG-MASK ZERO-IMDT))
                (op$ binary-or prj-bit inj-bit))])) 
         (sr-alloc "hyper_Coercion" (ann tag-expr D0-Expr)
                   `(("t1" . ,t1)
                     ("label" . ,lbl)
                     ("t2" . ,t2)
                     ("med-coercion" . ,m)))]
        [(HC-Inject-Huh (app recur h)) (check-tag? h HC-INJ-TAG-MASK)]
        [(HC-Project-Huh (app recur h)) (check-tag? h HC-PRJ-TAG-MASK)]
        [(HC-Identity-Huh (app recur h))
         (begin$
           (assign$ hc h)
           (If (check-tag? hc HC-TAG-MASK)
               FALSE-IMDT
               (build-id-coercion-huh (build-hc-med hc))))]
        [(HC-Label (app recur h)) 
         (tagged-array-ref h HC-TAG-MASK HC-LABEL-INDEX)]
        [(HC-T1 (app recur h))
         (tagged-array-ref h HC-TAG-MASK HC-T1-INDEX)]
        [(HC-T2 (app recur h))
         (tagged-array-ref h HC-TAG-MASK HC-T2-INDEX)]
        [(HC-Med (app recur h)) (build-hc-med h)]
        [(Make-Mu-Coercion) (sr-alloc-mu-id-coercion)]
        [(Mu-Coercion-Huh (app recur e))
         ;; TODO fix mediating coercions so that it is more obvious
         ;; that they have a shared layout.
         (begin$
           (assign$ crcn-tag-word
                    (sr-tagged-array-ref
                     e COERCION-MEDIATING-TAG COERCION-MU-TAG-INDEX))
           (assign$ crcn-med-tag (sr-get-tag crcn-tag-word COERCION-TAG-MASK))
           (op$ = crcn-med-tag COERCION-MU-SECOND-TAG))]
        [(Mu-Coercion-Body (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-MU-BODY-INDEX)]
        [(Mu-Coercion-Body-Set! (app recur m) (app recur b))
         (sr-mu-coercion-body-set! m b)]
        ;; Function Coercions
        [(Fn-Coercion-Huh (app recur e))
         (begin$
           (assign$ tmp-crcn (sr-tagged-array-ref
                              e COERCION-MEDIATING-TAG COERCION-FN-ARITY-INDEX))
           (assign$ crcn-tag (sr-get-tag tmp-crcn COERCION-TAG-MASK))
           (op$ = crcn-tag COERCION-FN-SECOND-TAG))]
        [(Fn-Coercion-Arity (app recur e))
         (begin$
           (assign$ tagged-arity
                    (sr-tagged-array-ref
                     e COERCION-MEDIATING-TAG COERCION-FN-ARITY-INDEX))
           (op$ %>> tagged-arity COERCION-SECOND-TAG-SHIFT))]
        [(Fn-Coercion-Arg (app recur e) (app recur i))
         (sr-tagged-array-ref
          e COERCION-MEDIATING-TAG (sr-plus COERCION-FN-FMLS-OFFSET i))]
        [(Fn-Coercion-Return (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-FN-RETURN-INDEX)]
        ;; TODO either repurpose or get rid of the arity field
        ;; One could immagine that we use it to dynamically dispatch on compose
        [(Fn-Coercion (app recur* e*) (app recur e))
         (begin$
           (assign$ tag_and_arity
                    (op$ + (op$ %<< (Quote (length e*)) COERCION-SECOND-TAG-SHIFT)
                         COERCION-FN-SECOND-TAG))
           (sr-alloc "fn_coercion" COERCION-MEDIATING-TAG
                     `(("arity" . ,tag_and_arity)
                       ("return" . ,e) .
                       ,(map (lambda ([e : D0-Expr])
                               (cons "argument" e))
                             e*))))]
        [(Make-Fn-Coercion mk-crcn (app recur t1) (app recur t2) (app recur l))
         (app-code$ (get-mk-fn-crcn! mk-crcn) t1 t2 l)]
        [(Id-Fn-Coercion (app recur a))
         (begin$
           (assign$ size a)
           (assign$ fn-c (op$ Alloc (sr-plus size (Quote 2))))
           (assign$ info (op$ + (op$ %<< size COERCION-SECOND-TAG-SHIFT)
                              COERCION-FN-SECOND-TAG))
           (sr-array-set! fn-c COERCION-FN-ARITY-INDEX info)
           (sr-array-set! fn-c COERCION-FN-RETURN-INDEX COERCION-IDENTITY-IMDT)
           (repeat$ (i (Quote 0) size) (_ (Quote 0))
             (sr-array-set!
              fn-c (op$ + i COERCION-FN-FMLS-OFFSET) COERCION-IDENTITY-IMDT))
           (sr-tag-value fn-c COERCION-MEDIATING-TAG))]
        [(Id-Tuple-Coercion (app recur a))
         (begin$
           (assign$ size a)
           (assign$ tup-c
             (op$ Alloc (sr-plus size COERCION-TUPLE-ELEMENTS-OFFSET)))
           (assign$ info
             (op$ + (op$ %<< size COERCION-SECOND-TAG-SHIFT)
                       COERCION-TUPLE-SECOND-TAG))
           (sr-array-set! tup-c COERCION-TUPLE-COUNT-INDEX info)
           (repeat$ (i COERCION-TUPLE-ELEMENTS-OFFSET
                       (op$ + size COERCION-TUPLE-ELEMENTS-OFFSET)) (_ (Quote 0))
             (sr-array-set! tup-c i COERCION-IDENTITY-IMDT))
           (sr-tag-value tup-c COERCION-MEDIATING-TAG))]
        [(Fn-Coercion-Arg-Set! (app recur f) (app recur i) (app recur a))
         (sr-tagged-array-set!
          f COERCION-MEDIATING-TAG (op$ + i COERCION-FN-FMLS-OFFSET) a)]
        [(Fn-Coercion-Return-Set! (app recur f) (app recur r))
         (sr-tagged-array-set!
          f COERCION-MEDIATING-TAG COERCION-FN-RETURN-INDEX r)]
        [(Tuple-Coercion-Item-Set! (app recur t) (app recur i) (app recur e))
         (sr-tagged-array-set!
          t COERCION-MEDIATING-TAG (op$ + i COERCION-TUPLE-ELEMENTS-OFFSET) e)]
        [(Ref-Coercion-Huh (app recur e))
         (begin$
           (assign$ tmp-crcn
                    (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-REF-TAG-INDEX))
           (assign$ crcn-tag (sr-get-tag tmp-crcn COERCION-TAG-MASK))
           (op$ = crcn-tag COERCION-REF-SECOND-TAG))]
        [(Ref-Coercion (app recur r) (app recur w) flag)
         (begin$
           (assign$ second-tag
                    (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                         COERCION-REF-SECOND-TAG))
           (sr-alloc "ref-coercion" COERCION-MEDIATING-TAG
                         `(("tag" . ,second-tag)
                           ("read-coercion" . ,r)
                           ("write-coercion" . ,w)
                           . ,(if (cast-profiler?)
                                  `(("flag" . ,(recur flag)))
                                  '()))))]
        [(Ref-Coercion-Read (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-REF-READ-INDEX)]
        [(Ref-Coercion-Write (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-REF-WRITE-INDEX)]
        [(Ref-Coercion-Ref-Huh (app recur e))
         (if (cast-profiler?)
             (begin$
               (assign$ flag
                        (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-REF-FLAG-INDEX))
               (op$ = flag COERCION-REF-REF-FLAG))
             NO-OP)]
        [(Failed-Coercion-Huh (app recur e))
         (sr-check-tag=? e COERCION-TAG-MASK COERCION-FAILED-TAG)]
        ;; For now I am allocating the blame label in a box.
        ;; Make this cheaper by ensuring that the string pointer is alligned and
        ;; tagging it.
        [(Failed-Coercion (app recur l))
         (sr-alloc "failed-coercion" COERCION-FAILED-TAG `(("label" . ,l)))]
        [(Failed-Coercion-Label (app recur e))
         (sr-tagged-array-ref e COERCION-FAILED-TAG COERCION-FAILED-LABEL-INDEX)]
        ;; FN-Proxy Stuff
        [(Fn-Proxy i (app recur clos) (app recur crcn))
         (sr-alloc "fn-proxy" FN-PROXY-TAG
                   `(("closure" . ,clos) ("coercion" . ,crcn)))]
        [(Fn-Proxy-Huh (app recur e)) (sr-check-tag=? e FN-TAG-MASK FN-PROXY-TAG)]
        [(Fn-Proxy-Closure (app recur e))
         (sr-tagged-array-ref e FN-PROXY-TAG FN-PROXY-CLOS-INDEX)]
        [(Fn-Proxy-Coercion (app recur e))
         (sr-tagged-array-ref e FN-PROXY-TAG FN-PROXY-CRCN-INDEX)]
        ;; Hybrid Proxy Stuff
        [(Closure-Proxy (app recur clos))
         (sr-tag-value clos FN-PROXY-TAG)]
        #;
        [(Hybrid-Proxy apply (app recur clos) (app recur crcn))
         (sr-alloc "hybrid-proxy" FN-PROXY-TAG
                   `(("apply-hybrid-proxy" . ,(Code-Label apply))
                     ("closure" . ,clos)
                     ("coercion" . ,crcn)))]
        [(Hybrid-Proxy-Huh (app recur e))
         (sr-check-tag=? e FN-TAG-MASK HYBRID-PROXY-TAG)]
        [(Hybrid-Proxy-Closure (app recur e))
         (sr-tagged-array-ref e HYBRID-PROXY-TAG HYBRID-PROXY-CLOS-INDEX)]
        [(Hybrid-Proxy-Coercion (app recur e))
         (sr-tagged-array-ref e HYBRID-PROXY-TAG HYBRID-PROXY-CRCN-INDEX)]
        ;; TODO Fix me TAG should never have been exposed
        [(Tag t) (sr-tag t)]
        ;; Dynamic Values Representation
        [(Dyn-Object (app recur e) t)
         (match t
           [(Type (Int)) (op$ + (op$ %<< e DYN-IMDT-SHIFT) DYN-INT-TAG)]
           [(Type (Bool)) (op$ + (op$ %<< e DYN-IMDT-SHIFT) DYN-BOOL-TAG)]
           [(Type (Unit)) (op$ + (op$ %<< e DYN-IMDT-SHIFT) DYN-UNIT-TAG)]
           [(Type (Character)) (op$ + (op$ %<< e DYN-IMDT-SHIFT) DYN-CHAR-TAG)]
           [(Type _)
            (sr-alloc "dynamic_boxed" DYN-BOXED-TAG
                      `(("value" . ,e) ("type" . ,(recur t))))]
           [_
            (define (shift-and-tag value tag)
              (op$ binary-or (op$ %<< value DYN-IMDT-SHIFT) tag))
            (begin$
              (assign$ val e)
              (assign$ type (recur t))
              (case$ type
                 [(data:TYPE-INT-RT-VALUE)  (shift-and-tag val DYN-INT-TAG)]
                 [(data:TYPE-BOOL-RT-VALUE) (shift-and-tag val DYN-BOOL-TAG)]
                 [(data:TYPE-UNIT-RT-VALUE) (shift-and-tag val DYN-UNIT-TAG)]
                 [(data:TYPE-CHAR-RT-VALUE) (shift-and-tag val DYN-CHAR-TAG)]
                 ;; float is handled in the else branch
                 [else (sr-alloc "dynamic_boxed" DYN-BOXED-TAG
                                 `(("value" . ,val) ("type" . ,type)))]))])]
        [(Dyn-Value (app recur e))
         (begin$
           (assign$ tmp (recur e))
           (assign$ tag (sr-get-tag tmp DYN-TAG-MASK))
           (If (op$ = tag DYN-BOXED-TAG)
               (op$ Array-ref tmp DYN-VALUE-INDEX)
               (op$ %>> tmp DYN-IMDT-SHIFT)))]
        [(Dyn-Type (app recur e))
         (define err-msg
           (Quote "specify-representation/Dyn-type: switch failure"))
         (begin$
           (assign$ tmp e)
           (assign$ tag (sr-get-tag tmp DYN-TAG-MASK))
           (case$ tag
             [(data:DYN-BOXED-TAG) (op$ Array-ref tmp DYN-TYPE-INDEX)]
             [(data:DYN-INT-TAG) TYPE-INT-RT-VALUE]
             [(data:DYN-BOOL-TAG) TYPE-BOOL-RT-VALUE]
             [(data:DYN-UNIT-TAG) TYPE-UNIT-RT-VALUE]
             [(data:DYN-CHAR-TAG) TYPE-CHAR-RT-VALUE]
             [else (op$ Print err-msg) (op$ Exit EXIT-FAILURE) UNDEF-IMDT]))]
        [(Dyn-Immediate-Value (app recur e))
         (op$ %>> e DYN-IMDT-SHIFT)]
        [(Dyn-Immediate-Tag=Huh (app recur e) t)
         (define (default-th) DYN-BOXED-TAG)
         (op$ = (type->dyn-tag t default-th) (sr-get-tag e DYN-TAG-MASK))]
        [(Dyn-Immediate-Object (app recur e) t)
         (define (err-th)
           (error 'Dyn-Immediate-Object "Shouldn't be used to allocate boxed types"))
         (op$ + (op$ %<< e DYN-IMDT-SHIFT) (type->dyn-tag t err-th))]
        [(Dyn-Box-Object (app recur e) (app recur t))
         (sr-alloc "dynamic_boxed" DYN-BOXED-TAG `(("value" . ,e) ("type" . ,t)))]
        [(Dyn-Box-Value (app recur e))
         (op$ Array-ref e DYN-VALUE-INDEX)]
        [(Dyn-Box-Type (app recur e))
         (op$ Array-ref e DYN-TYPE-INDEX)]
        ;; Observable Results Representation
        [(Blame (app recur e))
         (begin$ (op$ Print e) (op$ Exit EXIT-FAILURE) UNDEF-IMDT)]
        [(Observe (app recur e) t) (sr-observe next-uid! e t)]
        [(and nop (No-Op)) nop]
        ;; References Representation
        [(Begin (app recur* e*) (app recur e)) (Begin e* e)]
        [(Repeat i (app recur e1) (app recur e2) u (app recur e3) e4)
         (Repeat i e1 e2 u e3
           (recur/env e4 (extend (extend env u (Var u)) i (Var i)) cenv))]
        [(While (app recur e1) (app recur e2)) (While e1 e2)]
        [(Break-Repeat) (Break-Repeat)]
        ;; Guarded
        [(Unguarded-Box (app recur e))
         (sr-alloc "unguarded_box" UGBOX-TAG (list (cons "init_value" e)))]
        [(Unguarded-Box-On-Stack (app recur e))
         (sr-alloc-on-stack
          "unguarded_box_on_stack" UGBOX-TAG
          (list (cons "init_value" e)))]
        
        [(Unguarded-Box-Ref (app recur e)) (op$ Array-ref e UGBOX-VALUE-INDEX)]
        [(Unguarded-Box-Set! (app recur e1) (app recur e2))
         (op$ Array-set! e1 UGBOX-VALUE-INDEX e2)]
        [(Unguarded-Vect (app recur e1) (app recur e2))
         (begin$
           (assign$ size e1)
           (assign$ init-val e2)
           (assign$ repr-size (op$ + size UGVECT-OFFSET))
           (assign$ vect (op$ Alloc repr-size))
           (op$ Array-set! vect UGVECT-SIZE-INDEX size)
           (repeat$ (i UGVECT-OFFSET repr-size) (_ UNIT-IMDT)
             (op$ Array-set! vect i init-val))
           vect)]
        [(Unguarded-Vect-Ref (app recur e1) (app recur e2))
         (begin$
           (assign$ ind e2)
           (assign$ vect e1)
           (if (bounds-checks?)
               (If (If (op$ >= ind ZERO-IMDT)
                       (op$ < ind (op$ Array-ref vect ZERO-IMDT))
                       FALSE-IMDT)
                   (op$ Array-ref vect (op$ + ind UGVECT-OFFSET))
                   (begin$
                     (op$ Printf (Quote "index out of bound %ld\n") ind)
                     (op$ Exit EXIT-FAILURE)))
               (op$ Array-ref vect (op$ + ind UGVECT-OFFSET))))]
        [(Unguarded-Vect-Set! (app recur e1) (app recur e2) (app recur e3))
         (begin$
           (assign$ ind e2)
           (assign$ vect e1)
           (if (bounds-checks?)
               (If (If (op$ >= ind ZERO-IMDT)
                       (op$ < ind (op$ Array-ref vect ZERO-IMDT))
                       FALSE-IMDT)
                   (op$ Array-set! vect (op$ + ind UGVECT-OFFSET) e3)
                   (begin$
                     (op$ Printf (Quote "index out of bound %ld\n") ind)
                     (op$ Exit EXIT-FAILURE)))
               (op$ Array-set! vect (op$ + ind UGVECT-OFFSET) e3)))]
        [(Guarded-Proxy-Huh (app recur e))
         (op$ = (sr-get-tag e GREP-TAG-MASK) GPROXY-TAG)]
        [(Unguarded-Vect-length (app recur e))
         (op$ Array-ref e UGVECT-SIZE-INDEX)]
        [(Guarded-Proxy (app recur e) r)
         (match r
           [(Twosome (app recur t1) (app recur t2) (app recur l))
            (sr-alloc "proxied-ref" GPROXY-TAG
                      `(("ref" . ,e) ("from" . ,t1) ("to" . ,t2) ("label" . ,l)))]
           [(Coercion (app recur c))
            (sr-alloc "proxied-ref" GPROXY-TAG `(("ref" . ,e) ("crcn" . ,c)))])]
        [(Guarded-Proxy-Ref (app recur e))
         ((untag-deref-gproxy GPROXY-FOR-INDEX) e)]
        [(Guarded-Proxy-Source (app recur e))
         ((untag-deref-gproxy GPROXY-FROM-INDEX) e)]
        [(Guarded-Proxy-Target (app recur e))
         ((untag-deref-gproxy GPROXY-TO-INDEX) e)]
        [(Guarded-Proxy-Blames (app recur e))
         ((untag-deref-gproxy GPROXY-BLAMES-INDEX) e)]
        [(Guarded-Proxy-Coercion (app recur e))
         ((untag-deref-gproxy GPROXY-COERCION-INDEX) e)]
        [(Mbox (app recur e) (app sr-prim-type t))
         (sr-alloc "mbox" MBOX-TAG (list (cons "init_type" t) (cons "init_value" e)))]
        [(Mbox-val-set! (app recur e1) (app recur e2))
         (op$ Array-set! e1 MBOX-VALUE-INDEX e2)]
        [(Mbox-val-ref (app recur e)) (op$ Array-ref e MBOX-VALUE-INDEX)]
        [(Mbox-rtti-set! (app recur addr) (app recur e))
         (op$ Array-set! addr MONO-RTTI-INDEX e)]
        [(Mbox-rtti-ref (app recur addr)) (op$ Array-ref addr MONO-RTTI-INDEX)]
        [(Mvector (app recur e1) (app recur e2) (app sr-prim-type t))
         (begin$
           (assign$ size e1)
           (assign$ init-val e2)
           (assign$ rtti t)
           (assign$ repr-size (op$ + size MVECT-OFFSET))
           (assign$ vect (op$ Alloc repr-size))
           (op$ Array-set! vect MVECT-SIZE-INDEX size)
           (op$ Array-set! vect MONO-RTTI-INDEX rtti)
           (repeat$ (i MVECT-OFFSET repr-size) (_ UNIT-IMDT)
             (op$ Array-set! vect i init-val))
           vect)]
        [(Mvector-length (app recur e)) (op$ Array-ref e MVECT-SIZE-INDEX)]
        [(Mvector-rtti-set! (app recur addr) (app recur e))
         (op$ Array-set! addr MONO-RTTI-INDEX e)]
        [(Mvector-rtti-ref (app recur addr)) (op$ Array-ref addr MONO-RTTI-INDEX)]
        [(Mvector-val-ref (app recur e1) (app recur e2) mode)
         (begin$
           (assign$ ind e2)
           (assign$ mvect e1)
           (cond
             [(and (eq? mode 'check-bounds) (bounds-checks?))
              (If (op$ >= ind ZERO-IMDT) ;; vectors indices starts from 0
                  (If (op$ < ind (op$ Array-ref mvect MVECT-SIZE-INDEX))
                      (op$ Array-ref mvect (op$ + ind MVECT-OFFSET))
                      (begin$
                        (op$ Printf (Quote "index out of bound %ld\n") ind)
                        (op$ Exit EXIT-FAILURE)))
                  (begin$
                    (op$ Printf (Quote "index out of bound %ld\n") ind)
                    (op$ Exit EXIT-FAILURE)))]
             [else (op$ Array-ref mvect (op$ + ind MVECT-OFFSET))]))]
        [(Mvector-val-set! (app recur e1) (app recur e2) (app recur e3) mode)
         (begin$
           (assign$ ind e2)
           (assign$ mvect e1)
           (cond
             [(and (eq? mode 'check-bounds) (bounds-checks?))
              (If (op$ >= ind ZERO-IMDT) ;; vectors indices starts from 0
                  (If (op$ < ind (op$ Array-ref mvect MVECT-SIZE-INDEX))
                      (op$ Array-set! mvect (op$ + ind MVECT-OFFSET) e3)
                      (begin$
                        (op$ Printf (Quote "index out of bound %ld\n") ind)
                        (op$ Exit EXIT-FAILURE)))
                  (begin$
                    (op$ Printf (Quote "index out of bound %ld\n") ind)
                    (op$ Exit EXIT-FAILURE)))]
             [else (op$ Array-set! mvect (op$ + ind MVECT-OFFSET) e3)]))]
        [(Type-MVect (app recur e)) (sr-type-mvect e)]
        [(Type-MVect-Huh (app recur e)) (type-mvect? e)]
        [(Type-MVect-Of (app recur e)) (type-mvect-type-access e)]
        [(MVect-Coercion-Huh (app recur e))
         (begin$
           (assign$ tmp-crcn
                    (sr-tagged-array-ref
                     e COERCION-MEDIATING-TAG COERCION-MVECT-TAG-INDEX))
           (assign$ crcn-tag (sr-get-tag tmp-crcn COERCION-TAG-MASK))
           (op$ = crcn-tag COERCION-MVECT-SECOND-TAG))]
        [(MVect-Coercion-Type (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-MVECT-TYPE-INDEX)]
        [(MVect-Coercion (app recur t))
         (begin$
           (assign$ second-tag
                    (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                         COERCION-MVECT-SECOND-TAG))
           (sr-alloc "mvect-coercion" COERCION-MEDIATING-TAG
                     `(("tag" . ,second-tag) ("type" . ,t))))]
        [(MRef-Coercion-Huh (app recur e))
         (begin$
           (assign$ tmp-crcn
                    (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-MREF-TAG-INDEX))
           (assign$ crcn-tag (sr-get-tag tmp-crcn COERCION-TAG-MASK))
           (op$ = crcn-tag COERCION-MREF-SECOND-TAG))]
        [(MRef-Coercion-Type (app recur e))
         (sr-tagged-array-ref e COERCION-MEDIATING-TAG COERCION-MREF-TYPE-INDEX)]
        [(MRef-Coercion (app recur t))
         (begin$
           (assign$ second-tag
                    (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                         COERCION-MREF-SECOND-TAG))
           (sr-alloc "ref-coercion" COERCION-MEDIATING-TAG
                     `(("tag" . ,second-tag) ("type" . ,t))))]
        [(Make-GLB-Two-Fn-Types mk-glb (app recur t1) (app recur t2))
         (let ([mk-fn-type-glb (fn-type-glb (Code-Label mk-glb))])
           (cond
             [(and (Var? t1) (Var? t2)) (mk-fn-type-glb t1 t2)]
             [(Var? t1) (begin$ (assign$ a-t2 t2) (mk-fn-type-glb t1 a-t2))]
             [(Var? t2) (begin$ (assign$ a-t1 t1) (mk-fn-type-glb a-t1 t2))]
             [else (begin$
                     (assign$ a-t1 t1)
                     (assign$ a-t2 t2)
                     (mk-fn-type-glb a-t1 a-t2))]))]
        [(Make-GLB-Two-Tuple-Types mk-glb (app recur t1) (app recur t2))
         (let ([mk-tuple-type-glb (tuple-type-glb (Code-Label mk-glb))])
           (cond
             [(and (Var? t1) (Var? t2)) (mk-tuple-type-glb t1 t2)]
             [(Var? t1) (begin$ (assign$ a-t2 t2) (mk-tuple-type-glb t1 a-t2))]
             [(Var? t2) (begin$ (assign$ a-t1 t1) (mk-tuple-type-glb a-t1 t2))]
             [else (begin$
                     (assign$ a-t1 t1)
                     (assign$ a-t2 t2)
                     (mk-tuple-type-glb a-t1 a-t2))]))]
        [(Type-GRef (app recur e)) (sr-type-gref e)]
        [(Type-GVect (app recur e)) (sr-type-gvect e)]
        [(Type-MRef (app recur e)) (sr-type-mref e)]
        [(Type-MRef-Huh (app recur e)) (type-mref? e)]
        [(Type-MRef-Of (app recur e)) (type-mref-type-access e)]
        [(Error (app recur e))
         (begin$ (op$ Print e) (op$ Exit EXIT-FAILURE) UNDEF-IMDT)]
        [(Create-tuple (app recur* e*))
         (sr-alloc "tuple" #f (map (lambda ([e : D0-Expr]) (cons "element" e)) e*))]
        [(Tuple-proj (app recur e) (app recur i)) (op$ Array-ref e i)]
        [(Tuple-Coercion-Huh (app recur e))
         (begin$
           (assign$ tmp-crcn
                    (sr-tagged-array-ref
                     e COERCION-MEDIATING-TAG COERCION-TUPLE-COUNT-INDEX))
           (assign$ crcn-tag (sr-get-tag tmp-crcn COERCION-TAG-MASK))
           (op$ = crcn-tag COERCION-TUPLE-SECOND-TAG))]
        [(Tuple-Coercion-Num (app recur e))
         (begin$
           (assign$ tagged-count
                    (sr-tagged-array-ref
                     e COERCION-MEDIATING-TAG COERCION-TUPLE-COUNT-INDEX))
           (op$ %>> tagged-count COERCION-SECOND-TAG-SHIFT))]
        [(Tuple-Coercion-Item (app recur e) (app recur i))
         (sr-tagged-array-ref
          e COERCION-MEDIATING-TAG (sr-plus COERCION-TUPLE-ELEMENTS-OFFSET i))]
        [(Type-Tuple-Huh (app recur e)) (type-tuple? e)]
        [(Type-Tuple-num (app recur e)) (type-tuple-count-access e)]
        [(Type-Tuple-item (app recur e) (app recur i))
         (type-tuple-elements-access e i)]
        [(Coerce-Tuple coerce (app recur v) (app recur c) (app recur suspend-monotonic-heap-casts?))
         (app-code$ (get-coerce-tuple! coerce) v c suspend-monotonic-heap-casts?)]
        [(Cast-Tuple cast (app recur v) (app recur t1) (app recur t2) (app recur l) (app recur suspend-monotonic-heap-casts?))
         (app-code$ (get-cast-tuple! cast) v t1 t2 l suspend-monotonic-heap-casts?)]
        #;
        [(Make-Tuple-Coercion mk-crcn (app recur t1) (app recur t2) (app recur l))
         (app-code$ (get-mk-tuple-crcn! mk-crcn) t1 t2 l)]
        [(Mediating-Coercion-Huh (app recur e))
         (sr-check-tag=? e COERCION-TAG-MASK COERCION-MEDIATING-TAG)]
        [other (error 'specify-representation "unmatched ~a" other)]))

    (recur exp))

  (recur/env exp env cenv))

(define (build-id-coercion-huh [e : D0-Expr]) : D0-Expr
  (sr-check-tag=? e COERCION-TAG-MASK COERCION-IDENTITY-TAG))

(define (build-hc-med [e : D0-Expr]) : D0-Expr
  (tagged-array-ref e HC-TAG-MASK HC-MED-INDEX))

(: sr-prim-type (Immediate-Type -> D0-Expr))
(define (sr-prim-type t)
  (match t
    [(Int)  TYPE-INT-RT-VALUE]
    [(Bool) TYPE-BOOL-RT-VALUE]
    [(Dyn)  TYPE-DYN-RT-VALUE]
    [(Unit) TYPE-UNIT-RT-VALUE]
    [(Float) TYPE-FLOAT-RT-VALUE]
    [(Character) TYPE-CHAR-RT-VALUE]
    [(Static-Id u) (Var u)]
    [other (error 'specify-representation/primitive-type "unmatched ~a" other)]))

;; The first expression returned allocates the mu
;; The second value returned initializes the mu
;; This allows Mu types to "tie the recursive knot" by initializing
;; after all other types have been allocated, but allows
(: allocate-bound-mu-type (Bnd-Mu-Type -> (Values D0-Expr D0-Expr)))
(define (allocate-bound-mu-type bnd)
  (match-define (cons u (Mu it)) bnd)
  (values (Assign u (sr-type-mu (Quote 0)))
          (begin$
            (type-mu-body-assign (Var u) (sr-prim-type it))
            (hashcons-type (Var u)))))

(: allocate-bound-type (Bnd-Type -> D0-Expr))
(define (allocate-bound-type bnd)
  (: sr-type (Compact-Type -> D0-Expr))
  (define (sr-type t)
    (match t
      [(GRef t) (sr-type-gref (sr-prim-type t))]
      [(GVect t) (sr-type-gvect (sr-prim-type t))]
      [(MRef t) (sr-type-mref (sr-prim-type t))]
      [(MVect t) (sr-type-mvect (sr-prim-type t))]
      [(Fn a f* r)
       (sr-type-fn (Quote a) (sr-prim-type r) (map sr-prim-type f*))]
      [(STuple n a*) (sr-type-tuple (Quote n) (map sr-prim-type a*))]
      [other (error 'specify-representation/type "unmatched ~a" other)]))
  (match-let ([(cons u t) bnd])
    (Assign u (sr-type t))))

(: sr-immediate-coercion (Immediate-Coercion -> D0-Expr))
(define (sr-immediate-coercion c)
  (match c
    [(Identity) COERCION-IDENTITY-IMDT]
    [(Static-Id id) (Var id)]
    [else (error 'sr-immediate-coercion "unhandled case in match")]))

;; The first expression returned allocates the mu
;; The second value returned initializes the mu
;; This allows Mu types to "tie the recursive knot" by initializing
;; after all other types have been allocated, but allows
(: allocate-bound-mu-crcn (Bnd-Mu-Crcn -> (Values D0-Expr D0-Expr)))
(define (allocate-bound-mu-crcn bnd)
  (match-define (cons u (Mu c)) bnd)
  (values (Assign u (sr-alloc-mu-id-coercion))
          (sr-mu-coercion-body-set! (Var u) (sr-immediate-coercion c))))

(: sr-alloc-mu-id-coercion : -> D0-Expr)
(define (sr-alloc-mu-id-coercion)
  (sr-alloc "mu-coercion" COERCION-MEDIATING-TAG
            `(("tag" . ,COERCION-MU-SECOND-TAG)
              ("body" . ,COERCION-IDENTITY-IMDT))))

(: sr-mu-coercion-body-set! : D0-Expr D0-Expr -> D0-Expr)
(define (sr-mu-coercion-body-set! m b) 
  (sr-tagged-array-set! m COERCION-MEDIATING-TAG COERCION-MU-BODY-INDEX b))

(: sr-coercion (Compact-Coercion -> D0-Expr))
(define (sr-coercion t)
  (match t
    [(Identity) COERCION-IDENTITY-IMDT]
    [(Project t l)
     ;; TODO Make it possible to turn off type hoisting
     (define t^ (sr-prim-type t))
     (sr-alloc "project_coercion" COERCION-PROJECT-TAG
               `(("type" . ,t^) ("label" . ,(Quote l))))]
    [(Inject (app sr-prim-type t))
     (sr-alloc "inject-coercion" COERCION-INJECT-TAG `(("type" . ,t)))]
    [(HC p? (app sr-prim-type t1) l? 
         i? (app sr-prim-type t2)
         (app sr-immediate-coercion m))
     (define p (if p? data:HC-PRJ-TAG-MASK 0))
     (define i (if i? data:HC-INJ-TAG-MASK 0))
     (define t (bitwise-ior p i))
     (debug 'specify-representation/hc-hoisted
            p? p i? i t
            (sr-alloc "hyper_coercion" (Quote t)
                      `(("t1"    . ,t1)
                        ("label" . ,(if l? (Quote l?) FALSE-IMDT))
                        ("t2"    . ,t2)
                        ("Med-coercion" . ,m))))]
    [(Sequence (app sr-immediate-coercion f) (app sr-immediate-coercion s))
     (sr-alloc "sequence_coecion" COERCION-SEQUENCE-TAG
               `(("first" . ,f) (,"second" . ,s)))]
    [(Fn l a* (app sr-immediate-coercion r))
     (define len : Index (length a*))
     (unless (= l len)
       (error 'sr-coercion "length mismatch"))
     (begin$
       (assign$ second-tag (op$ + (op$ %<< (Quote l) COERCION-SECOND-TAG-SHIFT)
                                COERCION-FN-SECOND-TAG))
       (sr-alloc "fn_coercion" COERCION-MEDIATING-TAG
                 `(("arity"  . ,second-tag)
                   ("return" . ,r) .
                   ,(map (lambda ([a : Immediate-Coercion])
                           (cons "argument" (sr-immediate-coercion a)))
                         a*))))]
    [(Ref (app sr-immediate-coercion r) (app sr-immediate-coercion w) flag)
     (begin$
       (assign$ second-tag (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                                COERCION-REF-SECOND-TAG))
       (if (cast-profiler?)
           (sr-alloc "ref-coercion" COERCION-MEDIATING-TAG
                     `(("tag" . ,second-tag)
                       ("read-coercion" . ,r)
                       ("write-coercion" . ,w)
                       ("flag" . ,(case flag
                                    [(GRef)  COERCION-REF-REF-FLAG]
                                    [(GVect) COERCION-REF-VEC-FLAG]))))
           (sr-alloc "ref-coercion" COERCION-MEDIATING-TAG
                     `(("tag" . ,second-tag)
                       ("read-coercion" . ,r)
                       ("write-coercion" . ,w)))))]
    [(MonoRef (app sr-prim-type t))
     (begin$
       (assign$ second-tag (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                                COERCION-MREF-SECOND-TAG))
       (sr-alloc "mref-coercion" COERCION-MEDIATING-TAG
                 `(("tag" . ,second-tag) ("type" . ,t))))]
    [(MonoVect (app sr-prim-type t))
     (begin$
       (assign$ second-tag (op$ + (op$ %<< ZERO-IMDT COERCION-SECOND-TAG-SHIFT)
                                COERCION-MVECT-SECOND-TAG))
       (sr-alloc "mvect-coercion" COERCION-MEDIATING-TAG
                 `(("tag" . ,second-tag) ("type" . ,t))))]
    [(CTuple l a*)
     (define len : Index (length a*))
     (unless (= l len)
       (error 'sr-coercion "length mismatch"))
     (begin$
       (assign$ second-tag
         (op$ + (op$ %<< (Quote (length a*)) COERCION-SECOND-TAG-SHIFT)
              COERCION-TUPLE-SECOND-TAG))
       (sr-alloc "tuple_coercion" COERCION-MEDIATING-TAG
                 `(("num"  . ,second-tag)
                   .
                   ,(map (lambda ([a : Immediate-Coercion])
                           (cons "item" (sr-immediate-coercion a)))
                         a*))))]
    [(Failed l)
     (sr-alloc "failed-coercion" COERCION-FAILED-TAG `(("label" . ,(Quote l))))]
    [other (error 'specify-representation/type "unmatched ~a" other)]))

(: allocate-bound-coercion : CoC6-Bnd-Crcn -> D0-Expr)
(define (allocate-bound-coercion bnd)
  (match-define (cons u c) bnd) (Assign u (sr-coercion c)))

(: untag-deref-gproxy (-> D0-Expr (-> D0-Expr D0-Expr)))
(define ((untag-deref-gproxy index) proxy)
  (op$ Array-ref (op$ binary-xor proxy GPROXY-TAG) index))

;; fold map through bindings
(: sr-bnd* ((CoC6-Expr -> D0-Expr) -> (CoC6-Bnd-Data* -> D0-Bnd*)))
(define ((sr-bnd* sr-expr) b*)
  (: sr-bnd (CoC6-Bnd-Data -> D0-Bnd))
  (define (sr-bnd b)
    (cons (car b) (sr-expr (cdr b))))
  (map sr-bnd b*))

(: sr-bnd-code* ((CoC6-Expr Env IndexMap -> D0-Expr)
                 -> (CoC6-Bnd-Code* -> D0-Bnd-Code*)))
(define ((sr-bnd-code* sr-expr/env) b*)
  (: sr-bnd (CoC6-Bnd-Code -> D0-Bnd-Code))
  (define (sr-bnd b)
    (match-let ([(cons u (Code u* e)) b])
      (let ([env (extend* (hash) u* (map var u*))])
        (cons u (Code u* (sr-expr/env e env empty-index-map))))))
  (map sr-bnd b*))

(: sr-observe ((String -> Uid) D0-Expr Grift-Type -> D0-Expr))
(define (sr-observe next-uid! e t)
  (: generate-print ((Var Uid) Grift-Type -> D0-Expr))
  (define (generate-print id t)
    (define who 'sr-observe)
    (debug off who id t)
    (cond
      [(Int? t) (op$ Printf (Quote "Int : %ld\n") id)]
      ;; This is a fragile hack
      ;; switch to typed ASTs
      [(Float? t) (begin$ (op$ Print (Quote "Float : "))
                          (op$ print-float id (Quote 9))
                          (op$ Print (Quote "\n")))]
      [(Character? t)
       (begin$ (op$ Print (Quote "Char : "))
               (op$ print-char id)
               (op$ Print (Quote "\n")))]
      [(Bool? t)
       (If id
           (op$ Print (Quote "Bool : #t\n"))
           (op$ Print (Quote "Bool : #f\n")))]
      [(Unit? t) (op$ Print (Quote "Unit : ()\n"))]
      [(Fn? t) (op$ Print (Quote "Function : ?\n"))]
      [(GRef? t) (op$ Print (Quote "GReference : ?\n"))]
      [(GVect? t) (op$ Print (Quote "GVector : ?\n"))]
      [(MRef? t) (op$ Print (Quote "MReference : ?\n"))]
      [(MVect? t) (op$ Print (Quote "MVector : ?\n"))]
      [(STuple? t) (op$ Print (Quote "Tuple : ?\n"))]
      [(Dyn? t) (op$ Print (Quote "Dynamic : ?\n"))]
      [(Mu? t)
       (match-define (Mu s) t)
       (generate-print id (grift-type-instantiate s t))]
      [else
       (error 'sr-observe "printing other things: ~a" t)]))
  (begin$ (assign$ res e) (generate-print res t)))

#;(TODO GET RID OF TAGS IN THE COMPILER)
(: sr-tag (Tag-Symbol -> (Quote Integer)))
(define (sr-tag t)
  (case t
    [(Int)    DYN-INT-TAG]
    [(Char)   DYN-CHAR-TAG]
    [(Bool)   DYN-BOOL-TAG]
    [(Unit)   DYN-UNIT-TAG]
    [(Atomic) TYPE-ATOMIC-TAG]
    [(Fn)     TYPE-FN-TAG]
    [(GRef)   TYPE-GREF-TAG]
    [(GVect)  TYPE-GVECT-TAG]
    [(Boxed)  DYN-BOXED-TAG]
    [(MRef)   TYPE-MREF-TAG]
    [(MVect)  TYPE-MVECT-TAG]
    [(STuple) TYPE-TUPLE-TAG]
    [else (error 'sr-tag "invalid: ~a" t)]))

(: index-closure (Nat Uid Uid* -> IndexMap))
(define (index-closure offset clos fvar*)
  (define ((fvar-err f))
    (error 'specifiy-representation "failed to index free var ~a from clos ~a"
           f clos))
  (define (clos-err c f)
    (error 'specify-representation
           "unbound closure index ~a from closure ~a inside of clos ~a"
           f c clos))
  (let ([map (for/hash : (HashTable Uid Nat)
                 ([fvar : Uid fvar*]
                  [i : Nat (in-naturals offset)])
               (values fvar i))])
    (lambda ([c : Uid] [f : Uid])
      : Nat
      (if (uid=? c clos)
          (hash-ref map f (fvar-err f))
          (clos-err c f)))))

(: sr-clos-ref-code (-> D0-Expr D0-Expr))
(define (sr-clos-ref-code clos) (op$ Array-ref  clos CLOS-CODE-INDEX))

(: sr-clos-ref-caster (-> D0-Expr D0-Expr))
(define (sr-clos-ref-caster clos) (op$ Array-ref clos CLOS-CSTR-INDEX))

(define-type Env (HashTable Uid D0-Expr))

(define-syntax-rule (extend e k v) (hash-set e k v))

(: extend* (-> Env Uid* D0-Expr* Env))
(define (extend* env id* exp*)
  (match* (id* exp*)
    [('() _) env]
    [(_ '()) env]
    [((cons id id*) (cons exp exp*))
     (extend* (extend env id exp) id* exp*)]))

;; The variable is a normal variable
(: var  (-> Uid D0-Expr))
(define (var id) (Var id))

(: label (-> Uid D0-Expr))
(define (label id) (Code-Label id))

(: lookup (-> Env Uid D0-Expr))
(define (lookup e u) (hash-ref e u (lookup-error e u)))

(define (lookup-error e u)
  (lambda ()
    (error 'specify-representation/lookup
           "Unbound uid ~a\n\tin program with env ~a" u e)))

(define-type Triv (U (Quote String) (Quote Integer) (Code-Label Uid) (Var Uid)))
(define-predicate triv? Triv)

(: rename (-> String (-> Any String)))
(define (rename name) (lambda (_) name))

(define sr-quote : (D0-Literal -> D0-Expr) Quote)

(define (empty-index-map u i)
  (error 'specify-representation "attempt to index without index map ~a ~a" u i))

(: sr-closures : (Closure* CoC6-Expr CoC6-Expr) ->
   (Values (Bnd* (Fun D0-Expr)) Uid* D0-Expr* D0-Expr*))
(define (sr-closures c*)
  (: rec : CoC6-Expr -> D0-Expr)
  (define (rec e) (sr-expr (hasheq) empty-index-map e))
  (for/fold ([c* : (Bnd* (Fun D0-Expr)) '()]
             [i* : Uid* '()]
             [a* : D0-Expr* '()]
             [e* : D0-Expr* '()])
            ([c c*])
    (match-define (Closure name _ c/d label self ctr? f* p* e) c)
    (define code*
      (case c/d
        [(regular code-only)
         (cons (cons label (Code (cons self p*) (rec e))) c*)]
        [else c*]))
    (define-values (id* alloc* init*)
      (case c/d
        [(regular closure-only)
         (define init-fv-expr* (map rec f*))
         (define castor (if ctr? (Code-Label ctr?) FALSE-IMDT))
         (define init-expr* (list* (Code-Label label) castor init-fv-expr*))
         (define size   (Quote (+ 2 (length init-expr*))))
         (define clos (Var name))
         (values (cons name i*)
                 (cons (Assign name (op$ Alloc size)) a*) 
                 (for/fold ([e* : D0-Expr* e*])
                           ([e init-expr*] [i (in-naturals)])
                   (cons (op$ Array-set! clos (Quote i) e) e*)))]
        [else (values i* a* e*)])) 
    (values code* id* alloc* init*)))


(define (type->dyn-tag t default-th)
  (match t
    [(Int)  DYN-INT-TAG]
    [(Bool) DYN-BOOL-TAG]
    [(Unit) DYN-UNIT-TAG]
    [(Character) DYN-CHAR-TAG]
    [other  (default-th)]))
