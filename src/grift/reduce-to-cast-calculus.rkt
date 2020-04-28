#lang typed/racket/base/no-check

#|
This is a micro compiler that takes a path, reads the contents
of that file, parses the syntax into an ast, type-checks the
ast, and finally converts that ast into an equivalent ast
of the cast calculus.
|#

(require
 "./insert-casts.rkt"
 "./read.rkt"
 "./syntax-to-grift0.rkt"
 "./type-check.rkt"
 "../language/contracts.rkt"
 "./flow-judgement.rkt")

(provide reduce-to-cast-calculus)

(define (reduce-to-cast-calculus path)
  (flow-judgement (insert-casts ((optionally-contract type-check) (syntax->grift0 (read path))))))




