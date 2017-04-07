#lang racket

(require (except-in "lcfish.rkt" run-script)
         (for-syntax (for-syntax racket/base))
         "engine/hole.rkt"
         (for-syntax "engine/proof-state.rkt")
         "tooltip-info.rkt"
         (for-syntax "seal.rkt")
         (for-syntax "stx-utils.rkt"
                     racket/contract racket/match racket/promise syntax/parse racket/port syntax/srcloc)
         racket/stxparam
         (for-syntax racket/stream)
         (for-template racket/base))

(module+ test
  (require rackunit syntax/macro-testing))



(begin-for-syntax
  (define-stamp test)
  (tactic-info-hook
   (tooltip-info (lambda (x) (format "~a" x)))))

(define-syntax (run-script stx)
  (syntax-parse stx
    [(run-script tactic ...)
     #`(let-syntax ([go (lambda (s)
                          (init-hole
                           unseal-test
                           (make-skip seal-test)
                           (then tactic ...)
                           'goal
                           #'#,stx))])
         (go))]))

(define-for-syntax ((emit out-stx) hole make-subgoal)
    (displayln `(emitting ,out-stx ,(get-hole-loc hole)))
  (seal-test (refine hole out-stx)))

(define-for-syntax (l hole make-subgoal)
  (seal-test (refine hole #`(list #,((stream-ref make-subgoal 0) hole 1)
                                   #,((stream-ref make-subgoal 1) hole 2)))))
(define foo
  (run-script (then-l (then l skip)
                      ((emit #''a)
                       (emit #''b)))))
foo
