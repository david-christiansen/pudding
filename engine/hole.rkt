#lang racket/base

(require racket/contract/base
         (for-syntax racket/base racket/contract racket/promise syntax/srcloc
                     "proof-state.rkt" "refinement.rkt" "../seal.rkt"))

(provide hole
         (for-syntax hole?
                     tactic/c
                     multitactic/c
                     init-hole tactic-info-hook tactic/loc
                     (rename-out [make-tactic tactic]
                                 [make-multi multitactic])))

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)
       #t))


(define-for-syntax nat? exact-nonnegative-integer?)

(begin-for-syntax
  (struct tactic (code) #:transparent
    #:property prop:procedure (struct-field-index code))
  (struct multitactic (code) #:transparent
    #:property prop:procedure (struct-field-index code)))

;; A tactic is a procedure that takes the hole on which it is invoked
;; and a "continuation" procedure that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c tactic?)

(define-for-syntax multitactic/c multitactic?)

(begin-for-syntax
  (define/contract (make-tactic t)
    (-> (-> syntax? multitactic? sealed?) tactic?)
    (tactic t))
  (define/contract (make-multi mt)
    (-> (-> exact-nonnegative-integer? tactic?) multitactic?)
    (multitactic mt)))

;; A multitactic that doesn't work. Used at the end of scripts.
(define-for-syntax no-more-tactics
  (multitactic
   (procedure-rename (lambda (i)
                       (tactic (lambda (hole _) ((no-more-tactics-hook) hole))))
                     'no-more-tactics)))

(define-for-syntax tactic-info-hook
  (make-parameter
   (lambda (h) #f)))

(define-syntax (hole stx)
  (define tac (get-hole-tactic stx))
  (define sealed-result (tac stx no-more-tactics))
  (when (void? sealed-result)
    (eprintf "bad!!! ~s\n" (list tac stx))
    (error 'FAIL))
  (define result (unseal/hole stx sealed-result))

  ((tactic-info-hook) (refinement-loc result) (refinement-goal result))
  (refinement-stx result))


(define-for-syntax (init-hole unseal skip-tac tactic goal loc)
  (set-tactic
   (set-loc
    (set-goal
     (set-basic-state #'hole unseal skip-tac)
     goal)
    loc)
   tactic))


(begin-for-syntax
  (define/contract (tactic/loc tac loc)
    (-> (or/c tactic/c (promise/c tactic/c)) source-location?
        tactic/c)
    (make-tactic (procedure-rename (lambda (hole make-subgoal)
                                     ((force tac) (set-loc hole loc) make-subgoal))
                                   (string->symbol (format "tac/loc-~a" (object-name tac)))))))

