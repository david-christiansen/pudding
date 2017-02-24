#lang racket/base

(require (for-syntax racket/base racket/contract
                     "proof-state.rkt"))

(provide hole 
         (for-syntax hole? tactic/c basic-hole))

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)))


;; A tactic is a procedure that takes the hole on which it is invoked
;; and a "continuation" procedure that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c
  (-> syntax? (-> hole? hole?) syntax?))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(define-for-syntax (no-more-tactics h)
  (set-tactic #'hole (lambda (h n-t) (no-more-tactics-hook) h)))

(define-syntax (hole stx)
  (define tac (get-hole-tactic stx))
  (tac stx no-more-tactics))

(define-for-syntax basic-hole
  (set-basic-state #'hole))