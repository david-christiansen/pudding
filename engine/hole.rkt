#lang racket/base

(require (for-syntax racket/base racket/contract racket/promise
                     "proof-state.rkt"))

(provide hole
         (for-syntax hole? tactic/c init-hole tactic-info-hook tactic/loc))

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)
       #t))


;; A tactic is a procedure that takes the hole on which it is invoked
;; and a "continuation" procedure that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c
  (-> syntax? (-> hole? any/c hole?) syntax?))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(define-for-syntax (no-more-tactics old-hole new-goal)
  (set-tactic old-hole (lambda (h n-t)
                         ((no-more-tactics-hook) h))))

(define-for-syntax tactic-info-hook
  (make-parameter
   (lambda (h) #f)))

(define-syntax (hole stx)
  ((tactic-info-hook) stx)
  (define tac (get-hole-tactic stx))
  (tac stx no-more-tactics))


(define-for-syntax (init-hole tactic goal loc)
  (set-tactic
   (set-loc
    (set-goal
     (set-basic-state #'hole)
     goal)
    loc)
   tactic))

(define-for-syntax (tactic/loc tac loc)
  (lambda (hole make-subgoal)
    ((tactic-info-hook) hole)
    ((force tac) (set-loc hole loc) make-subgoal)))