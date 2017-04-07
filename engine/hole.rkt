#lang racket/base

(require (for-syntax racket/base racket/contract racket/promise racket/stream
                     "proof-state.rkt" "refinement.rkt" "../seal.rkt"))

(provide hole 
         (for-syntax hole? tactic/c init-hole tactic-info-hook tactic/loc))

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)
       #t))


;; A tactic is a procedure that takes the hole on which it is invoked
;; and a stream of "continuation" procedures that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c
  (-> syntax? (stream/c (-> hole? any/c hole?)) sealed?))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(define-for-syntax (no-more-tactics old-hole new-goal)
  (set-tactic old-hole (lambda (h n-t)
                         ((no-more-tactics-hook) h))))

(define-for-syntax never-more-tactics (stream-cons no-more-tactics never-more-tactics))

(define-for-syntax tactic-info-hook
  (make-parameter
   (lambda (h) #f)))

(define-syntax (hole stx)
  (define tac (get-hole-tactic stx))
  (displayln tac)
  (define sealed-result (tac stx never-more-tactics))
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


(define-for-syntax (tactic/loc tac loc)
  (procedure-rename
   (lambda (hole make-subgoal)
     ((force tac) (set-loc hole loc) make-subgoal))
   (gensym (format "tactic/loc: ~a ~a" tac loc))))

