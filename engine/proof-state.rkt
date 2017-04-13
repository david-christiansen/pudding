#lang racket/base
(require racket/match
         racket/promise
         (for-template racket/base)
         "refinement.rkt"
         "machine.rkt"
         "../stx-utils.rkt")

(provide basic-handler basic-proof-state proof-state? no-more-tactics-hook
         get-machine-state set-machine-state set-basic-state get-hole-goal get-hole-loc
         unseal/hole refine)

(define proof-state-prop 'proof-state)

(require racket/contract)
(define/contract no-more-tactics-hook
  (parameter/c (-> syntax? syntax?))
  (make-parameter
   (lambda (hole-stx)
     (define st (get-proof-state hole-stx))
     (define loc (LCF-state-loc (proof-state-machine-state st)))
     (raise-syntax-error 'no-more-tactics "No more tactics" loc))
   (lambda (f)
     (if (procedure? f)
         f
         (error "must be a proc")))))

(define basic-handler
  (make-parameter
   (lambda (e)
     #;((error-display-handler) (exn-message e) e)
     #;#`(raise #,e)
     (raise e))))
  
(struct proof-state
  (machine-state
   unseal)
  #:transparent)


(define (get-proof-state stx)
  (leftmost (syntax-property stx proof-state-prop)))

(define (set-proof-state stx st)
  (syntax-property stx proof-state-prop st))

(define ((update-proof-state f) stx)
  (define old-state (get-proof-state stx))
  (set-proof-state stx (f old-state)))

(define (get-machine-state stx)
  (match (get-proof-state stx)
    [(proof-state m _) m]))

(define (set-machine-state stx m)
  (match (get-proof-state stx)
    [(proof-state _ unseal)
     (set-proof-state stx (proof-state m unseal))]))

(define ((update-machine-state f) stx)
  (set-machine-state (f (get-machine-state stx))))

(define (basic-machine-state goal tactic loc)
  (LCF-state (THEN tactic
                   (TACTIC (lambda (h next)
                             ((no-more-tactics-hook) h))))
             '()
             goal
             loc))

(define (basic-proof-state unseal tactic goal loc)
  (proof-state (basic-machine-state goal tactic loc)
               unseal))

(define (set-basic-state hole-stx unseal tactic goal loc)
  (set-proof-state hole-stx (basic-proof-state unseal tactic goal loc)))

(define (unseal/hole h r)
  (match (get-proof-state h)
    [(proof-state (LCF-state _ _ g _) u) (u g r)]))

(define (get-hole-loc hole-stx)
  (LCF-state-loc (proof-state-machine-state (get-proof-state hole-stx))))

(define (get-hole-goal hole-stx)
  (LCF-state-goal (proof-state-machine-state (get-proof-state hole-stx))))

(define (refine hole-stx new-stx)
  (refinement new-stx
              (LCF-state-goal (get-machine-state hole-stx))
              (get-hole-loc hole-stx)))
