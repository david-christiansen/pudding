#lang racket/base
(require racket/match
         racket/promise
         (for-template racket/base)
         "refinement.rkt"
         "machine.rkt"
         "../stx-utils.rkt")

(provide basic-handler basic-proof-state proof-state? no-more-tactics-hook
         get-machine-state set-machine-state set-basic-state
         unseal/hole refine)

(define proof-state-prop 'proof-state)

(require racket/contract)
(define/contract no-more-tactics-hook
  (parameter/c (-> syntax? syntax?))
  (make-parameter
   (lambda (hole-stx)
     (define st (get-proof-state hole-stx))
     (define loc (proof-state-loc st))
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
   loc
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
    [(proof-state m _ _) m]))

(define (set-machine-state stx m)
  (match (get-proof-state stx)
    [(proof-state _ loc unseal)
     (set-proof-state stx (proof-state m loc unseal))]))

(define ((update-machine-state f) stx)
  (set-machine-state (f (get-machine-state stx))))

(define (basic-machine-state goal tactic)
  (LCF-state (THEN tactic
                   (TACTIC (lambda (h next)
                             ((no-more-tactics-hook) h))))
             '()
             goal))

(define (basic-proof-state tactic unseal)
  (proof-state (basic-machine-state #f tactic)
               #f
               unseal))

(define (set-basic-state hole-stx tactic unseal)
  (set-proof-state hole-stx (basic-proof-state tactic unseal)))

(define (unseal/hole h r)
  (match (get-proof-state h)
    [(proof-state _ _ u) (u r)]))

(define (get-hole-loc hole-stx)
  (proof-state-loc (get-proof-state hole-stx)))

(define (refine hole-stx new-stx)
  (refinement new-stx
              (LCF-state-goal (get-machine-state hole-stx))
              (get-hole-loc hole-stx)))
