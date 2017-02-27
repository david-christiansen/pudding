#lang racket/base
(require racket/match racket/promise (for-template racket/base))

(provide basic-handler basic-proof-state proof-state? no-more-tactics-hook
         set-tactic set-goal set-handler set-loc set-basic-state
         get-hole-tactic get-hole-handler get-hole-loc get-hole-goal)

(define proof-state-prop 'proof-state)

(define (leftmost v)
  (if (pair? v)
      (leftmost (car v))
      v))

(define no-more-tactics-hook
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
     ((error-display-handler) (exn-message e) e)
     #`(raise #,e))))
  
(struct proof-state
  (tactic
   loc
   handler
   goal)
  #:transparent)


(define (get-proof-state stx)
  (leftmost (syntax-property stx 'proof-state)))

(define (set-proof-state stx st)
  (syntax-property stx 'proof-state st))

(define ((update-proof-state f) stx)
  (define old-state (get-proof-state stx))
  (set-proof-state stx (f old-state)))

(define basic-proof-state
  (proof-state (lambda (h n-t)
                 ((no-more-tactics-hook) h))
               #f
               (lambda (e)
                 ((basic-handler) e))
               #f))

(define (set-basic-state h)
  (set-proof-state h basic-proof-state))

(define ((proof-state-with-tactic tac) st)
  (match st
    [(proof-state _ loc h g) (proof-state tac loc h g)]))

(define ((proof-state-with-loc loc) st)
  (match st
    [(proof-state tac _ h g) (proof-state tac loc h g)]))

(define ((proof-state-with-handler h) st)
  (match st
    [(proof-state tac loc _ g) (proof-state tac loc h g)]))

(define ((proof-state-with-goal g) st)
  (match st
    [(proof-state tac loc h _) (proof-state tac loc h g)]))

(define (set-tactic hole tac)
  ((update-proof-state (proof-state-with-tactic tac)) hole))

(define (set-loc hole loc)
  ((update-proof-state (proof-state-with-loc loc)) hole))

(define (set-handler hole h)
  ((update-proof-state (proof-state-with-handler h)) hole))

(define (set-goal hole g)
  ((update-proof-state (proof-state-with-goal g)) hole))

(define (get-hole-tactic h)
  (proof-state-tactic (get-proof-state h)))

(define (get-hole-handler h)
  (proof-state-handler (get-proof-state h)))

(define (get-hole-goal h)
  (proof-state-goal (get-proof-state h)))

(define (get-hole-loc h)
  (proof-state-loc (get-proof-state h)))

