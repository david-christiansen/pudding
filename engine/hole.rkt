#lang racket/base

(require (for-syntax racket/base racket/contract racket/promise racket/match syntax/srcloc
                     "machine.rkt" "proof-state.rkt" "refinement.rkt" "../seal.rkt"))

(provide hole 
         (for-syntax hole? tactic/c init-hole tactic-info-hook))

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
  (-> hole? (-> exact-nonnegative-integer? hole? any/c hole?) sealed?))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(begin-for-syntax
  (define/contract (no-more-tactics old-hole new-goal)
    tactic/c
    (error 'todo)
    #;
    (set-tactic old-hole (lambda (h n-t)
                           ((no-more-tactics-hook) h)))))

(begin-for-syntax
  (define/contract tactic-info-hook
    (parameter/c (-> source-location? any/c (or/c 'in 'out) void?))
    (make-parameter
     (lambda (where goal mode)
       (void)))))

(define-for-syntax (get-handler cont)
  (match cont
    [(list)
     (lambda (e) (error e))]
    [(list (ORELSE-frame h) _ ...)
     h]
    [(list _ frames ...)
     (get-handler frames)]))


(define-syntax (hole stx)
  (match-define (LCF-state control cont goal loc)
    (get-machine-state stx))
  (define result
    (let internal-step ([st (get-machine-state stx)])
      (match st
        [(LCF-state (ID) cont goal loc)
         (match cont
           [(list) ((no-more-tactics-hook) stx)]
           [(list-rest (THEN-frame next) more)
            (internal-step (LCF-state next more goal loc))]
           [(list-rest (THENL-frame nexts) more)
            (internal-step
             (match nexts
               [(list) (LCF-state (ID) more goal loc)]
               [(list-rest t ts) (LCF-state t more goal loc)]))]
           [(list-rest (ORELSE-frame _) more)
            (internal-step (LCF-state (ID) more goal loc))]
           [(list-rest (LOC-frame old-loc) more)
            ((tactic-info-hook) loc goal 'out)
            (internal-step (LCF-state (ID) more goal old-loc))])]
        [(LCF-state (THEN t1 t2) cont goal loc)
         (internal-step (LCF-state t1 (cons (THEN-frame t2) cont) goal loc))]
        [(LCF-state (THENL t1 t2s) cont goal loc)
         (internal-step (LCF-state t1 (cons (THENL-frame t2s) cont) goal loc))]
        [(LCF-state (ORELSE t1 t2) cont goal loc)
         ;; Here, we need to local-expand in order to capture a
         ;; continuation that includes macro expansion.
         (match (let/ec k
                  (cons 'ok
                        (local-expand (set-machine-state
                                       stx
                                       (LCF-state t1
                                                  (cons (ORELSE-frame (lambda (x)
                                                                        (k (cons 'failed x))))
                                                        cont)
                                                  goal loc))
                                      'expression
                                      null)))
           [(cons 'ok out)
            ;; NB: This is not sealed, because the hole that is local-expanded does unsealing
            out]
           [(cons 'failed err)
            (internal-step (LCF-state t2 cont goal loc))])]
        [(LCF-state (FAIL message) cont goal loc)
         ((get-handler cont) message)]
        [(LCF-state (TACTIC fun) cont goal loc)
         ;; Here, we unseal, because refinement rules do seal returns.
         (unseal/hole
          stx
          (fun stx
               (let pop ([c cont]
                         [l loc])
                 (match c
                   [(list) (lambda (_ goal loc) ((no-more-tactics-hook) stx))]
                   [(list-rest (THEN-frame t2) more)
                    (lambda (_ new-goal)
                      (set-machine-state stx (LCF-state t2 more new-goal l)))]
                   [(list-rest (THENL-frame t2s) more)
                    (lambda (i new-goal)
                      (set-machine-state
                       stx
                       (LCF-state
                        (if (< i (length t2s))
                            (list-ref t2s i)
                            (ID))
                        more
                        new-goal
                        l)))]
                   [(list-rest (ORELSE-frame _) more)
                    (pop more l)]
                   [(list-rest (LOC-frame old-loc) more)
                    ((tactic-info-hook) loc goal 'out)
                    (pop more old-loc)]))))]
        [(LCF-state (? procedure? th) cont goal loc)
         (internal-step (LCF-state (th) cont goal loc))]
        [(LCF-state (LOC where next) cont goal loc)
         ((tactic-info-hook) where goal 'in)
         (internal-step (LCF-state next (cons (LOC-frame loc) cont) goal where))])))
  result)


(define-for-syntax (init-hole unseal tactic goal loc)
  (set-basic-state #'hole tactic unseal))

#;
(define-for-syntax (tactic/loc tac loc)
  (lambda (hole make-subgoal)
    ((force tac) (set-loc hole loc) make-subgoal)))

