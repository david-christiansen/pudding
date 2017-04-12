#lang racket/base

(require (for-syntax racket/base racket/contract racket/promise racket/match
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
  (define/contract (no-more-tacticsi  old-hole new-goal)
    tactic/c
    (error 'todo)
    #;
    (set-tactic old-hole (lambda (h n-t)
                           ((no-more-tactics-hook) h)))))

(define-for-syntax tactic-info-hook
  (make-parameter
   (lambda (h) #f)))

(define-for-syntax (get-handler cont)
  (match cont
    [(list)
     (lambda (e) (error e))]
    [(list (ORELSE-frame h) _ ...)
     h]
    [(list _ frames ...)
     (get-handler frames)]))


(define-syntax (hole stx)
  (match-define (LCF-state control cont goal)
    (get-machine-state stx))
  (define sealed-result
    (let internal-step ([st (get-machine-state stx)])
      (displayln st)
      (match st
        [(LCF-state (ID) cont goal)
         (match cont
           [(list) ((no-more-tactics-hook) stx)]
           [(list-rest (THEN-frame next) more)
            (internal-step (LCF-state next more goal))]
           [(list-rest (THENL-frame nexts) more)
            (internal-step
             (match nexts
               [(list) (LCF-state (ID) more goal)]
               [(list-rest t ts) (LCF-state t more goal)]))]
           [(list-rest (ORELSE-frame _) more)
            (internal-step (LCF-state (ID) more goal))])]
        [(LCF-state (THEN t1 t2) cont goal)
         (internal-step (LCF-state t1 (cons (THEN-frame t2) cont) goal))]
        [(LCF-state (THENL t1 t2s) cont goal)
         (internal-step (LCF-state t1 (cons (THENL-frame t2s) cont) goal))]
        [(LCF-state (ORELSE t1 t2) cont goal)
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
                                                  goal))
                                      'expression
                                      null)))
           [(cons 'ok out) out]
           [(cons 'failed err)
            (internal-step (LCF-state t2 cont goal))])]
        [(LCF-state (FAIL message) cont goal)
         ((get-handler cont) message)]
        [(LCF-state (TACTIC fun) cont goal)
         (fun stx
              (let pop ([c cont])
                (match c
                  [(list) (lambda (_ goal) ((no-more-tactics-hook) stx))]
                  [(list-rest (THEN-frame t2) more)
                   (lambda (_ new-goal)
                     (set-machine-state stx (LCF-state t2 more new-goal)))]
                  [(list-rest (THENL-frame t2s) more)
                   (lambda (i new-goal)
                     (displayln `(here it is ,i ,(list-ref t2s i)))
                     (set-machine-state
                      stx
                      (LCF-state
                       (if (< i (length t2s))
                           (list-ref t2s i)
                           (ID))
                       more
                       new-goal)))]
                  [(list-rest (ORELSE-frame _) more)
                   (pop more)])))])))
  (define result (unseal/hole stx sealed-result))
  (displayln `(emitting ,sealed-result --> ,result))
  #;((tactic-info-hook) (refinement-loc result) (refinement-goal result))
  result)


(define-for-syntax (init-hole unseal tactic goal loc)
  (set-basic-state #'hole tactic unseal))

#;
(define-for-syntax (tactic/loc tac loc)
  (lambda (hole make-subgoal)
    ((force tac) (set-loc hole loc) make-subgoal)))

