#lang racket/base

(require (for-syntax racket/base racket/contract racket/promise racket/match syntax/srcloc
                     "../dependent-stream.rkt"
                     "machine.rkt" "proof-state.rkt" "refinement.rkt" "../seal.rkt"))

(provide hole
         (for-syntax hole? tactic/c init-hole tactic-info-hook))
(begin-for-syntax
  (define subgoal-count-prop 'refinement-subgoal-count)
  ;; Keep others from messing with the subgoal count
  (struct goal-count (count))

  (define (leftmost v)
    (if (pair? v)
        (leftmost (car v))
        v))

  (define (save-subgoal-count stx n)
    (syntax-property stx subgoal-count-prop (goal-count n)))
  (define (get-subgoal-count stx)
    (define n (leftmost (syntax-property stx subgoal-count-prop)))
    (if n (goal-count-count n) (error 'no-subgoal-count)))

  (define goal-prop 'the-goal)
  (struct the-goal (goal))

  (define (save-goal stx g)
    (syntax-property stx goal-prop (the-goal g)))
  (define (refinement-goal stx)
    (define g (leftmost (syntax-property stx goal-prop)))
    (if g (the-goal-goal g) (error 'no-goal))))


(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)
       #t))

(define-for-syntax ((nat-less-than/c n) k)
  (and (exact-nonnegative-integer? k)
       (< k n)))

(define-for-syntax tactic/c
  (struct/dc REFINE
             [subgoal-count exact-nonnegative-integer?]
             [tactic (subgoal-count)
                   (-> hole?
                       (-> (nat-less-than/c subgoal-count) hole? any/c hole?)
                       (-> string? any/c) ;; failure continuation
                       sealed?)]))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(begin-for-syntax
  #;
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


(define-for-syntax (more-specific? loc1 loc2)
  (and (equal? (source-location-source loc1) (source-location-source loc2))
       (>= (source-location-position loc1) (source-location-position loc2))
       (<= (+ (source-location-position loc1) (source-location-span loc1))
           (+ (source-location-position loc2) (source-location-span loc2)))))

(begin-for-syntax
  )

(define-syntax (hole stx)
  (let internal-step ([st (get-machine-state stx)])
    (match st
      [(LCF-state offset skips (ID) cont goal loc)
       (match cont
         [(list) ((no-more-tactics-hook) stx)]
         [(list-rest (THEN-frame next) more)
          ;; here, we need to local-expand
          (internal-step (LCF-state offset skips next more goal loc))]
         [(list-rest (THENL-frame nexts) more)
          (internal-step
           (LCF-state (max 0 (- offset (length nexts)))
                      skips
                      (if (< offset (length nexts))
                          (list-ref nexts offset)
                          (ID))
                      more
                      goal
                      loc))]
         [(list-rest (ORELSE-frame _) more)
          (internal-step (LCF-state offset skips (ID) more goal loc))]
         [(list-rest (LOC-frame old-loc) more)
          ((tactic-info-hook) loc goal 'out)
          (internal-step (LCF-state offset skips (ID) more goal old-loc))])]
      [(LCF-state offset skips (THEN t1 t2) cont goal loc)
       (internal-step (LCF-state offset skips t1 (cons (THEN-frame t2) cont) goal loc))]
      [(LCF-state offset skips (THENL t1 t2s) cont goal loc)
       (internal-step (LCF-state offset skips t1 (cons (THENL-frame t2s) cont) goal loc))]
      [(LCF-state offset skips (ORELSE t1 t2) cont goal loc)
       ;; Here, we need to local-expand in order to capture a
       ;; continuation that includes macro expansion.
       (match (let/ec k
                (cons 'ok
                      (let-values ([(_ opaque)
                                    (syntax-local-expand-expression
                                     (set-machine-state
                                      stx
                                      (LCF-state offset
                                                 skips
                                                    t1
                                                    (cons (ORELSE-frame (lambda (x)
                                                                          (k (cons 'failed x))))
                                                          cont)
                                                    goal loc)))])
                        opaque)))
         [(cons 'ok out)
          ;; NB: This is not sealed, because the hole that is local-expanded does unsealing
          out]
         [(cons 'failed err)
          (internal-step (LCF-state offset skips t2 cont goal loc))])]
      [(LCF-state offset skips (FAIL message) cont goal loc)
       ((get-handler cont) message)]
      [(LCF-state offset skips (REFINE goal-count fun) cont goal loc)
       (define (next-subgoal refinement))
       ;; Here, we unseal, because refinement rules do seal returns.
       (save-goal
        (save-subgoal-count
          (unseal/hole
           stx
           (fun stx (lambda (i the-hole new-goal)
                      ;                   (displayln `(,offset ,i ,goal-count ))
                      (set-machine-state the-hole (LCF-state (+ offset i) skips (ID) cont new-goal loc)))
                (get-handler cont)))
          goal-count)
        goal)]
      [(LCF-state offset skips (? procedure? th) cont goal loc)
       (internal-step (LCF-state offset skips (th) cont goal loc))]
      [(LCF-state offset skips (LOC where next) cont goal loc)
       (if (more-specific? where loc)
           (begin ((tactic-info-hook) where goal 'in)
                  (internal-step (LCF-state offset skips next (cons (LOC-frame loc) cont) goal where)))
           (internal-step (LCF-state offset skips next cont goal where)))]
      [(LCF-state offset skips (REFLECT todo) cont goal loc)
       (internal-step (LCF-state offset skips (todo st) cont goal loc))])))


(define-for-syntax (init-hole unseal tactic goal loc)
  (set-basic-state #'hole unseal tactic goal loc))

#;
(define-for-syntax (tactic/loc tac loc)
  (lambda (hole make-subgoal)
    ((force tac) (set-loc hole loc) make-subgoal)))
