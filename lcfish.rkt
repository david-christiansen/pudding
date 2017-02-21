#lang racket
(require (for-syntax racket/generator racket/contract racket/sequence racket/promise racket/match
                     
                     (for-syntax racket/base))
         racket/stxparam)

(provide
 (for-syntax skip fail try then then-l emit tactic/c hole-with-tactic log basic-proof-state
             no-more-tactics-hook tactic-info-hook basic-handler hole-loc get-proof-state set-tactic-location)
 tactic-debug? tactic-debug-hook
 run-script)

(module+ test
  (require rackunit))

(define-syntax-parameter tactic-debug? #f)
(define-syntax-parameter tactic-debug-hook
  (lambda (hole-stx)
    (printf "Hole state: ~a\n" (get-proof-state hole-stx))))

(begin-for-syntax
  (define tactic-info-hook
    (make-parameter
     (lambda (h) #f)))
  (define no-more-tactics-hook
    (make-parameter
     (lambda (hole-stx)
       (define st (get-proof-state hole-stx))
       (define loc (proof-state-loc st))
       (displayln st)
       (raise-syntax-error 'no-more-tactics "No more tactics" loc)))))



(begin-for-syntax
  (define basic-handler
    (make-parameter (lambda (e)
                      ((error-display-handler) (exn-message e) e)
                      #`(raise #,e)
                      #;(raise e))))
  
  (struct proof-state
    (tactic
     loc
     handler)
    #:transparent)

  (define basic-proof-state
    (proof-state (lambda (h n-t) ((no-more-tactics-hook) h))
                 #f
                 (lambda (e)
                   ((basic-handler) e))))

  (define (proof-state-with-tactic st tac)
    (match st
      [(proof-state _ loc h) (proof-state tac loc h)]))

  (define (proof-state-with-loc st loc)
    (match st
      [(proof-state tac _ h) (proof-state tac loc h)]))

  (define (proof-state-with-handler st h)
    (match st
      [(proof-state tac loc _) (proof-state tac loc h)]))
  )

(define-for-syntax (leftmost v)
  (if (pair? v)
      (leftmost (car v))
      v))

(define-for-syntax (get-proof-state stx)
  (leftmost (syntax-property stx 'proof-state)))

(define-for-syntax (hole-loc stx)
  (proof-state-loc (get-proof-state stx)))

(define-for-syntax (set-tactic-location hole-stx loc)
  (syntax-property hole-stx 'proof-state
                   (proof-state-with-loc (get-proof-state hole-stx) loc)))

;; Get the tactic to run in a hole out of its state
(define-for-syntax (get-hole-tactic hole-stx)
  (define st (get-proof-state hole-stx))
  (define tac (proof-state-tactic st))
  tac)

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (syntax-property stx 'proof-state)))

;; A tactic is a procedure that takes the hole on which it is invoked
;; and a "continuation" procedure that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c
  (-> syntax? (-> proof-state? hole?) syntax?))

(define-for-syntax (copy-goal old-goal new-goal)
  (syntax-property new-goal 'goal (syntax-property old-goal 'goal)))

;; Failing tactics should raise an exception for which exn:fail:tactics? is truthy.
(begin-for-syntax
  (define (syntax->srcloc stx)
    (srcloc (syntax-source stx)
            (syntax-line stx)
            (syntax-column stx)
            (syntax-position stx)
            (syntax-span stx)))

  (struct exn:fail:tactics exn:fail (hole location)
    #:extra-constructor-name make-exn:fail:tactics
    #:property prop:exn:srclocs
    (lambda (e)
      (match (exn:fail:tactics-location e)
        [(? srcloc? loc)
         (list loc)]
        [(? syntax? stx)
         (list (syntax->srcloc stx))]
        [_ null]))))

(define-syntax (hole stx)
  (define tac (get-hole-tactic stx))
  (when (syntax-parameter-value #'tactic-debug?)
    ((syntax-parameter-value #'tactic-debug-hook) stx))
  (tac stx no-more-tactics))

;; Create a syntax object that is a hole, and will run the provided tactic.
(begin-for-syntax
  (define/contract (hole-with-tactic st tac)
    (-> proof-state? tactic/c syntax?)
    (define new-state (proof-state-with-tactic st tac))
    (syntax-property #'hole 'proof-state new-state))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
  (define (no-more-tactics st)
    (hole-with-tactic st (lambda (h n-t) ((no-more-tactics-hook) h)) ))
  
  ;; A tactic that does nothing.
  (define/contract (skip hole make-hole)
    tactic/c
    (define st (get-proof-state hole))
    (copy-goal hole (make-hole st)))

  (define/contract ((then-l* tac/loc . tacs) hole make-hole)
    (->* ((cons/c (or/c tactic/c (promise/c tactic/c))
                  (or/c #f srcloc? syntax?)))
         #:rest (listof (sequence/c (cons/c (or/c tactic/c (promise/c tactic/c))
                                            (or/c #f syntax? srcloc?))))
         tactic/c)
    (define tac (car tac/loc))
    (define loc (cdr tac/loc))
    (define old-st (get-proof-state hole))
    (define st (if loc (proof-state-with-loc old-st loc) old-st))
    (cond
      [(pair? tacs)
       (define inner-next
         (generator (state)
                    (for ([tac/loc2 (in-sequences (car tacs)
                                                  (in-cycle (in-value (cons skip #f))))])
                      (yield (hole-with-tactic
                              state
                              (lambda (hole-stx m-h)
                                ((apply then-l* tac/loc2 (cdr tacs))
                                 hole-stx
                                 make-hole)))))))
       ((force tac) (syntax-property hole 'proof-state st) inner-next)]
      [else
       ((force tac) (syntax-property hole 'proof-state st) make-hole)]))

  (define-syntax (then-l stx)
    (syntax-case stx ()
      [(_ tac1 (tac2 ...) ...)
       (let ([tactics/loc (for/list ([ts (syntax->list #'((tac2 ...) ...))])
                            (quasisyntax/loc ts
                             (list #,@(for/list ([t (syntax->list ts)])
                                        (quasisyntax/loc t
                                          (cons #,t #'#,t))))))])
       (quasisyntax/loc stx
         (then-l* (cons tac1 #'tac1) #,@tactics/loc)))]))

  ;; If tacs is empty, just run tac. Otherwise, run tac, with
  ;; (then . tacs) running in each subgoal.
  (define/contract ((then* tac/loc . tacs-and-locs) hole make-hole)
    (->* ((cons/c (or/c tactic/c (promise/c tactic/c))
                  (or/c #f srcloc? syntax?)))
         #:rest (listof (cons/c (or/c tactic/c (promise/c tactic/c))
                                (or/c #f srcloc? syntax?)))
         tactic/c)
    (define tac (car tac/loc))
    (define loc (cdr tac/loc))
    (define old-st (get-proof-state hole))
    (define st (if loc (proof-state-with-loc old-st loc) old-st))
    (cond
      [(pair? tacs-and-locs)
       ((force tac) hole (lambda (state)
                           (hole-with-tactic
                            state
                            (lambda (h m-h)
                              ((apply then* tacs-and-locs) h make-hole)))))]
      [else
       ((force tac) (syntax-property hole 'proof-state st) make-hole)]))

  
  (define-syntax (then stx)
    (syntax-case stx ()
       [(_ tac ...)
        (let ([tactics/loc (for/list ([t (syntax->list #'(tac ...))])
                             (quasisyntax/loc t
                               (cons #,t #'#,t)))])
          (quasisyntax/loc stx
            (then* #,@tactics/loc)))]))
  
  (define/contract ((log message) hole make-hole)
    (-> any/c tactic/c)
    (println message)
    (copy-goal hole (make-hole)))

  ;; Emit a particular piece of syntax.
  (define/contract ((emit out-stx) hole make-hole)
    (-> syntax? tactic/c)
    out-stx)

  (define/contract ((fail message) hole make-hole)
    (-> string? tactic/c)
    (define st (get-proof-state hole))
    (define h (proof-state-handler st))
    (define loc (proof-state-loc st))
    (h (make-exn:fail:tactics message (current-continuation-marks) hole loc)))

  ;; Transform a make-hole procedure to first replace the current handler. This is used to cut off
  ;; part of the proof tree at the end of a try.
  (define (set-handler h make-hole)
    (lambda (st)
      (define new-st (match st
                       [(proof-state tac loc _) (proof-state tac loc h)]))
      (make-hole st)))
  
  ;; Attempt to continue with tac, using alts in order if it fails. First, the proof script is
  ;; parameterized by the handler, but its continuation is then set up to de-install the handler.
  ;; Because we must manually manage the dynamic extent of handlers, this is not done with normal
  ;; exceptions, but instead with let/ec.
  (define/contract ((try tac . alts) hole make-hole)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c))) tactic/c)
    (cond
      [(pair? alts)
       (define st (get-proof-state hole))
       (define h (proof-state-handler st))
       (let ([res (let/ec k
                    (define st/k (proof-state-with-handler st k))
                    (local-expand ((force tac)
                                   (syntax-property hole 'proof-state st/k)
                                   (set-handler h make-hole))
                                  'expression
                                  null))])
         (if (exn:fail? res)
             ((apply try alts) hole make-hole)
             res))]
      [else
       ((force tac) hole make-hole)])))

(define-syntax (run-script stx)
  (syntax-case stx ()
    [(_ tacs ...)
     #`(let ()
         (define-syntax (go s)
           (hole-with-tactic (proof-state-with-loc
                              basic-proof-state
                              #'#,stx)
                             (then tacs ...)))
         (go))]))


(module+ test
  (define-for-syntax (repeat t)
    (then t
           (try (delay (repeat t))
                skip)))

  (define-for-syntax (plus hole make-hole)
    (define st (get-proof-state hole))
    (define h1 (make-hole st))
    (define h2 (make-hole st))
    #`(+ #,h1 #,h2))

  (define seven
    (run-script (emit #'7)))
  (check-equal? seven 7)

  (define four
    (run-script plus
                (emit #'2)))
  (check-equal? four 4)

  (define eight
    (run-script plus plus (emit #'2)))
  (check-equal? eight 8)

  (define three
    (run-script (then-l plus
                        ((emit #'2) (emit #'1)))))
  (check-equal? three 3)

  (define six
    (run-script (then-l plus
                        ((emit #'1) plus)
                        ((emit #'2) (emit #'3)))))
  (check-equal? six 6)

  (define another-four
    (run-script plus
                (try (fail "no way")
                     (fail "urgh")
                     (emit #'2)
                     (fail "nope"))))
  (check-equal? another-four 4)

  (define another-three
    (run-script (then-l plus
                        ((emit #'2))
                        ((emit #'1)))))

  (define-for-syntax counter 0)
  (define-for-syntax (at-most-two-plus hole new-hole)
    (if (> counter 1)
        ((fail "no more plus") hole new-hole)
        (begin (set! counter (+ counter 1))
               (plus hole new-hole))))
  
  (define foo
    (run-script (then plus
                      (then plus plus )
                      plus plus
                      (repeat (emit #'1)))))
  (check-equal? foo 32)

  
  (define bar (run-script (then (repeat at-most-two-plus)
                                (repeat (emit #'1)))))
  (check-equal? bar 3) ;; (+ (+ 1 1) 1)
)


;; Local Variables:
;; eval: (put (quote generator) (quote racket-indent-function) 1)
;; End:
