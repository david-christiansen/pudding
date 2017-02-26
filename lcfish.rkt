#lang racket/base
(require (for-syntax racket/base racket/generator racket/contract racket/sequence racket/promise racket/match
                     
                     (for-syntax racket/base))
         racket/stxparam
         (for-syntax "engine/proof-state.rkt")
         "engine/hole.rkt")

(provide
 (for-syntax skip fail try then then-l emit tactic/c hole-with-tactic log basic-proof-state
             no-more-tactics-hook)
 tactic-debug? tactic-debug-hook
 run-script)

(module+ test
  (require rackunit))

(define-syntax-parameter tactic-debug? #f)
(define-syntax-parameter tactic-debug-hook
  (lambda (hole-stx)
    (printf "Hole state: \n" )))


(begin-for-syntax
  (define (syntax->srcloc stx)
    (srcloc (syntax-source stx)
            (syntax-line stx)
            (syntax-column stx)
            (syntax-position stx)
            (syntax-span stx)))

  ;; Failing tactics should raise an exception for which exn:fail:tactics? is truthy.
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



;; Create a syntax object that is a hole, and will run the provided tactic.
(begin-for-syntax
  (define/contract (hole-with-tactic old-hole tac)
    (-> hole? tactic/c syntax?)
    (set-tactic old-hole tac))


  
  ;; A tactic that does nothing.
  (define/contract (skip hole make-hole)
    tactic/c
    (make-hole hole))

  (define (in-repeat val)
    (in-cycle (in-value val)))
  
  (define/contract ((then-l* tac . tacs) hole make-hole)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (sequence/c (or/c tactic/c (promise/c tactic/c))))
         tactic/c)
    (cond
      [(pair? tacs)
       (define inner-next
         (generator (old-hole)
           (for ([next-tactic
                  (in-sequences (car tacs)
                                (in-repeat (tactic/loc skip #f)))])
             (yield (hole-with-tactic
                     old-hole
                     (lambda (hole-stx m-h)
                       ((apply then-l* next-tactic (cdr tacs))
                        hole-stx
                        make-hole)))))))
       ((force tac) hole inner-next)]
      [else
       ((force tac) hole make-hole)]))

  (define-syntax (then-l stx)
    (syntax-case stx ()
      [(_ tac1 (tac2 ...) ...)
       (let ([tactics/loc
              (for/list ([ts (syntax->list #'((tac2 ...) ...))])
                (quasisyntax/loc ts
                  (list #,@(for/list ([t (syntax->list ts)])
                             (quasisyntax/loc t
                               (tactic/loc #,t #'#,t))))))])
       (quasisyntax/loc stx
         (then-l* (tactic/loc tac1 #'tac1)
                  #,@tactics/loc)))]))

  ;; If tacs is empty, just run tac. Otherwise, run tac, with
  ;; (then . tacs) running in each subgoal.
  (define/contract ((then* tac . tacs) hole make-hole)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c)))
         tactic/c)
    (cond
      [(pair? tacs)
       ((force tac) hole (lambda (state)
                           (hole-with-tactic
                            state
                            (lambda (h m-h)
                              ((apply then* tacs) h make-hole)))))]
      [else
       ((force tac) hole make-hole)]))

  
  (define-syntax (then stx)
    (syntax-case stx ()
       [(_ tac ...)
        (let ([tactics/loc (for/list ([t (syntax->list #'(tac ...))])
                             (quasisyntax/loc t
                               (tactic/loc #,t #'#,t)))])
          (quasisyntax/loc stx
            (then* #,@tactics/loc)))]))
  
  (define/contract ((log message) hole make-hole)
    (-> any/c tactic/c)
    (println message)
    (make-hole hole))

  ;; Emit a particular piece of syntax.
  (define/contract ((emit out-stx) hole make-hole)
    (-> syntax? tactic/c)
    out-stx)

  (define/contract ((fail message) hole make-hole)
    (-> string? tactic/c)
    (define h (get-hole-handler hole))
    (define loc (get-hole-loc hole))
    (h (make-exn:fail:tactics message (current-continuation-marks) hole loc)))

  ;; Transform a make-hole procedure to first replace the current handler. This is used to cut off
  ;; part of the proof tree at the end of a try.
  (define (use-handler h make-hole)
    (lambda (old-hole)
      (set-handler (make-hole old-hole) h)))
  
  ;; Attempt to continue with tac, using alts in order if it fails. First, the proof script is
  ;; parameterized by the handler, but its continuation is then set up to de-install the handler.
  ;; Because we must manually manage the dynamic extent of handlers, this is not done with normal
  ;; exceptions, but instead with let/ec.
  (define/contract ((try tac . alts) hole make-hole)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c))) tactic/c)
    (cond
      [(pair? alts)
       (define h (get-hole-handler hole))
       (let ([res (let/ec k
                    (local-expand ((force tac)
                                   (set-handler hole k)
                                   (use-handler h make-hole))
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
           (set-tactic basic-hole (then tacs ...)))
         (go))]))


(module+ test
  (define-for-syntax (repeat t)
    (then t
           (try (delay (repeat t))
                skip)))

  (define-for-syntax (plus hole make-hole)
    (define h1 (make-hole hole))
    (define h2 (make-hole hole))
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
