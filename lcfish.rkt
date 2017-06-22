#lang racket/base
(require (for-syntax racket/base racket/generator racket/contract racket/sequence racket/promise racket/match
                     racket/function
                     (for-syntax racket/base))
         racket/stxparam
         (for-syntax "engine/proof-state.rkt")
         (for-syntax "seal.rkt")
         (for-syntax "rewindable-streams.rkt")
         (for-syntax "engine/refinement.rkt")
         "engine/hole.rkt")

(provide
 (for-syntax skip fail try try* then then* then-l then-l* tactic/c subgoal-with-tactic basic-proof-state
             no-more-tactics-hook make-skip debug
             with-goal match-goal match-goal*)
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
  (define/contract (subgoal-with-tactic old-hole new-goal tac)
    (-> hole? any/c tactic/c syntax?)
    (set-goal (set-tactic old-hole tac) new-goal))

  ;; A tactic that does nothing.
  (define/contract (skip hole make-subgoal)
    tactic/c
    ((get-skip-tac hole) hole make-subgoal))

  (define/contract ((make-skip seal) hole make-subgoal)
    (-> (-> any/c any/c sealed?) tactic/c)
    (call-with-continuation-barrier
     (thunk
      (seal (get-hole-goal hole)
            (refine hole (make-subgoal hole (get-hole-goal hole)))))))

  (define (in-forever val)
    (in-cycle (in-value val)))

  (define/contract ((then-l** tac . tacs) hole make-subgoal)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (sequence/c (or/c tactic/c (promise/c tactic/c))))
         tactic/c)
    (cond
      [(pair? tacs)
       (define (hole-with tac)
         (lambda (old-hole new-goal)
           (subgoal-with-tactic
            old-hole
            new-goal
            (lambda (hole-stx _)
              ((apply then-l** tac (cdr tacs))
               hole-stx
               make-subgoal)))))
       (define inners
         (list->rstream (map hole-with (car tacs)) (hole-with skip)))
       (define inner-next
         (lambda (old-hole new-goal)
           ((rstream-next inners) old-hole new-goal)))
       ((force tac) hole inner-next)]
      [else
       ((force tac) hole make-subgoal)]))

  (define-syntax (then-l* stx)
    (syntax-case stx ()
      [(_ tac1 (tac2 ...) ...)
       (syntax/loc stx
         (then-l** tac1 (list tac2 ...) ...))]))

  (define-syntax (then-l stx)
    (syntax-case stx ()
      [(_ tac1 (tac2 ...) ...)
       (let ([tactics/loc
              (for/list ([ts (syntax->list #'((tac2 ...) ...))])
                (quasisyntax/loc ts
                  (list #,@(for/list ([t (syntax->list ts)])
                             (quasisyntax/loc t
                               (tactic/loc #,t #,(quasisyntax/loc t #'#,t)))))))])
         (quasisyntax/loc stx
           (then-l** (tactic/loc tac1 #,(quasisyntax/loc #'tac1 #'#,#'tac1))
                     #,@tactics/loc)))]))

  ;; If tacs is empty, just run tac. Otherwise, run tac, with
  ;; (then . tacs) running in each subgoal.
  (define/contract ((then* tac . tacs) hole make-subgoal)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c)))
         tactic/c)
    (cond
      [(pair? tacs)
       ((force tac)
        hole
        (lambda (old-hole new-goal)
          (subgoal-with-tactic
           old-hole
           new-goal
           (procedure-rename
            (lambda (hole m-s)
              ((apply then* tacs)
               hole
               make-subgoal))
            (string->symbol (format "~a" tacs))))))]
      [else
       ((force tac) hole make-subgoal)]))


  (define-syntax (then stx)
    (syntax-case stx ()
      [(_ tac ...)
       (with-syntax ([(tacs/locs ...)
                      (for/list ([t (syntax->list #'(tac ...))])
                        (quasisyntax/loc t
                          (tactic/loc #,t #,(quasisyntax/loc t #'#,t))))])
         (quasisyntax/loc stx
           (then* tacs/locs ...)))]))

  (define/contract ((log message) hole make-hole)
    (-> any/c tactic/c)
    (println message)
    (skip hole make-hole))

  ;; Emit a particular piece of syntax.
  (define/contract ((emit out-stx) hole make-subgoal)
    (-> syntax? tactic/c)
    #;(displayln `(emitting ,out-stx))
    (seal-lcfish-test (get-hole-goal hole) (refine hole out-stx)))

  (define/contract ((fail message . args) hole make-subgoal)
    (->* (string?) () #:rest (listof any/c) tactic/c)
    (define h (get-hole-handler hole))
    (define loc (get-hole-loc hole))
    (h (make-exn:fail:tactics (apply format message args) (current-continuation-marks) hole loc)))

  ;; Transform a make-hole procedure to first replace the current handler. This is used to cut off
  ;; part of the proof tree at the end of a try.
  (define (use-handler h make-subgoal)
    (lambda (old-hole new-goal)
      (set-handler (make-subgoal old-hole new-goal) h)))

  ;; Attempt to continue with tac, using alts in order if it fails. First, the proof script is
  ;; parameterized by the handler, but its continuation is then set up to de-install the handler.
  ;; Because we must manually manage the dynamic extent of handlers, this is not done with normal
  ;; exceptions, but instead with let/ec.
  (define/contract ((try* tac . alts) hole make-subgoal)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c))) tactic/c)
    (cond
      [(pair? alts)
       (define h (get-hole-handler hole))
       (define stream-state (rstream-snapshot))
       (let ([res (let/ec k
                    (local-expand-sealed
                     ((force tac)
                      (set-handler hole k)
                      (use-handler h make-subgoal))))])
         (if (exn:fail? res)
             (begin (rstream-rewind! stream-state)
                    ((apply try* alts) hole make-subgoal))
             res))]
      [else
       ((force tac) hole make-subgoal)])))

(begin-for-syntax
  (define-syntax (try stx)
    (syntax-case stx ()
      [(_ tac ...)
       (with-syntax ([(tacs/locs ...)
                      (for/list ([t (syntax->list #'(tac ...))])
                        (quasisyntax/loc t
                          (tactic/loc #,t
                                      #,(quasisyntax/loc t #'#,t))))])
       (quasisyntax/loc stx
         (try* tacs/locs ...)))])))

(begin-for-syntax
  (define/contract ((call-with-goal tac) hole make-subgoal)
    (-> (-> any/c (or/c tactic/c (promise/c tactic/c)))
        tactic/c)
    ((tac (get-hole-goal hole)) hole make-subgoal))

  (define-syntax (with-goal stx)
    (syntax-case stx ()
      [(_ g e ...)
       (syntax/loc stx
         (call-with-goal
          (lambda (g)
            e ...)))]))

  (define-syntax (match-goal* stx)
    (syntax-case stx ()
      [(_ (pat #:when w body ...) ...)
       (quasisyntax/loc stx
         (with-goal g
           (match g
             (pat #:when w (then* body ...))
             ...
             (_ (fail "No pattern matched goal")))))]
      [(_ (pat body ...) ...)
       (syntax/loc stx
         (match-goal* (pat #:when #t body ...) ...))]))

  (define-syntax (match-goal stx)
    (syntax-case stx ()
      [(_ (pat #:when w body ...) ...)
       (quasisyntax/loc stx
         (with-goal g
           (match g
             (pat #:when w (then body ...))
             ...
             (_ (fail "No pattern matched goal")))))]
      [(_ (pat body ...) ...)
       (syntax/loc stx
         (match-goal (pat #:when #t body ...) ...))])))

(begin-for-syntax
  (define ((debug (message "")) hole make-hole)
    (displayln `(,message ,(get-hole-loc hole) ,(get-hole-tactic hole) ,(get-hole-goal hole)))
    (skip hole make-hole))

  (define-stamp lcfish-test))

(define-syntax (run-script stx)
  (syntax-case stx ()
    [(_ tacs ...)
     #`(let ()
         (define-syntax (go s)
           (init-hole unseal-lcfish-test
                      (make-skip seal-lcfish-test)
                      (then tacs ...) #f #f))
         (go))]))


(module+ test
  (require "engine/hole.rkt" )
  (require "tooltip-info.rkt")
  (begin-for-syntax
    (define tooltip-counter (box 0))
    (tactic-info-hook
     (tooltip-info
      (lambda (_)
        (set-box! tooltip-counter (+ 1 (unbox tooltip-counter)))
        (format "this is a tooltip! (~a)" (unbox tooltip-counter))))))

  (define-for-syntax (repeat t)
    (then t
          (try (delay (repeat t))
               skip)))

  (define-for-syntax (plus hole make-subgoal)
    (define h1 (make-subgoal hole #f))
    (define h2 (make-subgoal hole #f))
    (seal-lcfish-test (get-hole-goal hole)
                      (refine hole #`(+ #,h1 #,h2))))



  (check-equal?
   (run-script #;(debug "foo")
              (try (fail "fnord")
                   skip)

              plus

              #;(debug "bar")
              (emit #'22)
              #;(debug "hi"))
   44)

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

  (define eight-more
    (run-script (then plus (then plus
                                 (then (emit #'2) skip)))))
  (check-equal? eight-more 8)

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
    (run-script (try (fail "hmm")
                     plus)
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
                      (then plus plus)
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
