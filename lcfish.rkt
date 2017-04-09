#lang racket/base
(require (for-syntax racket/base racket/generator racket/contract racket/sequence racket/promise racket/match
                     racket/function
                     (for-syntax racket/base))
         racket/stxparam
         (for-syntax "engine/proof-state.rkt")
         (for-syntax "seal.rkt")
         (for-syntax "engine/refinement.rkt")
         "engine/hole.rkt")

#;(provide
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




(begin-for-syntax

  (define/contract (in-all t)
    (-> tactic/c multitactic/c)
    (multitactic (lambda (i) t)))

  ;; Sequence two multitactics
  (define/contract (multi-then m1 m2)
    (-> multitactic/c multitactic/c multitactic/c)
    (multitactic (procedure-rename
                  (lambda (i)
                    (displayln `((multi-then ,m1 ,m2) ,i))
                    (tactic (procedure-rename
                             (lambda (hole-stx ks)
                               ((m1 i) hole-stx (multi-then m2 ks)))
                             (string->symbol (format "inner-multi-then-[~a,~a]" (object-name m1) (object-name m2))))))
                  (string->symbol (format "multi-then-[~a,~a]" (object-name m1) (object-name m2))))))

  ;; Run a multitactic after a tactic
  (define/contract (seq t mt)
    (-> tactic/c multitactic/c tactic/c)
    (tactic (lambda (hole-stx next)
              (displayln `(seq ,t ,mt))
              (t hole-stx (multi-then mt next)))))

  ;; Create a syntax object that is a hole, and will run the provided tactic.
  (define/contract (subgoal-with-tactic old-hole new-goal tac)
    (-> hole? any/c tactic/c syntax?)
    (printf "putting ~a in hole\n" tac)
    (set-goal (set-tactic old-hole tac) new-goal))

  ;; A multitactic that does nothing.
  (define/contract skip
    multitactic/c
    (multitactic (lambda (i)
                   (displayln `(skippping ,i))
                   (tactic (lambda (hole make-subgoal)
                             ((make-subgoal i) hole make-subgoal)
                             #;
                             (((get-skip-tac hole) i) hole make-subgoal))))))


  (define/contract (make-skip seal)
    (-> (-> any/c sealed?) multitactic/c)
    (multitactic
     (lambda (i)
       (tactic (lambda (hole make-subgoal)
                 (call-with-continuation-barrier
                  (thunk
                   (seal (refine hole ((make-subgoal i) hole make-subgoal))))))))))

  (define lazy-tactic/c (or/c tactic/c (promise/c tactic/c)))

  (define/contract (tactic-list->multitactic tacs)
    (-> (listof lazy-tactic/c)
        multitactic/c)
    (multitactic (lambda (i)
                   (if (< i (length tacs))
                       (force (list-ref tacs i))
                       (skip i)))))


  (define/contract (then-l** tac . tacss)
    (->* (lazy-tactic/c)
         #:rest (listof (listof lazy-tactic/c))
         tactic/c)
    (cond [(pair? tacss)
           (tactic (seq (force tac)
                        (tactic-list->multitactic
                         (for/list ([tac* (car tacss)])
                           (apply then-l** tac* (cdr tacss))))))]
          [else (force tac)]))

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
  (define/contract (then* tac . tacs)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c)))
         tactic/c)
    (displayln `(then* ,tac . ,tacs))
    (cond
      [(pair? tacs)
       (displayln `(then*-1))
       (tactic (seq (force tac)
                    (multitactic (lambda (i)
                                   (displayln `(found ,i))
                                   (apply then* (car tacs) (cdr tacs))))))]
      [else
       (displayln `(then*-2 ,tac))
       (force tac)]))

  (define-syntax (then stx)
    (syntax-case stx ()
       [(_ tac ...)
        (with-syntax ([(tacs/locs ...)
                       (for/list ([t (syntax->list #'(tac ...))])
                         (quasisyntax/loc t
                           (tactic/loc #,t #,(quasisyntax/loc t #'#,t))))])
          (quasisyntax/loc stx
            (then* tacs/locs ...)))]))

  (define/contract (log message)
    (-> any/c multitactic/c)
    (multitactic (lambda (i)
                   (tactic (lambda (hole make-hole)
                             (println message)
                             ((skip i) hole make-hole))))))

  ;; Emit a particular piece of syntax.
  (define/contract (emit out-stx)
    (-> syntax? tactic/c)
    (tactic (lambda (hole make-subgoal)
              (displayln `(emitting ,out-stx))
              (seal-lcfish-test (refine hole out-stx)))))

  (define/contract (fail message . args)
    (->* (string?) () #:rest (listof any/c) tactic/c)
    (tactic (lambda (hole make-subgoal)
              (define h (get-hole-handler hole))
              (define loc (get-hole-loc hole))
              (displayln `( failing ,(apply format message args)))
              (h (make-exn:fail:tactics (apply format message args) (current-continuation-marks) hole loc)))))

  ;; Transform a multitactic to first replace the current handler. This is used to cut off
  ;; part of the proof tree at the end of a try.
  (define/contract (use-handler h outer-mt)
    (-> (-> exn:fail:tactics? any) multitactic/c
        multitactic/c)
    (multitactic (procedure-rename (lambda (i)
                                     (tactic (procedure-rename (lambda (hole inner-mt)
                                                                 ((outer-mt i) (set-handler hole h) inner-mt))
                                                               (string->symbol (format "use-handler-t[-~a]" (object-name outer-mt))))))
                                   (let ([n (object-name outer-mt)])
                                     (if n
                                         (string->symbol (format "use-handler-~a" n))
                                         'use-handler)))))

  ;; Attempt to continue with tac, using alts in order if it fails. First, the proof script is
  ;; parameterized by the handler, but its continuation is then set up to de-install the handler.
  ;; Because we must manually manage the dynamic extent of handlers, this is not done with normal
  ;; exceptions, but instead with let/ec.
  (define/contract (try* tac . alts)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c)))
         tactic/c)
    (tactic (lambda (hole make-subgoal)
              (displayln `(try* ,tac . ,alts))
              (cond
                [(pair? alts)
                 (define h (get-hole-handler hole))
                 (let ([res (let/ec k
                              (local-expand-sealed
                               ((force tac)
                                (set-handler hole k)
                                (use-handler h make-subgoal))))])
                   (displayln `(res ,res))
                   (if (exn:fail? res)
                       ((apply try* alts) hole make-subgoal)
                       res))]
                [else
                 ((force tac) hole make-subgoal)])))))

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
  (define (((debug (message "")) i) hole make-hole)
    (displayln `(,message ,(get-hole-loc hole) ,(get-hole-tactic hole) ,(get-hole-goal hole)))
    ((skip i) hole make-hole))

  (define-stamp lcfish-test))

(define-syntax (run-script stx)
  (syntax-case stx ()
    [(_ tac)
     #`(let ()
         (define-syntax (go s)
           (init-hole unseal-lcfish-test
                      (make-skip seal-lcfish-test)
                      tac #f #f))
         (go))]
    [(_ tacs ...)
     #'(run-script (then tacs ...))]))


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
    (then* t
          (try* (delay (repeat t))
                (skip 0))))

  (begin-for-syntax
    (define/contract plus
      tactic/c
      (tactic (lambda (hole k)
                (displayln 'plus)
                (define h1 (subgoal-with-tactic hole #f (k 0)))
                (define h2 (subgoal-with-tactic hole #f (k 1)))
                (displayln `(plus-got-goals ,(k 0) ,(k 1)))
                (seal-lcfish-test (refine hole #`(+ #,h1 #,h2)))))))

  
  (define seven
    (run-script (emit #'7)))
  
  (check-equal? seven 7)
  
  (define four
    (run-script (then* plus (emit #'2))))
  (check-equal? four 4)

  (check-equal?
   (run-script #;(debug "foo")
              (try* (fail "fnord")
                    (skip 0))

              plus

              #;(debug "bar")
              (emit #'22)
              #;(debug "hi"))
   44)

  (define eight
    (run-script plus plus (emit #'2)))
  (check-equal? eight 8)

  (define eight-more
    (run-script (then plus (then plus
                                 (then (emit #'2) (skip 0))))))
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
    (run-script (then (then-l plus
                                ((emit #'2)))
                      (emit #'1))))

  (define foo
    (run-script (then plus
                      (then plus plus)
                      plus plus
                      (emit #'1))))

  (check-equal? foo 32)

  (define-for-syntax counter 0)

  (define-for-syntax at-most-two-plus
    (tactic (procedure-rename (lambda (hole new-hole)
                                (displayln `(at-most-two-plus ,counter))
                                (if (> counter 1)
                                    ((fail "no more plus") hole new-hole)
                                    (begin (set! counter (+ counter 1))
                                           (plus hole new-hole))))
                              'at-most-two-plus-tac)))

  (define bar (run-script (repeat at-most-two-plus) (emit #'1)))
  (check-equal? bar 3)  ;; (+ (+ 1 1) 1)
)


;; Local Variables:
;; eval: (put (quote generator) (quote racket-indent-function) 1)
;; End:
