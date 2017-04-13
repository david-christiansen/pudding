#lang racket/base
(require (for-syntax racket/base racket/generator racket/contract racket/sequence racket/promise racket/match
                     racket/function
                     (for-syntax syntax/parse)
                     (for-syntax racket/base))
         racket/stxparam
         (for-syntax "engine/proof-state.rkt")
         (for-syntax "seal.rkt")
         
         (for-syntax "engine/machine.rkt")
         "engine/hole.rkt")

(provide
 
 (for-syntax skip fail try #;try* then #;then* then-l #;then-l* tactic/c #;subgoal-with-tactic basic-proof-state
             no-more-tactics-hook  #;debug
             #;with-goal #;match-goal #;match-goal*)
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
  #;
  (define/contract (subgoal-with-tactic old-hole new-goal tac)
    (-> hole? any/c tactic/c syntax?)
    (set-goal (set-tactic old-hole tac) new-goal))


  
  ;; A tactic that does nothing.
  (define skip
    (ID))

  (define-syntax (then-l stx)
    (with-syntax ([the-stx stx])
      (syntax-parse stx
        [(thl t (ts ...)) #'(LOC #'the-stx (THENL (LOC #'t t) (list (LOC #'ts ts) ...)))]
        [(thl t (ts ...) (ts2 ...) ...) #'(then-l (THENL (LOC #'t t) (list (LOC #'ts ts) ...)) (ts2 ...) ...)])))

  (define-syntax (then stx)
    (quasisyntax/loc stx
      (LOC
       #'#,stx
       #,(syntax-parse stx
           [(_ tac) #`(LOC #'tac tac)]
           [(_ tac1 tac2) #`(THEN (LOC #'tac1 tac1) (LOC #'tac2 tac2))]
           [(_ tac1 tac2 tac ...) #'(THEN (LOC #'tac1 tac1) (then tac2 tac ...))]))))

  ;; Emit a particular piece of syntax.
  (define (emit out-stx)
    #;(displayln `(emitting ,out-stx))
    (TACTIC (lambda (hole k fk) (seal-lcfish-test (get-hole-goal hole) out-stx))))

  (define-syntax (fail stx)
    (with-syntax ([the-stx stx])
      (syntax-parse stx
        [(f message arg ...)
         #'(LOC #'the-stx (FAIL (format message arg ...)))]))))

(begin-for-syntax
  (define-syntax (try stx)
    (with-syntax ([the-stx stx])
      (syntax-parse stx
        [(_ t) #'(LOC #'t t)]
        [(_ t1 t2) #'(LOC #'the-stx (ORELSE (LOC #'t1 t1) (LOC #'t2 t2)))]
        [(_ t1 t2 t3 ...)
         #'(LOC #'the-stx (ORELSE (LOC #'t1 t1) (try t2 t3 ...)))]))))

(begin-for-syntax
  #;
  (define/contract ((call-with-goal tac) hole make-subgoal)
    (-> (-> any/c (or/c tactic/c (promise/c tactic/c)))
        tactic/c)
    ((tac (get-hole-goal hole)) hole make-subgoal))
  #;
  (define-syntax (with-goal stx)
    (syntax-case stx ()
      [(_ g e ...)
       (syntax/loc stx
         (call-with-goal
          (lambda (g)
            e ...)))]))
  #;
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
  #;
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
  #;
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
                      (then tacs ...)
                      #f
                      #f))
         (go))]))


(module+ test
  (require "engine/hole.rkt" )
  (require "tooltip-info.rkt")
  (begin-for-syntax
    (define tooltip-counter (box 0))
    (tactic-info-hook
     (tooltip-info
      (lambda (goal)
        (set-box! tooltip-counter (+ 1 (unbox tooltip-counter)))
        (format "this is a tooltip! (~a)" (unbox tooltip-counter))))))
  
  (define-for-syntax (repeat t)
    (lambda ()
      (then t
            (try (repeat t)
                 skip))))

  (begin-for-syntax
    (define/contract plus
      tactic/c
      (TACTIC (lambda (hole-stx make-subgoal fk)
                (define h1 (make-subgoal 0 hole-stx #f))
                (define h2 (make-subgoal 1 hole-stx #f))
                (seal-lcfish-test (get-hole-goal hole-stx) #`(+ #,h1 #,h2))))))

  

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
  (check-equal? another-three 3)

  (define-for-syntax counter 0)

  (define-for-syntax (at-most-two-plus)
    (if (> counter 1)
        (fail "no more plus")
        (begin (set! counter (+ counter 1))
               plus)))
  

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
