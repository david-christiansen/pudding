#lang racket
(require (for-syntax racket/generator racket/contract racket/sequence racket/promise racket/match
                     
                     (for-syntax racket/base))
         racket/stxparam)

(provide
 (for-syntax skip fail try then then-l emit tactic/c hole-with-tactic log
             current-tactic-location no-more-tactics-hook tactic-info-hook
             )
 tactic-debug? tactic-debug-hook
 run-script)

(module+ test
  (require rackunit))

(define-syntax-parameter tactic-debug? #f)
(define-syntax-parameter tactic-debug-hook
  (lambda (hole-stx)
    (printf "Hole ID: ~a\n" (get-id hole-stx))))

(begin-for-syntax
  (define tactic-info-hook
    (make-parameter
     (lambda (h) #f)))
  (define no-more-tactics-hook
    (make-parameter
     (lambda (hole-stx)
       (raise-syntax-error 'no-more-tactics "No more tactics" (current-tactic-location))))))



(begin-for-syntax
  
  (define current-tactic-location (make-parameter #f))
  (define current-tactic-handler (make-parameter (lambda (e) (raise e))))
  
  ;; Keys are used to look up the tactic for a hole. They are used
  ;; only as unique identifiers --- the fact that the struct is not
  ;; transparent means that equality is pointer equality, and
  ;; allocation is used like gensym here.
  ;;
  ;; Each hole will get a unique key.
  (struct key ())
  (define (fresh-key) (key))

  ;; The state of the tactic engine is a mapping from hole keys to
  ;; the tactic to run in that hole.
  (struct tactic-state (hole-tactics) #:transparent))

(define-for-syntax (new-state)
  (tactic-state (make-weak-hasheq)))

(define-for-syntax the-state (new-state))

(define-for-syntax (leftmost v)
  (if (pair? v)
      (leftmost (car v))
      v))

;; Get the unique identifier for a hole. Due to syntax property
;; merging (which can occur if a tactic has no effect but continues
;; with a new tactic), this may be a cons tree. If so, the leftmost
;; leaf is what we want.
(define-for-syntax (get-id hole-stx)
  (leftmost (syntax-property hole-stx 'hole-id)))

(define-for-syntax (set-id hole-stx id)
  (syntax-property hole-stx 'hole-id id))

;; Get the tactic to run in a hole, using its key.
(define-for-syntax (get-hole-tactic hole-stx)
  (define id (get-id hole-stx))
  (define tactics (tactic-state-hole-tactics the-state))
  (define tac (hash-ref tactics id))
  (hash-remove! tactics id)
  tac)

(define-for-syntax (hole? stx)
  (and (identifier? stx)
       (free-identifier=? stx #'hole)
       (get-id stx)))

;; A tactic is a procedure that takes the hole on which it is invoked
;; and a "continuation" procedure that returns tactics for any
;; subgoals. It returns the output syntax, potentially containing new
;; holes.
(define-for-syntax tactic/c
  (-> syntax? (-> hole?) syntax?))

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

;; The hole macro runs the tactic that is associated with its key in
;; the state.
(define-syntax (hole stx)
  (define-logger online-check-syntax)
  (define tac (get-hole-tactic stx))
  (define params (leftmost (syntax-property stx 'params)))
  (when (syntax-parameter-value #'tactic-debug?)
    ((syntax-parameter-value #'tactic-debug-hook) stx))
  (call-with-parameterization params
                              (lambda ()
                                (tac stx no-more-tactics))))

;; Create a syntax object that is a hole, and will run the provided tactic.
(begin-for-syntax
  (define/contract (hole-with-tactic tac)
    (-> tactic/c syntax?)
    (define id (fresh-key))
    (hash-set! (tactic-state-hole-tactics the-state) id tac)
    (syntax-property (set-id #'hole id) 'params (current-parameterization)))

  ;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
  (define (no-more-tactics)
    (hole-with-tactic (lambda (h n-t) ((no-more-tactics-hook) h))))
  
  ;; A tactic that does nothing.
  (define/contract (skip hole make-hole)
    tactic/c
    (copy-goal hole (make-hole)))

  (define/contract ((then-l* tac/loc . tacs) hole make-hole)
    (->* ((cons/c (or/c tactic/c (promise/c tactic/c))
                  (or/c #f srcloc? syntax?)))
         #:rest (listof (sequence/c (cons/c (or/c tactic/c (promise/c tactic/c))
                                            (or/c #f syntax? srcloc?))))
         tactic/c)
    (define tac (car tac/loc))
    (define loc (cdr tac/loc))
    (parameterize ([current-tactic-location (if loc loc (current-tactic-location))])
      (cond
        [(pair? tacs)
         (define inner-next
           (generator ()
                      (for ([tac/loc2 (in-sequences (car tacs)
                                                    (in-cycle (in-value (cons skip #f))))])
                        (yield (hole-with-tactic (lambda (hole-stx m-h)
                                                   ((apply then-l* tac/loc2 (cdr tacs))
                                                    hole-stx
                                                    make-hole)))))))
         ((force tac) hole inner-next)]
        [else
         ((force tac) hole make-hole)])))

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
    (parameterize ([current-tactic-location (if loc loc (current-tactic-location))])
      (cond
        [(pair? tacs-and-locs)
         ((force tac) hole (lambda ()
                             (hole-with-tactic
                              (lambda (h m-h)
                                ((apply then* tacs-and-locs) h make-hole)))))]
        [else
         ((force tac) hole make-hole)])))

  
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


  ;; Error handling works as follows:
  ;; The parameter current-tactic-handler contains the exception handler to run. If in the apparent
  ;; dynamic extent of a try operator, this handler will be an escape continuation. If not, it will
  ;; raise a normal Racket exception.
  ;;
  ;; This is needed because of the way continuations are chained: technically, the entire rest of the
  ;; tactic program is in the dynamic extent of the try, so we need to manually be able to cut off the
  ;; portion of the tree that corresponds to the try operator itself. That is, we must de-install the
  ;; handler at the end of the try.
  ;;
  ;; fail simply calls the current handler.
  (define/contract ((fail message) hole make-hole)
    (-> string? tactic/c)
    ((current-tactic-handler)
     (make-exn:fail:tactics message (current-continuation-marks) hole (current-tactic-location))))

  ;; Transform a make-hole procedure to first replace the current handler. This is used to cut off
  ;; part of the proof tree at the end of a try.
  (define (set-handler h make-hole)
    (lambda ()
      (parameterize ([current-tactic-handler h])
        (make-hole))))
  
  ;; Attempt to continue with tac, using alts in order if it fails. First, the proof script is
  ;; parameterized by the handler, but its continuation is then set up to de-install the handler.
  ;; Because we must manually manage the dynamic extent of handlers, this is not done with normal
  ;; exceptions, but instead with let/ec.
  (define/contract ((try tac . alts) hole make-hole)
    (->* ((or/c tactic/c (promise/c tactic/c)))
         #:rest (listof (or/c tactic/c (promise/c tactic/c))) tactic/c)
    (cond
      [(pair? alts)
       (define h (current-tactic-handler))
       (let ([res (let/ec k
                    (parameterize ([current-tactic-handler k])
                      (local-expand ((force tac) hole (set-handler h make-hole))
                                    'expression
                                    null)))])
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
           (parameterize ([current-tactic-location #'#,stx])
             (hole-with-tactic (then tacs ...))))
         (go))]))


(module+ test
  (define-for-syntax (repeat t)
    (then t
           (try (delay (repeat t))
                skip)))

  (define-for-syntax (plus hole make-hole)
    (define h1 (make-hole))
    (define h2 (make-hole))
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
