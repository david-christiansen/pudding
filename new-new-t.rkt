#lang racket
(require (for-syntax racket/generator racket/contract racket/sequence))

(module+ test
  (require rackunit))

(begin-for-syntax
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

;; Failing tactics should raise an exception for which exn:fail:tactics? is truthy.
(begin-for-syntax
  (struct exn:fail:tactics exn:fail (hole) #:extra-constructor-name make-exn:fail:tactics))

;; A "next tactic" procedure that doesn't work. Used at the end of scripts.
(define-for-syntax (failures)
  (raise (make-exn:fail:tactics "No more tactics." (current-continuation-marks) #f)))

;; The hole macro runs the tactic that is associated with its key in
;; the state.
(define-syntax (hole stx)
  (define tac (get-hole-tactic stx))
  (tac stx failures))

;; Create a syntax object that is a hole, and will run the provided tactic.
(begin-for-syntax
  (define/contract (hole-with-tactic tac)
    (-> tactic/c syntax?)
    (define id (fresh-key))
    (hash-set! (tactic-state-hole-tactics the-state) id tac)
    (set-id #'hole id))

  ;; A tactic that does nothing.
  (define/contract (skip hole make-hole)
    tactic/c
    (make-hole))

  ;; If tacs is empty, just run tac. Otherwise, run tac, with
  ;; (then . tacs) running in each subgoal.
  (define/contract ((then tac . tacs) hole make-hole)
    (->* (tactic/c) #:rest (listof tactic/c) tactic/c)
    (cond
      [(pair? tacs)
       (define (inner-next)
         (hole-with-tactic (apply then tacs)))
       (tac hole inner-next)]
      [else
       (tac hole make-hole)]))

  (define/contract ((then-l tac . tacs) hole make-hole)
    (->* (tactic/c) #:rest (listof (sequence/c tactic/c)) tactic/c)
    (cond
      [(pair? tacs)
       (define inner-next
         (generator ()
           (for ([t2 (in-sequences (car tacs)
                                   (in-cycle (in-value skip)))])
             (yield (hole-with-tactic (apply then-l t2 (cdr tacs)))))))
       (tac hole inner-next)]
      [else
       (tac hole make-hole)]))

  ;; Emit a particular piece of syntax.
  (define/contract ((emit out-stx) hole make-hole)
    (-> syntax? tactic/c)
    out-stx)

  (define/contract ((fail message) hole make-hole)
    (-> string? tactic/c)
    (raise (make-exn:fail:tactics message (current-continuation-marks) hole)))

  ;; Attempt to continue with tac, using alts in order if it fails.
  (define/contract ((try tac . alts) hole make-hole)
    (->* (tactic/c) #:rest (listof tactic/c) tactic/c)
    (cond
      [(pair? alts)
       (with-handlers ([exn:fail:tactics? (lambda (e)
                                            ((apply try alts) hole make-hole))])
         (tac hole make-hole))]
      [else
       (tac hole make-hole)])))


(define-syntax (run-script stx)
  (syntax-case stx ()
    [(_ . tacs)
     #'(let ()
         (define-syntax (go s)
           (hole-with-tactic (then . tacs)))
         (go))]))

(module+ test
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
                        (list (emit #'2)
                              (emit #'1)))))
  (check-equal? three 3)

  (define six
    (run-script (then-l plus
                        (list (emit #'1)
                              plus)
                        (list (emit #'2)
                              (emit #'3)))))
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
                        (list (emit #'2))
                        (list (emit #'1))))))


;; Local Variables:
;; eval: (put (quote generator) (quote racket-indent-function) 1)
;; End:
