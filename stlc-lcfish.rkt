#lang racket

(require (except-in "lcfish.rkt" run-script)
         (for-syntax racket/contract racket/match racket/promise syntax/parse racket/port syntax/srcloc)
         racket/stxparam
         (for-template racket/base))

(module+ test (require rackunit syntax/macro-testing))

(begin-for-syntax
  (struct ⊢ (hyps goal) #:transparent))

(define-syntax (define-type stx)
  (syntax-case stx ()
    [(_ id)
     #'(define-syntax (id stx) (raise-syntax-error 'id "Not available for programs" stx))]))

(define-type Int)
(define-type String)
(define-type →)


(define-for-syntax (type=? t1 t2)
  (syntax-case t1 (Int String →)
    [Int (and (identifier? t2)
              (free-identifier=? t2 #'Int))]
    [String (and (identifier? t2)
                 (free-identifier=? t2 #'String))]
    [(→ a c)
     (syntax-case t2 (→)
       [(→ b d)
        (and (type=? #'a #'b)
             (type=? #'c #'d))]
       [_ #f])]
    [_ #f]))

(define-for-syntax (type->contract t)
  (syntax-case t (→ Int String)
    [Int #'integer?]
    [String #'string?]
    [(→ a b)
     #`(-> #,(type->contract #'a) #,(type->contract #'b))]
    [_ (error 'bad-type)]))


;; For trampolining through the macro expander to get the right scopes.
;; Communicates with make-assumption-hole and →-intro.
(define-syntax (assumption-hole stx)
  (match-define (⊢ H G) (get-goal stx))
  (define next-hole (syntax-property stx 'next-hole))
  (define params (syntax-property stx 'params))
  (syntax-case stx ()
    [(_ x a)
     (call-with-parameterization
      params
      (lambda ()
        (set-goal (next-hole) (⊢ (cons (list #'x #'a #t) H) G))))]))

(define-for-syntax (make-assumption-hole next-hole x a H G)
  (syntax-property
   (syntax-property
    (set-goal #`(assumption-hole #,x #,a) (⊢ H G))
    'next-hole next-hole)
   'params (current-parameterization)))

(begin-for-syntax
  (define (leftmost v)
    (cond
      [(pair? v) (leftmost (car v))]
      [else v]))

  (define (get-goal stx)
    (leftmost (syntax-property stx 'goal)))

  (define (set-goal stx goal)
    (syntax-property stx 'goal goal))

  (define (dump-goal stx)
    (match-define (⊢ H G) (get-goal stx))
    (for/list ([h (reverse H)]
               [i (in-range (length H) 0 -1)])
      (match h
        [(list x t safe?)
         (printf "~a. ~a : ~a\n" (sub1 i) (syntax-e x) (syntax->datum t))]))
    (printf "⊢ ~a\n\n" (syntax->datum G)))

  (no-more-tactics-hook (lambda (hole-stx)
                          (define message
                            (with-output-to-string
                                (lambda ()
                                  (printf "Unsolved goal:\n")
                                  (dump-goal hole-stx))))
                          (raise-syntax-error 'run-script
                                              message
                                              (current-tactic-location))))
  (define-logger online-check-syntax)
  (tactic-info-hook
   (lambda (hole-stx)
     (define where (current-tactic-location))
     (define goal (with-output-to-string
                   (lambda ()
                     (dump-goal hole-stx))))
     (log-message online-check-syntax-logger
                  'info
                  goal
                  (list (syntax-property #'(void) 'mouse-over-tooltips
                                         (vector where
                                                 (syntax-position where)
                                                 (+ (syntax-position where)
                                                    (syntax-span where))
                                                 (format "~a:\n~a"
                                                         (syntax->datum where)
                                                         goal)))))))
  
  (define/contract ((guard-goal pred tac) hole make-hole)
    (-> (-> ⊢? any/c) tactic/c tactic/c)
    (match (get-goal hole)
      [#f ((fail "No goal found.") hole make-hole)]
      [g #:when (pred g)
         ((tactic-info-hook) hole)
         (tac hole make-hole)]
      [g ((fail (format "Wrong goal: ~a ⊢ ~a" (⊢-hyps g) (syntax->datum (⊢-goal g)))) hole make-hole)]))

  (define/contract (int-intro i)
    (-> integer? tactic/c)
    (if (integer? i)
        (guard-goal (lambda (g) (type=? (⊢-goal g) #'Int))
                    (emit (datum->syntax #'here i)))
        (fail (format "Not an int: ~a" i))))

  (define/contract (string-intro s)
    (-> string? tactic/c)
    (if (string? s)
        (guard-goal (lambda (g) (type=? (⊢-goal g) #'String))
                    (emit (datum->syntax #'here s)))
        (fail (format "Not a string: ~a" s))))


  (define/contract ((→-intro [x 'x]) hole make-hole)
    (->* () (symbol?) tactic/c)
    ((tactic-info-hook) hole)
    (match-define (⊢ H G) (get-goal hole))
    (syntax-case G (→)
      [(→ a b)
       ((emit #`(lambda (#,x)
                  #,(make-assumption-hole make-hole
                                          (datum->syntax #'here x)
                                          #'a
                                          H
                                          #'b)))
        hole make-hole)]
      [t
       ((fail (format "Not an arrow: ~a" (syntax->datum G))) hole make-hole)]))

  (define/contract ((assumption n) hole make-hole)
    (-> exact-nonnegative-integer? tactic/c)
    ((tactic-info-hook) hole)
    (match-define (⊢ H G) (get-goal hole))
    (if (>= n (length H))
        ((fail "Not enough hypotheses") hole make-hole)
        (match-let ([(list x t safe?) (list-ref H n)])
          (cond [(not (type=? t G))
                 ((fail (format "Wrong goal type. Expected ~a, got ~a" G t))
                  hole make-hole)]
                [safe? ((emit x) hole make-hole)]
                [else
                 (define where #`(srcloc '#,(syntax-source x)
                                         '#,(syntax-line x)
                                         '#,(syntax-column x)
                                         '#,(syntax-position x)
                                         '#,(syntax-span x)))
                 ((emit #`(contract #,(type->contract t)
                                    #,x
                                    #,(string-append "assumption " (symbol->string (syntax-e x)) " in proof")
                                    'neg-blame
                                    '#,x
                                    #,where))
                  hole make-hole)]))))

  (define/contract ((plus n) hole make-hole)
    (-> exact-nonnegative-integer? tactic/c)
    ((tactic-info-hook) hole)
    (match-define (⊢ H G) (get-goal hole))
    (if (not (type=? G #'Int))
        ((fail (format "Type not Int: ~a" G)) hole make-hole)
        ((emit #`(+ #,@(for/list ([h (in-producer make-hole)]
                                  [i (in-range n)])
                         (set-goal h (⊢ H #'Int))))) hole make-hole))))


(begin-for-syntax
  (define-splicing-syntax-class hyps-option
    (pattern (~seq #:hyps [(x:id t:expr) ...])
             #:with hyps #'[(x t) ...])
    (pattern (~seq)
             #:with hyps #'[])))

(define-syntax (run-script stx)
  (syntax-parse stx
    [(run-script hs:hyps-option #:goal g tactic ...)
     (with-syntax ([((x t) ...) #'hs.hyps])
      #`(syntax-parameterize ([tactic-debug-hook #,dump-goal])
          (define-syntax (go s)
            (parameterize ([current-tactic-location #'#,stx])
              (set-goal (hole-with-tactic (then tactic ...))
                        (⊢ (reverse (list (list #'x #'t #f) ...)) #'g))))
          (go)))]))



(module+ test
  (check-equal?
   (run-script #:goal Int
               (int-intro 3))
   3)

  ;; In this example, the x in the hypotheses list is precisely the
  ;; same binding as the x in the lambda. This lets us include tactic
  ;; scripts in ordinary programs, and switch program construction
  ;; modalities without giving up binding.

  (define (f x)
    (run-script #:hyps [(x Int)] #:goal Int
                (then-l (plus 2)
                        ((int-intro 1) (assumption 0)))))
  (for ([i (in-range 0 100)])
    (check-equal? (f i) (add1 i)))

  ;; The assumption was wrapped in a contract matching its type.
  (check-exn exn:fail:contract? (thunk (f "foo")))

  ;; Wrong goal type:
  (define (g x)
    (convert-compile-time-error
     (run-script #:hyps [(x String)] #:goal Int
                 (then-l (plus 2)
                         ((int-intro 1) (assumption 0))))))
  (for ([i (in-range 0 100)])
      (check-exn #rx"Wrong goal type."
             (thunk (g i))))
  
  ;; Identifiers must match:
  (define (h x)
    (convert-compile-time-error
     (run-script #:hyps [(y Int)] #:goal Int
                 (then-l (plus 2)
                         ((int-intro 1) (assumption 0))))))
  (for ([i (in-range 0 100)])
      (check-exn #rx"y: unbound identifier"
                 (thunk (h i))))

  (define twice
    (run-script #:goal (→ Int Int)
                (→-intro 'x)
                (plus 2)
                (assumption 0)))

  (for ([i (in-range 100)])
    (check-equal? (twice i) (* 2 i)))

  (define-for-syntax (repeat t)
    (try (then t
               (delay (repeat t)))
         skip))
  (define add
    (syntax-parameterize ([tactic-debug-hook dump-goal]
                          [tactic-debug? #f])
        (run-script #:goal (→ Int (→ Int Int))
                    ;(repeat (→-intro))
                    (→-intro 'z)
                    (try (repeat (→-intro)) skip)
                    (try (repeat (→-intro))
                         skip)
                   
                    ;(string-intro "hey")
                    (then-l (plus 2)
                            ((assumption 0) (assumption 1))))))
  (for* ([i (in-range 100)]
         [j (in-range 100)])
    (check-equal? ((add i) j) (+ i j))))
