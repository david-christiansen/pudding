#lang racket

(require (except-in "lcfish.rkt" run-script)
         (for-syntax racket/base (for-syntax racket/base))
         "engine/hole.rkt"
         (for-syntax "engine/proof-state.rkt")
         "tooltip-info.rkt"
         "rule.rkt"
         (for-syntax "seal.rkt")
         (for-syntax "stx-utils.rkt"
                     racket/contract racket/match racket/promise syntax/parse racket/port syntax/srcloc)
         racket/stxparam
         (for-template racket/base))

(module+ test
  (require rackunit syntax/macro-testing))

(begin-for-syntax
  (struct ⊢ (hyps goal) #:transparent))

(define-syntax (define-type stx)
  (syntax-case stx ()
    [(_ id)
     #'(define-syntax (id stx)
         (raise-syntax-error 'id "Not available for programs" stx))]))

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

(define-for-syntax ((type-is? t1) t2)
  (type=? t1 t2))

(begin-for-syntax
  (define-match-expander arrow-type
    (lambda (stx)
      (syntax-parse stx
        [(a-t dom cod)
         #'(app (lambda (x)
                  (syntax-case x (→)
                    [(→ a b)
                     (cons a b)]
                    [_ #f]))
                (cons dom cod))]))))

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
  (match-define (⊢ H G) (syntax-property stx 'goal))
  (define old-hole (syntax-property stx 'old-hole))
  (define next-hole (syntax-property stx 'next-hole))
  (syntax-case stx ()
    [(_ x a)
     (next-hole old-hole (⊢ (cons (list #'x #'a #t) H) G)) ]))

(define-for-syntax (make-assumption-hole old-hole next-hole x a H G)
  (syntax-property
   (syntax-property
    (syntax-property
     #`(assumption-hole #,x #,a) 
     'next-hole next-hole)
    'goal (⊢ H G))
   'old-hole old-hole))

(begin-for-syntax
  (define (dump-goal stx)
    (match-define (⊢ H G) (get-hole-goal stx))
    (for/list ([h (reverse H)]
               [i (in-range (length H) 0 -1)])
      (match h
        [(list x t safe?)
         (printf "~a. ~a : ~a\n" (sub1 i) (syntax-e x) (syntax->datum t))]))
    (printf "⊢ ~a\n\n" (syntax->datum G)))

  (no-more-tactics-hook
   (lambda (hole-stx)
     (define message
       (with-output-to-string
           (lambda ()
             (printf "Unsolved goal:\n")
             (dump-goal hole-stx))))
     (raise-syntax-error 'run-script
                         message
                         (get-hole-loc hole-stx))))

  ;; In this file, just throw exceptions instead of accumulating them.
  ;; This is for testing purposes.
  (basic-handler (lambda (exn) (raise exn)))
  
  (tactic-info-hook
   (tooltip-info
    (match-lambda [(⊢ H G)
                   (string-append
                    (apply
                     string-append
                     (reverse
                      (for/list ([h (in-list H)]
                                 [i (in-naturals)])
                        (match-define (list x t hidden?) h)
                        (format "~a. ~a : ~a\n"
                                i
                                (syntax->datum x)
                                (syntax->datum t)))))
                    (format "⊢ ~a" (syntax->datum G)))])))
  
  (define/contract (guard-goal pred tac)
    (-> (-> ⊢? any/c) tactic/c tactic/c)
    (lambda (hole make-hole)
      (match (get-hole-goal hole)
        [#f ((fail "No goal found.") hole make-hole)]
        [g #:when (pred g)
           (tac hole make-hole)]
        [g ((fail (format "Wrong goal: ~a ⊢ ~a" (⊢-hyps g) (syntax->datum (⊢-goal g)))) hole make-hole)])))

  (define/contract (int-intro i)
    (-> integer? tactic/c)
    (rule (⊢ _ (? (type-is? #'Int)))
          #:seal seal-stlc
          (if (integer? i)
              (datum->syntax #'here i)
              (not-applicable "Not an integer: ~a" i))))

  (define/contract (string-intro s)
    (-> string? tactic/c)
    (rule (⊢ _ (? (type-is? #'String)))
          #:seal seal-stlc
          (if (string? s)
              (datum->syntax #'here s)
              (not-applicable "Not a string: ~a" s))))


  (define/contract (→-intro [x 'x])
    (->* () (symbol?) tactic/c)
    #;(rule (⊢ H (arrow-type a b))
          #:seal seal-stlc
          #`(lambda (#,x)
              #,(make-assumption-hole hole
                                      make-hole
                                      (datum->syntax #'here x)
                                      #'a
                                      H
                                      #'b))
          )
    (lambda (hole make-hole)
      (match-define (⊢ H G) (get-hole-goal hole))
      (syntax-case G (→)
        [(→ a b)
         ((emit #`(lambda (#,x)
                    #,(make-assumption-hole hole
                                            make-hole
                                            (datum->syntax #'here x)
                                            #'a
                                            H
                                            #'b)))
          hole make-hole)]
        [t
         ((fail (format "Not an arrow: ~a" (syntax->datum G))) hole make-hole)])))

  (define repeat-string
    (rule (⊢ H G)
          #:seal seal-stlc
          #:when (type=? G #'String)
          (with-syntax ([count (subgoal (⊢ H #'Int))]
                        [str (subgoal (⊢ H #'String))])
          #'(apply string-append
                   (for/list ([n (in-range 0 count)])
                     str)))))
  
  (define/contract (assumption n)
    (-> exact-nonnegative-integer? tactic/c)
    (lambda (hole make-hole)
      (match-define (⊢ H G) (get-hole-goal hole))
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
                    hole make-hole)])))))

  (define/contract (plus n)
    (-> exact-nonnegative-integer? tactic/c)
    (lambda (hole make-subgoal)
      (match-define (⊢ H G) (get-hole-goal hole))
      (if (not (type=? G #'Int))
          ((fail (format "Type not Int: ~a" G)) hole make-subgoal)
          ((emit #`(+ #,@(for/list ([h (in-producer (lambda ()
                                                      (make-subgoal hole (⊢ H #'Int))))]
                                    [i (in-range n)])
                           h)))
           hole make-subgoal))))

  (define/contract strlen
    tactic/c
    (rule (⊢ H (? (type-is? #'Int)))
          #:seal seal-stlc
          (with-syntax ([g (subgoal (⊢ H #'String))])
            #'(string-length g)))))


(begin-for-syntax
  (define-stamp stlc)

  (define ((emit stx) h make-subgoal)
    (seal-stlc (refine h stx)))
  
  (define-splicing-syntax-class hyps-option
    (pattern (~seq #:hyps [(x:id t:expr) ...])
             #:with hyps #'[(x t) ...])
    (pattern (~seq)
             #:with hyps #'[])))

(define-syntax (run-script stx)
  (syntax-parse stx
    [(run-script hs:hyps-option #:goal g tactic ...)
     (with-syntax ([((x t) ...) #'hs.hyps])
       #`(let-syntax ([go (lambda (s)
                            (init-hole
                             unseal-stlc
                             (make-skip seal-stlc)
                             (then tactic ...)
                             (⊢ (reverse (list (list #'x #'t #f) ...)) #'g)
                             #'#,stx))])
           (go)))]))



(module+ test
  
  (check-equal?
   (run-script #:goal Int
               (int-intro 3))
   3)

  (define (id x)
    (run-script #:hyps ((x Int))
                #:goal Int
                (assumption 0)))
  (check-equal? (id 4) 4)
  
  ;; In this example, the x in the hypotheses list is precisely the
  ;; same binding as the x in the lambda. This lets us include tactic
  ;; scripts in ordinary programs, and switch program construction
  ;; modalities without giving up binding.

  (define (f x)
    (run-script #:hyps [(x Int)]
                #:goal Int
                skip
                (then-l (plus 2)
                        [(assumption 0)
                         (int-intro 1)])))
  (for ([i (in-range 0 100)])
    (check-equal? (f i) (add1 i)))

  ;; The assumption was wrapped in a contract matching its type.
  (check-exn exn:fail:contract? (thunk (f "foo")))

  ;; Wrong goal type:
  (define (g x)
    (convert-compile-time-error
     (run-script #:hyps [(x String)] #:goal Int
                 (then-l (plus 2)
                         [(int-intro 1) (assumption 0)]))))
  (for ([i (in-range 0 100)])
    (check-exn #rx"Wrong goal type."
               (thunk (g i))))
  
  ;; Identifiers must match:
  (define (h x)
    (convert-compile-time-error
     (run-script #:hyps [(y Int)] #:goal Int
                 (then-l (plus 2)
                         [(int-intro 1) (assumption 0)]))))
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

  (define (length-+ str num)
    (run-script #:hyps ((str String) (num Int))
                #:goal Int
                (then-l (plus 2)
                        ((then strlen
                               (assumption 1))
                         (assumption 0)))))
  
  (define add
    (run-script #:goal (→ Int (→ Int Int))
                (repeat (→-intro))
                (→-intro 'z)
                (try (repeat (→-intro))
                     skip)
                (try (repeat (→-intro))
                     skip)
                   
                ;(string-intro "hey")
                (then-l (plus 2)
                        [(assumption 0)
                         (assumption 1)])))
  (for* ([i (in-range 100)]
         [j (in-range 100)])
    (check-equal? ((add i) j) (+ i j)))

  (define b3 (run-script #:goal String
                         (then-l repeat-string
                                 ((then (int-intro 3))
                                  (then (string-intro "badger "))))))
  (check-equal? b3 "badger badger badger ")
  )
