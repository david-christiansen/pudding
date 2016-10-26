#lang racket

(require (except-in "lcfish.rkt" run-script)
         (for-syntax racket/contract racket/match)
         (for-template racket/base))

(module+ test (require rackunit))

(begin-for-syntax
  (struct ⊢ (hyps goal) #:transparent))

(define-syntax (define-type stx)
  (syntax-case stx ()
    [(_ id)
     #'(define-syntax (id stx) (raise-syntax-error 'id "Not available for programs" stx))]))

(define-type Int)
(define-type String)
(define-type →)

(begin-for-syntax
  (define (type=? t1 t2)
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
      [_ #f])))

;; For trampolining through the macro expander to get the right scopes.
;; Communicates with make-assumption-hole and →-intro.
(define-syntax (assumption-hole stx)
  (match-define (⊢ H G) (get-goal stx))
  (define next-hole (syntax-property stx 'next-hole))
  (syntax-case stx ()
    [(_ x a)
     (set-goal (next-hole) (⊢ (cons (cons #'x #'a) H) G))]))

(define-for-syntax (make-assumption-hole next-hole x a H G)
  (syntax-property
   (set-goal #`(assumption-hole #,x #,a) (⊢ H G))
   'next-hole next-hole))

(begin-for-syntax
  (define (leftmost v)
    (cond
      [(pair? v) (leftmost (car v))]
      [else v]))

  (define (get-goal stx)
    (leftmost (syntax-property stx 'goal)))

  (define (set-goal stx goal)
    (syntax-property stx 'goal goal))

  (define/contract ((guard-goal pred tac) hole make-hole)
    (-> (-> ⊢? any/c) tactic/c tactic/c)
    (match (get-goal hole)
      [#f ((fail "No goal found.") hole make-hole)]
      [g #:when (pred g)
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
    (match-define (⊢ H G) (get-goal hole))
    (syntax-case G (→)
      [(→ a b)
       ((emit #`(lambda (#,x) #,(make-assumption-hole make-hole (datum->syntax #'here x) #'a H #'b))) hole make-hole)]
      [_ ((fail "Not an arrow: ~a" (syntax->datum G)) hole make-hole)]))

  (define/contract ((assumption n) hole make-hole)
    (-> exact-nonnegative-integer? tactic/c)
    (match-define (⊢ H G) (get-goal hole))
    (if (>= n (length H))
        ((fail "Not enough hypotheses") hole make-hole)
        (match-let ([(cons x t) (list-ref H n)])
          (if (not (type=? t G))
              ((fail (format "Wrong goal type. Expected ~a, got ~a" G t))
               hole make-hole)
              ((emit x) hole make-hole)))))

  (define/contract ((plus n) hole make-hole)
    (-> exact-nonnegative-integer? tactic/c)
    (match-define (⊢ H G) (get-goal hole))
    (if (not (type=? G #'Int))
        ((fail (format "Type not Int: ~a" G)) hole make-hole)
        ((emit #`(+ #,@(for/list ([h (in-producer make-hole)]
                                  [i (in-range n)])
                         (set-goal h (⊢ H #'Int))))) hole make-hole))))


(define-syntax (run-script stx)
  (syntax-case stx ()
    [(run-script #:hyps [(x t) ...] #:goal g tac . tacs)
     #'(let ()
         (define-syntax (go s)
           (set-goal (hole-with-tactic (then tac . tacs))
                     (⊢ (reverse (list (cons #'x #'t) ...)) #'g)))
         (go))]
    [(run-script #:goal g
        tac . tacs)
     #'(run-script #:hyps () #:goal g tac . tacs)]))



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
                        (list (int-intro 1)
                              (assumption 0)))))

  (for ([i (in-range 0 100)])
    (check-equal? (f i) (add1 i)))

  ;; Wrong goal type:
  #;
  (define (g x)
    (run-script #:hyps [(x String)] #:goal Int
                (then-l (plus 2)
                        (list (int-intro 1)
                              (assumption 0)))))

  ;; Identifiers must match:
  #;
  (define (g x)
    (run-script #:hyps [(y Int)] #:goal Int
                (then-l (plus 2)
                        (list (int-intro 1)
                              (assumption 0)))))

  (define twice
    (run-script #:goal (→ Int Int)
                (→-intro 'x)
                (plus 2)
                (assumption 0)))
  (for ([i (in-range 100)])
    (check-equal? (twice i) (* 2 i)))

  (define add
    (run-script #:goal (→ Int (→ Int Int))
                (→-intro)
                (→-intro)
                (then-l (plus 2)
                        (list (assumption 0)
                              (assumption 1)))))
  (for* ([i (in-range 100)]
         [j (in-range 100)])
    (check-equal? ((add i) j) (+ i j))))
