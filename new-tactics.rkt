#lang racket
(require (for-syntax racket/match racket/control racket/promise))
(require (for-syntax racket/pretty))
(require (for-syntax racket/list))

(module+ test
  (require rackunit))

(define-for-syntax next-tactic (box #f))

(define-syntax (hole stx)
  ((unbox next-tactic) stx))

(define-for-syntax (leftmost p)
  (displayln p)
  (cond [(pair? p) (leftmost (car p))]
        [else p]))

(begin-for-syntax
  (struct ⊢ (hyps goal) #:transparent))

(define-syntax (Integer s) (error 'Integer))
(define-syntax (-> s) (error '->))
(define-syntax (∀ s) (error '∀))
(define-syntax (⋆ s) (error '⋆))

(define-for-syntax (make-hole hyps g)
  (syntax-property #'hole 'goal (⊢ hyps g)))

(define-for-syntax (goal h) (leftmost (syntax-property h 'goal)))

(define-for-syntax (∀-intro h)
  (match-define (⊢ hyps g) (goal h))
  (syntax-case g (∀)
    [(∀ α t)
     (make-hole (cons (cons #'α #'⋆) hyps) #'t)]
    [_ ((fail "not ∀") h)]))

(define-for-syntax ((->-intro x) h)
  (match-define (⊢ hyps g) (goal h))
  (syntax-case g (->)
    [(-> a b)
     (let ([x (datum->syntax #f x)])
       ((emit #`(lambda (#,x) #,(make-assumption-hole x #'a hyps #'b))) h))]
    [_ ((fail "not an ->") h)]))

(define-for-syntax (make-assumption-hole x a hyps g)
  (syntax-property #`(assumption-hole #,x #,a) 'goal (⊢ hyps g)))

(define-syntax (assumption-hole stx)
  (match-define (⊢ hyps g) (goal stx))
  (syntax-case stx ()
    [(_ x a)
     (make-hole (cons (cons #'x #'a) hyps) g)]))

(define-for-syntax ((assumption n) h)
  (match-define (⊢ hyps g) (goal h))
  (when (>= n (length hyps))
    ((fail "bad") h))
  (match-define (cons x t) (list-ref hyps n))
  (unless (goal-matches? t g)
    ((fail "bad type") h))
  x)

(define-for-syntax (goal-matches? a b) #t)

(define-for-syntax ((int-intro i) h)
  (unless (integer? i)
    ((fail "not an int") h))
  (match-define (⊢ hyps g) (goal h))
  (unless (and (identifier? g) (free-identifier=? #'Integer g))
    ((fail "not an int goal") h))
  ((emit (datum->syntax h i)) h))

(define-for-syntax ((emit stx) hole)
  stx)

(define-for-syntax ((then t . ts) hole)
  (if (null? ts)
      (set-box! next-tactic (lambda _ (error 'fail)))
      (set-box! next-tactic (apply then ts)))
  ((force t) hole))

(define-for-syntax ((fail msg) hole)
  (raise-syntax-error #f msg hole))

(define-for-syntax ((try t1 t2) hole)
  (with-handlers ([exn:fail:syntax? (lambda (e) (t2 hole))])
    (t1 hole)))

(define-for-syntax (skip h) h)

(define-syntax (run-script stx)
  (syntax-case stx ()
    [(_ #:goal g . tacs)
     #'(let ()
         (define-syntax (go s)
           (set-box! next-tactic (then . tacs))
           #`(#%expression #,(make-hole null #'g)))
         (#%expression (go)))]
    [(_ . tacs)
     #'(run-script #:goal #f . tacs)]))

(define-for-syntax solve-with-1
  (then (emit #'1) (delay solve-with-1)))

(define-for-syntax (debug h)
  (pretty-print (goal h))
  ;; avoid copying syntax properties onto h
  #`(#%expression #,h))

(define-for-syntax ((named-assumption n) h)
  (match-define (⊢ hyps g) (goal h))
  ;; fixme : check goal type
  (car (assf (lambda (a) (eq? n (syntax-e a))) hyps)))

(module+ test

  (check-equal?
   (run-script (emit #'(+ hole hole hole))
               (emit #'2)
               debug
               solve-with-1)
   4)

  (check-equal?
   (run-script (emit #'(add1 hole))
               (emit #'(- hole hole))
               (try (fail "bad") skip)
               (emit #'2)
               (emit #'3))
   0)

  ;; TODO: test debug output
  (check-equal?
   (run-script #:goal Integer
               debug
               debug
               (int-intro 5))
   5)

  (check-equal? (run-script (try (int-intro 5)
                                 (emit #'"hi")))
                "hi")

  (define f (run-script #:goal (-> Integer Integer)
                        (->-intro 'x)
                        (int-intro 32)))
  (check-equal? (f 1) 32)
  (check-equal? (f 2) 32)
  (check-equal? (f 20234) 32)

  (define id (run-script #:goal (-> Integer Integer)
                         (->-intro 'x)
                         (assumption 0)))

  (for ([i (in-range 100)])
    (check-equal? (id i) i))



  (define fst (run-script #:goal (-> Integer (-> Integer Integer))
                          (->-intro 'x)
                          (->-intro 'x)
                          (assumption 1)))

  (define snd (run-script #:goal (-> Integer (-> Integer Integer))
                          (->-intro 'x)
                          (->-intro 'x)
                          (named-assumption 'x)))

  (check-equal? ((fst 5) 6) 5)
  (check-equal? ((snd 5) 6) 6))


