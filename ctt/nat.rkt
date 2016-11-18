#lang racket

(require "ctt-core.rkt"
         (except-in "../lcfish.rkt" run-script)
         (for-syntax racket/match syntax/parse))

(module+ test (require rackunit))

(struct Nat () #:transparent)

(define (ind-Nat target base step)
  (if (zero? target)
      base
      (step (sub1 target) (ind-Nat (sub1 target) base step))))


(define (monus . args)
  (max 0 (apply - args)))



(begin-for-syntax
  ;; TODO: computation and equality rules for ind-Nat, add1, +, *,-
  
  (define nat-formation
    (rule (⊢ H G)
          #:when (syntax-parse G
                   [u:Uni #t]
                   [_     #f])
          (local-expand #'(Nat) 'expression null)))
  (define nat-equality
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with u:Uni #'eq.type
             #:with (#%plain-app n1) #'eq.left
             #:with (#%plain-app n2) #'eq.right
             #:when (and (constructs? #'Nat #'n1)
                         (constructs? #'Nat #'n2))
             #'(void)]
            [_ (not-applicable)])))
  (define (nat-intro i)
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [(#%plain-app n:id)
             #:when (and (exact-nonnegative-integer? i)
                         (constructs? #'Nat #'n))
             #`'#,i]
            [_ (not-applicable)])))

  (define nat-literal-equality
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with (#%plain-app n) #'eq.type
             #:with (quote j) #'eq.left
             #:with (quote k) #'eq.right
             #:when (and (constructs? #'Nat #'n)
                         (exact-nonnegative-integer? (syntax-e #'j))
                         (exact-nonnegative-integer? (syntax-e #'k))
                         (= (syntax-e #'j) (syntax-e #'k)))
             #'(void)]
            [_ (not-applicable)])))

  (define nat-intro-add1
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [(#%plain-app n:id)
             #:when (constructs? #'Nat #'n)
             #`(add1 #,(subgoal (⊢ H G)))]
            [_ (not-applicable)])))

  (define nat-equality-add1
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (add1)
            [eq:Eq
             #:with (#%plain-app nat) #'eq.type
             #:with (#%plain-app add1 j) #'eq.left
             #:with (#%plain-app add1 k) #'eq.right
             #:when (constructs? #'Nat #'nat)
             (subgoal (⊢ H (local-expand #'(≡ (Nat) j k) 'expression null)))])))


  (define (nat-intro-arith op args)
    (rule (⊢ H G)
          #:when (and (exact-positive-integer? args)
                      (member op '(+ * -)))
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [(#%plain-app nat)
             #:when (constructs? #'Nat #'nat)
             (define subgoals
               (for/list ([i (in-range 0 args)])
                 (subgoal (⊢ H G))))
             #`(#,(match op
                    ['+ #'+]
                    ['* #'*]
                    ['- #'monus])
                #,@subgoals)])))

  (define ind-nat-step-zero
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (ind-Nat)
            [eq:Eq
             #:with (#%plain-app ind-Nat n base step) #'eq.left
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #'(≡ eq.type base eq.right) 'expression null)))
                #,(subgoal (⊢ H (local-expand #'(≡ (Nat) n 0) 'expression null)))
                (void))])))
  
  
  (define (nat-elim n)
    (rule (⊢ (and H (at-hyp n Δ (hyp x nat #f) Γ)) G)
          (syntax-parse nat
            #:literal-sets (kernel-literals)
            [(#%plain-app n)
             #:when (constructs? #'Nat #'n)
             
             (define base
               (subgoal (⊢ H (subst1 x (local-expand #'0 'expression null) G))))
             (define k #'k)
             (define ih #'ih)
             (define step
               #`(λ (#,k #,ih)
                   #,(make-assumption-hole
                      (lambda (g) (subgoal g))
                      (lambda (n ih)
                        (⊢ (cons (hyp ih (subst1 x n G) #f)
                                 (cons (hyp n nat #f)
                                       H))
                           (subst1 x #`(add1 #,n) G)))
                      k
                      ih)))
             
             #`(ind-Nat #,x
                        #,base
                        #,step)]))))

(module+ test

  ;; Test that symmetry and replace do the right thing  
  (theorem add1-garbage
           (Π (≡ (Nat) 2 3)
              (λ (h)
                (≡ (Nat) (add1 2) (add1 3))))
           (then-l (Π-intro 0 'x)
                   ((then-l equality-equality
                            (nat-equality nat-literal-equality nat-literal-equality))))
           (then-l (replace 0
                            (local-expand #'(Nat) 'expression null)
                            (local-expand #'3 'expression null)
                            (local-expand #'2 'expression null)
                            #'(lambda (x) (≡ (Nat) (add1 2) (add1 x))))
                   (symmetry nat-equality (then nat-equality-add1
                                                nat-literal-equality))
                   ((assumption 0))))
  
  (theorem my-Nat-type (U 0) nat-formation)
  (check-equal? my-Nat-type (Nat))

  (theorem nat-is-nat (≡ (U 0) (Nat) (Nat)) nat-equality)
  (check-equal? nat-is-nat (void))

  (define sixteen
    (run-script #:goal (Nat)
                (nat-intro 16)))
  (check-equal? sixteen 16)
  
  (theorem plus
           (Π (Nat) (λ (_)
                            (Π (Nat) (λ (_)
                                       (Nat)))))
           (then-l
                 (Π-intro 0 'n)
                 (nat-equality (Π-intro 0 'm))
                 (nat-equality))
                (then-l
                 (nat-elim 1)
                 ((assumption 0) nat-intro-add1))
                (assumption 0))

  (check-equal? ((plus 2) 5) 7)

  #;
  (theorem plus-zero
           (Π (Nat)
              (λ (n)
                (≡ (Nat) ((plus n) 0) n)))
           (then-l (Π-intro 0)
                   (nat-equality (unfold #'plus)))
           (then-l (nat-elim 1)
                   ((replace 0 (Π (Nat) (λ (j) (Π (Nat) (λ (k) (Nat))))) #'plus) todo)))
  
  (theorem another-plus
           (Π (Nat) (λ (_)
                      (Π (Nat) (λ (_)
                                 (Nat)))))
           (Π-intro 0 'n)
                (try nat-equality skip)
                (Π-intro 0 'm)
                (try nat-equality skip)
                (then-l
                 (nat-intro-arith '+ 2)
                 ((assumption 0) (assumption 1))))

  (check-equal? ((another-plus 2) 5) 7)

  (define yet-another-plus
    (run-script #:goal (Π (Nat) (λ (j)
                                  (Π (Nat) (λ (k)
                                             (Nat)))))
                (lemma #'plus 'addition)
                (assumption 0)))

  ;; TODO: requires rewriting with an equality and axiomatization of +, ind-Nat's op-sem
  (theorem plus-is-plus
           (≡ (Π (Nat) (λ (_)
                         (Π (Nat) (λ (_)
                                    (Nat)))))
              plus
              another-plus)
           (then-l (extensionality 'an-arg)
                   (todo todo (then-l (nat-elim 0)
                                      ((then-l
                                        (unfold #'plus)
                                        ((replace 0 (local-expand #'(Π (Nat) (λ (_)
                                                                               (Π (Nat) (λ (_)
                                                                                          (Nat)))))
                                                                  'expression null)
                                                  #'plus
                                                  (local-expand #'(lambda (n)
                                                                    (lambda (m)
                                                                      (ind-Nat
                                                                       n m (lambda (k ih) (add1 ih)))))
                                                                'expression null)
                                                  (local-expand #'(λ (p) (≡ (Π (Nat) (λ (_)
                                                                                       (Nat)))
                                                                            (p 0) (another-plus 0)))
                                                                'expression null)))
                                        ((assumption 0) todo todo))
                                       todo))))))
