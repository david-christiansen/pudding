#lang racket

(require "ctt-core.rkt"
         "../lift-tooltips.rkt"
         "../lift-errors.rkt"
         "../rule.rkt"
         racket/stxparam
         (except-in "../lcfish.rkt" run-script)
         (for-syntax "unsafe.rkt" "../goal.rkt" racket/list)
         (for-syntax racket/match syntax/parse racket/promise racket/format racket/list
                     racket/syntax syntax/id-set))

(provide (struct-out Nat)
         ind-Nat
         monus
         (for-syntax Nat-stx
                     add1-equality
                     ind-Nat-0-reduce
                     ind-Nat-add1-reduce
                     ind-nat-step-zero
                     ind-Nat-equality
                     nat-equality
                     nat-intro-arith
                     nat-equal-arith
                     nat-equal-const
                     nat-elim
                     nat-intro-add1
                     nat-simplify
                     E
                     ex))

(module+ test (require rackunit))

(let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
  (begin (tt)))
(module+ test
  (let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
    (begin (tt))))

(struct Nat () #:transparent #:extra-constructor-name make-Nat)

(define (ind-Nat target base step)
  (if (zero? target)
      base
      ((step (sub1 target)) (ind-Nat (sub1 target) base step))))


(define (monus . args)
  (max 0 (apply - args)))

(begin-for-syntax (define-syntax-rule (E t) (ex #`t)))
(define-for-syntax (ex tm)
  (local-expand tm 'expression null))



(begin-for-syntax
  (require (for-syntax racket/base syntax/stx))
  
  
  (define-syntax-class Nat-stx
    #:literal-sets (kernel-literals)
    #:literals (make-Nat)
    (pattern (#%plain-app make-Nat)))
  

  (define nat-formation
    (rule (⊢ H G)
          #:seal seal-ctt
          #:when (syntax-parse G
                   [u:Uni #t]
                   [_     #f])
          (ex #'(Nat))))
  (define nat-equality
    (rule (⊢ H G)
          #:seal seal-ctt
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
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [(#%plain-app n:id)
             #:when (and (exact-nonnegative-integer? i)
                         (constructs? #'Nat #'n))
             #`'#,i]
            [_ (not-applicable)])))

  (define nat-literal-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             #:with (quote j) #'eq.left
             #:with (quote k) #'eq.right
             #:when (and (exact-nonnegative-integer? (syntax-e #'j))
                         (exact-nonnegative-integer? (syntax-e #'k))
                         (= (syntax-e #'j) (syntax-e #'k)))
             #'(void)]
            [_ (not-applicable)])))

  (define nat-intro-add1
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [n:Nat-stx
             #`(add1 #,(subgoal (⊢ H G)))]
            [_ (not-applicable)])))

  (define nat-equality-add1
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (add1)
            [eq:Eq
             #:with nat:Nat-stx #'eq.type
             #:with (#%plain-app add1 j) #'eq.left
             #:with (#%plain-app add1 k) #'eq.right
             (subgoal (⊢ H (ex #'(≡ (Nat) j k))))]
            [_ (not-applicable)])))


  (define (nat-intro-arith op args)
    (rule (⊢ H G)
          #:seal seal-ctt
          #:when (and (exact-positive-integer? args)
                      (member op '(+ * -)))
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [nat:Nat-stx
             (define subgoals
               (for/list ([i (in-range 0 args)])
                 (subgoal (⊢ H G))))
             #`(#,(match op
                    ['+ #'+]
                    ['* #'*]
                    ['- #'monus])
                #,@subgoals)]
            [_ (not-applicable)])))

  (define nat-equal-const
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             #:with (quote j:nat) #'eq.left
             #:with (quote k:nat) #'eq.right
             #:when (= (syntax-e #'j) (syntax-e #'k))
             #'(void)]
            [_ (not-applicable)])))
  
  (define nat-equal-arith
    (rule (⊢ H G)
          #:seal seal-ctt
          (define ops (list #'+ #'* #'monus))
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (+ * monus)
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             #:with (#%plain-app op1:id arg1 ...) #'eq.left
             #:with (#%plain-app op2:id arg2 ...) #'eq.right
             #:when (= (length (syntax->list #'(arg1 ...)))
                       (length (syntax->list #'(arg2 ...))))
             #:when (and (free-identifier=? #'op1 #'op2))
             #:with (~or + * monus) #'op1
             #:with (subgoal ...) (for/list ([j (syntax->list #'(arg1 ...))]
                                             [k (syntax->list #'(arg2 ...))])
                                    (subgoal (⊢ H (ex #`(≡ (Nat) #,j #,k)))))
             #`(side-conditions subgoal ...
                                (void))]
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             #:with (#%plain-app op1:id arg1 ...) #'eq.left
             #:with (#%plain-app op2:id arg2 ...) #'eq.right
             #:with (longer ...) (if (> (length (syntax->list #'(arg1 ...)))
                                        (length (syntax->list #'(arg2 ...))))
                                     #'(arg1 ...)
                                     #'(arg2 ...))
             #:with (shorter ... last) (if (> (length (syntax->list #'(arg1 ...)))
                                        (length (syntax->list #'(arg2 ...))))
                                     #'(arg2 ...)
                                     #'(arg1 ...))
             #:when (and (free-identifier=? #'op1 #'op2))
             #:with (~or + * monus) #'op1
             #:with (subgoals ...) (for/list ([j (syntax->list #'(longer ...))]
                                              [k (syntax->list #'(shorter ...))])
                                    (subgoal (⊢ H (ex #`(≡ (Nat) #,j #,k)))))
             #:with final-subgoal (subgoal (⊢ H (ex #`(≡ (Nat)
                                                         (op1 #,@(drop (syntax->list #'(longer ...))
                                                                       (length (syntax->list #'(shorter ...)))))
                                                         last))))
             #`(side-conditions subgoals ...
                                final-subgoal
                                (void))]
            [other
             (not-applicable "Not a Nat arithmetic equality: ~a" (stx->string #'other))])))

  (define (normalize-addition stx)
    (define (flatten-addition tm)
      (syntax-parse tm
        #:literal-sets (kernel-literals)
        #:literals (+ add1)
        ((#%plain-app add1 n) (cons #''1 (flatten-addition #'n)))
        [(#%plain-app + arg ...)
         (apply append (map flatten-addition (syntax->list #'(arg ...))))]
        [other (list #'other)]))
    (define (num-of stx)
      (syntax-parse stx
        #:literal-sets (kernel-literals)
        ((quote n) #:when (number? (syntax-e #'n)) (syntax-e #'n))
        (n:nat (syntax-e #'n))
        (_ #f)))
    (define-values (c xs)
      (for/fold ([constant 0]
                 [other '()])
                ([e (in-list (flatten-addition stx))])
        (define v (num-of e))
        (if (number? v)
            (values (+ constant v) other)
            (values constant (cons e other)))))
    (define (compare s1 s2)
      (string<? (~a (syntax->datum s1)) (~a (syntax->datum s2))))
    
    (match (if (= c 0)
               (sort xs compare)
               (cons (datum->syntax stx c) (sort xs compare)))
      ['() #'0]
      [(list x) (datum->syntax stx x)]
      [(list-rest x xs) (quasisyntax/loc stx
                          (#%plain-app + #,x #,@xs))]))
  (require syntax/stx)
  (define nat-simplify
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             (subgoal (⊢ H
                         (ex #`(≡ (Nat)
                                  #,(normalize-addition #'eq.left)
                                  #,(normalize-addition #'eq.right)))))]
            [_ (not-applicable)])))
  
  (define ind-nat-step-zero
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (ind-Nat)
            [eq:Eq
             #:with (#%plain-app ind-Nat n base step) #'eq.left
             #`(side-conditions
                #,(subgoal (⊢ H (ex #'(≡ eq.type base eq.right))))
                #,(subgoal (⊢ H (ex #'(≡ (Nat) n 0))))
                (void))]
            [_ (not-applicable)])))

  (define add1-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (add1)
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             #:with (#%plain-app add1 j) #'eq.left
             #:with (#%plain-app add1 k) #'eq.right
             (subgoal (⊢ H (ex #'(≡ (Nat) j k))))]
            [_ (not-applicable)])))
  
  (define (nat-elim n)
    (rule (⊢ (and H (at-hyp n Δ (hyp x nat #f) Γ)) G)
          #:seal seal-ctt
          (syntax-parse nat
            #:literal-sets (kernel-literals)
            [(#%plain-app n)
             #:when (constructs? #'Nat #'n)
             
             (define base
               (subgoal (⊢ H (subst1 x #'(quote 0) G))))
             (define k #'k)
             (define ih #'ih)
             (define step
               #`(λ (#,k)
                   (λ (#,ih)
                     #,(make-assumption-hole
                        (lambda (g) (subgoal g))
                        (lambda (n ih)
                          (⊢ (cons (hyp ih (subst1 x n G) #f)
                                   (cons (hyp n nat #f)
                                         H))
                             (ex (subst1 x #`(add1 #,n) G))))
                        k
                        ih))))
             
             #`(ind-Nat #,x
                        #,base
                        #,step)]
            [_ (not-applicable)])))


  (define (ind-Nat-equality motive)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse (ex motive)
            #:literal-sets (kernel-literals)
            [(#%plain-lambda (motive-var:id) motive-type)
             (syntax-parse G
               #:literal-sets (kernel-literals)
               #:literals (ind-Nat)
               [eq:Eq
                #:with (#%plain-app ind-Nat target-l base-l step-l) #'eq.left
                #:with (#%plain-app ind-Nat target-r base-r step-r) #'eq.right
                #:when (α-equiv?/hyps H
                                      #'eq.type
                                      (subst1 #'motive-var #'target-l #'motive-type))
                (with-syntax* ([target= (subgoal (⊢ H (ex #'(≡ (Nat) target-l target-r))))]
                               [base-type (subst1 #'motive-var #'0 #'motive-type)]
                               [base= (subgoal (⊢ H (ex #'(≡ base-type base-l base-r))))]
                               [step-type #`(Π (Nat)
                                               (lambda (n)
                                                 (Π #,(subst1 #'motive-var #'n #'motive-type)
                                                    (lambda (ih)
                                                      #,(subst1 #'motive-var #'(add1 n) #'motive-type)))))]
                               [step= (subgoal (⊢ H (ex #'(≡ step-type step-l step-r))))])
                  #'(side-conditions target= base= step= (void)))])]
            [_ (not-applicable "Bad motive ~a" motive)])))
  
  (define ind-Nat-0-reduce
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            (eq:Eq
             #:with (#%plain-app ind-Nat tgt base _) #'eq.left
             (with-syntax ([its-zero (subgoal (⊢ H (ex #'(≡ (Nat) tgt 0))))]
                           [real-goal (subgoal (⊢ H (ex #'(≡ eq.type base eq.right))))])
               #'(side-conditions its-zero real-goal (void))))
            (_ (not-applicable)))))

  (define (ind-Nat-add1-reduce k)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (ind-Nat)
            [eq:Eq
             #:with (#%plain-app ind-Nat n base step) #'eq.left
             (with-syntax ([n-add1 (subgoal (⊢ H (ex #`(≡ (Nat) n (add1 #,k)))))]
                           [the-step (subgoal (⊢ H (ex #`(≡ eq.type
                                                            (#%plain-app (#%plain-app step
                                                                                      #,k)
                                                                         (ind-Nat #,k base step))
                                                            eq.right))))])
               #'(side-conditions n-add1 the-step (void)))]))))



(module+ test

  ;; Test that symmetry and replace do the right thing  
  (theorem add1-garbage
           (Π (≡ (Nat) 2 3)
              (λ (h)
                (≡ (Nat) (add1 2) (add1 3))))
           (then-l (Π-intro 0 'x)
                   ((then-l equality-equality
                            (nat-equality nat-literal-equality nat-literal-equality))))
           (then-l (replace (ex #'(Nat))
                            (ex #'3)
                            (ex #'2)
                            (ex #'(lambda (x) (≡ (Nat) (add1 2) (add1 x)))))
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
  
  

  #;
  (theorem plus-zero
           (Π (Nat)
              (λ (n)
                (≡ (Nat) ((plus n) 0) n)))
           (then-l (Π-intro 0)
                   (nat-equality (unfold #'plus)))
           (then-l (nat-elim 1)
                   ((replace (Π (Nat) (λ (j) (Π (Nat) (λ (k) (Nat))))) #'plus) todo)))
  





)




























