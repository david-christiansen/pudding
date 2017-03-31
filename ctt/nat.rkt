#lang racket

(require "ctt-core.rkt"
         "../lift-tooltips.rkt"
         "../lift-errors.rkt"
         "../rule.rkt"
         (except-in "../lcfish.rkt" run-script)
         (for-syntax "unsafe.rkt" "../goal.rkt")
         (for-syntax racket/match syntax/parse racket/promise racket/format racket/list
                     racket/syntax syntax/id-set))

(module+ test (require rackunit))

(let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
  (begin (tt)))
(module+ test
  (let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
    (begin (tt))))

(struct Nat () #:transparent)

(define (ind-Nat target base step)
  (if (zero? target)
      base
      ((step (sub1 target)) (ind-Nat (sub1 target) base step))))


(define (monus . args)
  (max 0 (apply - args)))



(begin-for-syntax
  (define-syntax-class Nat-stx
    #:literal-sets (kernel-literals)
    (pattern (#%plain-app N:id)
             #:when (constructs? #'Nat #'N)))
  
  ;; TODO: computation and equality rules for ind-Nat, add1, +, *,-
  
  (define nat-formation
    (rule (⊢ H G)
          #:seal seal-ctt
          #:when (syntax-parse G
                   [u:Uni #t]
                   [_     #f])
          (local-expand #'(Nat) 'expression null)))
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
             (subgoal (⊢ H (local-expand #'(≡ (Nat) j k) 'expression null)))])))


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
                #,@subgoals)])))

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
                                    (subgoal (⊢ H (local-expand #`(≡ (Nat) #,j #,k) 'expression null))))
             #`(side-conditions subgoal ...
                (void))]
            [other
             (displayln #'other)
             (not-applicable "Not a Nat arithmetic equality: ~a" (syntax->datum #'other))])))

  ;; TODO: implement fancier normalization
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
  
  (define nat-simplify
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             #:with n:Nat-stx #'eq.type
             (subgoal (⊢ H
                         (local-expand #`(≡ (Nat)
                                            #,(normalize-addition #'eq.left)
                                            #,(normalize-addition #'eq.right))
                                       'expression
                                       null)))]
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
                #,(subgoal (⊢ H (local-expand #'(≡ eq.type base eq.right) 'expression null)))
                #,(subgoal (⊢ H (local-expand #'(≡ (Nat) n 0) 'expression null)))
                (void))])))

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
             (subgoal (⊢ H (local-expand #'(≡ (Nat) j k) 'expression null)))])))
  
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
                             (local-expand (subst1 x #`(add1 #,n) G)
                                           'expression
                                           null)))
                      k
                      ih))))
             
             #`(ind-Nat #,x
                        #,base
                        #,step)])))


  (define (ind-Nat-equality motive)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse (local-expand motive 'expression null)
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
                (with-syntax* ([target= (subgoal (⊢ H (local-expand #'(≡ (Nat) target-l target-r)
                                                                    'expression
                                                                    null)))]
                               [base-type (subst1 #'motive-var #'0 #'motive-type)]
                               [base= (subgoal (⊢ H (local-expand #'(≡ base-type base-l base-r)
                                                                  'expression
                                                                  null)))]
                               [step-type #`(Π (Nat)
                                               (lambda (n)
                                                 (Π #,(subst1 #'motive-var #'n #'motive-type)
                                                    (lambda (ih)
                                                      #,(subst1 #'motive-var #'(add1 n) #'motive-type)))))]
                               [step= (subgoal (⊢ H (local-expand #'(≡ step-type step-l step-r)
                                                                  'expression
                                                                  null)))])
                  #'(side-conditions target= base= step= (void)))])]
            [_ (not-applicable "Bad motive ~a" motive)])))
  
  (define ind-Nat-0-reduce
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            (eq:Eq
             #:with (#%plain-app ind-Nat tgt base _) #'eq.left
             (with-syntax ([its-zero (subgoal (⊢ H (local-expand #'(≡ (Nat) tgt 0)
                                                                 'expression
                                                                 null)))]
                           [real-goal (subgoal (⊢ H (local-expand #'(≡ eq.type base eq.right)
                                                                  'expression
                                                                  null)))])
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
             (with-syntax ([n-add1 (subgoal (⊢ H (local-expand #`(≡ (Nat) n (add1 #,k))
                                                               'expression
                                                               null)))]
                           [the-step (subgoal (⊢ H (local-expand #`(≡ eq.type
                                                                      (#%plain-app (#%plain-app step
                                                                                                #,k)
                                                                                   (ind-Nat #,k base step))
                                                                      eq.right)
                                                                 'expression
                                                                 null)))])
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

  (define-for-syntax (repeat t)
    (try (then t
               (delay (repeat t)))
         skip))

  (define-syntax (abstract stx)
    (syntax-parse stx
      ;#:datum-literals (quote) ;; WARNING: hack alert
      ;((quote x) stx)
      (any 
       (syntax-parse stx
         #:literal-sets (kernel-literals)
         [(_ free-id:id bound-id:id tm:id)
          #:when (free-identifier=? #'free-id #'tm)
          #'bound-id]
         [(_ free-id bound-id (#%expression e))
          (syntax/loc #'e
            (abstract free-id bound-id e))]
         [(_ free-id bound-id (#%plain-app tm ...))
          (syntax/loc stx
            (#%plain-app (abstract free-id bound-id tm) ...))]
         [(_ free-id bound-id (#%plain-lambda (x ...) tm ...))
          (syntax/loc stx
            (#%plain-lambda (x ...) (abstract free-id bound-id tm) ...))]
         [(_ free-id bound-id (quote any)) #'(quote any)]
         [(_ free-id bound-id (tm ...))
          (syntax/loc stx
            ((abstract free-id bound-id tm) ...))]
         [(_ _ _ other) #'other]))))

  (define-for-syntax (auto)
    (match-goal
     ((⊢ H G)
      (syntax-parse G
        #:literal-sets (kernel-literals)
        [eq:Eq
         #:with l:Pi #'eq.left
         #:with r:Pi #'eq.right
         (Π-in-uni)]
        [eq:Eq
         #:with l:Nat-stx #'eq.left
         #:with r:Nat-stx #'eq.right
         nat-equality]
        [eq:Eq
         #:with x:id #'eq.left
         #:with y:id #'eq.right
         #:when (free-identifier=? #'x #'y)
         #:with i:nat (index-where H (lambda (h) (free-identifier=? (hypothesis-id h) #'x)))
         (assumption-refl (syntax-e #'i))]
        [eq:Eq
         #:with (quote n:nat) #'eq.left
         #:with (quote k:nat) #'eq.right
         nat-equal-const]
        [foo (fail "Can't auto: ~a" (syntax->datum G))]))))

  (define-for-syntax (call-with-hypothesis-name num tac)
    (match-goal
     ((⊢ H G)
      #:when (>= (length H) num)
      (tac (hypothesis-id (list-ref H num))))))

  (define-for-syntax (call-with-hypothesis-names . args)
    (match args
      [(list num ... tac)
       (match-goal
        ((⊢ H G)
         (apply tac
                (for/list ([n num])
                  (hypothesis-id (list-ref H n))))))]
      [_ (fail "Bad call-with-hypothesis-names use")]))
  
  (define-for-syntax (unfold-all id)
    (then (unfold id)
          (match-goal
           ((⊢ (cons (hyp _ t _) H) G)
            (syntax-parse t
              [eq:Eq
               (let ([context (with-syntax ([G G] [id id])
                                (local-expand 
                                 #'(lambda (x) (abstract id x G))
                                 'expression
                                 null))])
                 (then-l (replace 0 #'eq.type #'eq.left #'eq.right context)
                         ((assumption 0)
                          (then (repeat (auto))))))])))))
  
  ;; TODO: requires rewriting with an equality and axiomatization of +, ind-Nat's op-sem
  (theorem plus-is-plus
           (≡ (Π (Nat) (λ (n1)
                         (Π (Nat) (λ (n2)
                                    (Nat)))))
              plus
              another-plus)
           (then-l (extensionality 'an-arg)
                   ((then (unfold-all #'plus)
                          λ-equality
                          λ-equality
                          (then-l (ind-Nat-equality (local-expand #'(lambda (_) (Nat)) 'expression null))
                                  ((auto)
                                   (auto)
                                   (then λ-equality λ-equality
                                         nat-simplify
                                         nat-equal-arith
                                         (auto)))))
                    (then (unfold-all #'another-plus)
                          λ-equality
                          λ-equality
                          (then nat-equal-arith
                                (auto)))
                    (then-l (then (nat-elim 0)
                                  (unfold-all #'plus)
                                  (unfold-all #'another-plus))
                            ((then apply-reduce
                                   symmetry
                                   apply-reduce
                                   λ-equality
                                   nat-simplify
                                   symmetry
                                   (then ind-Nat-0-reduce nat-simplify
                                         (auto))
                                   (assumption-refl 0))
                             (then apply-reduce
                                   symmetry
                                   apply-reduce
                                   symmetry
                                   λ-equality
                                   (then-l (call-with-hypothesis-name 4 ind-Nat-add1-reduce)
                                           ((then nat-simplify
                                                  nat-equal-arith
                                                  (try nat-equal-const
                                                       (assumption-refl 4)))
                                            (then-l
                                             (call-with-hypothesis-name
                                              4
                                              (lambda (k-name)
                                                (cut 0
                                                     (local-expand #`(≡ (Π (Nat) (lambda (n) (Nat)))
                                                                        ((λ (k) (λ (ih) (add1 ih))) #,k-name)
                                                                        (λ (ih) (add1 ih)))
                                                                   'expression
                                                                   null))))
                                             ((then apply-reduce
                                                    λ-equality
                                                    nat-simplify
                                                    nat-equal-arith
                                                    (auto))
                                              (then-l
                                               (call-with-hypothesis-name
                                                5
                                                (lambda (k-name)
                                                  (call-with-hypothesis-name
                                                   1
                                                   (lambda (n2-name)
                                                     (replace 0
                                                              (local-expand #'(Π (Nat) (λ (n) (Nat))) 'expression null)
                                                              (local-expand #`((λ (k) (λ (ih) (add1 ih))) #,k-name) 'expression null)
                                                              (local-expand #'(λ (ih) (add1 ih)) 'expression null)
                                                              (local-expand #`(lambda (hole)
                                                                                (≡ (Nat)
                                                                                   (hole (ind-Nat #,k-name #,n2-name (λ (k) (λ (ih) (add1 ih)))))
                                                                                   (+ #,n2-name (add1 #,k-name))))
                                                                            'expression null))))))
                                               ((then apply-reduce λ-equality nat-simplify nat-equal-arith (auto))
                                                (then (Π-in-uni) nat-equality)
                                                (then apply-reduce
                                                      (then-l
                                                       (call-with-hypothesis-name
                                                        1
                                                        (lambda (n2-name)
                                                          (call-with-hypothesis-name
                                                           5
                                                           (lambda (k-name)
                                                             (cut 0 (local-expand #`(≡ (Nat)
                                                                                       (+ #,n2-name (add1 #,k-name))
                                                                                       (add1 (+ #,n2-name #,k-name)))
                                                                                  'expression
                                                                                  null))))))
                                                       ((then nat-simplify nat-equal-arith (auto))
                                                        (call-with-hypothesis-names
                                                         2 6
                                                         (lambda (n2-name k-name)
                                                           (then-l
                                                            (replace 0
                                                                     (local-expand #'(Nat) 'expression null)
                                                                     (local-expand #`(+ #,n2-name (add1 #,k-name)) 'expression null)
                                                                     (local-expand #`(add1 (+ #,n2-name #,k-name)) 'expression null)
                                                                     (local-expand #`(lambda (hole)
                                                                                       (≡ (Nat)
                                                                                          (add1 (ind-Nat #,k-name
                                                                                                         #,n2-name
                                                                                                         (lambda (k) (lambda (ih) (add1 ih)))))
                                                                                          hole))
                                                                                   'expression
                                                                                   null))
                                                            ((assumption 0)
                                                             nat-equality
                                                             (then add1-equality
                                                                   (then-l (cut 0 (local-expand
                                                                                   #`(≡ (Nat)
                                                                                        (+ #,n2-name #,k-name)
                                                                                        ((another-plus #,n2-name) #,k-name))
                                                                                   'expression
                                                                                   null))
                                                                           ((then (unfold-all #'another-plus)
                                                                                  symmetry
                                                                                  (then-l (cut 0 (local-expand
                                                                                                  #`(≡ (Π (Nat) (lambda (n) (Nat)))
                                                                                                       ((λ (n) (λ (m) (+ m n))) #,n2-name)
                                                                                                       (λ (m) (+ m #,n2-name)))
                                                                                                  'expression
                                                                                                  null))
                                                                                          ((then apply-reduce
                                                                                                 λ-equality
                                                                                                 nat-equal-arith
                                                                                                 (auto))
                                                                                           (then-l (replace 0
                                                                                                            (local-expand #'(Π (Nat) (λ (n) (Nat))) 'expression null)
                                                                                                            (local-expand #`((λ (n) (λ (m) (+ m n))) #,n2-name) 'expression null)
                                                                                                            (local-expand #`(λ (m) (+ m #,n2-name)) 'expression null)
                                                                                                            (local-expand #`(λ (here)
                                                                                                                              (≡ (Nat) (here #,k-name) (+ #,n2-name #,k-name)))
                                                                                                                          'expression null))
                                                                                                   ((assumption 0)
                                                                                                    (repeat (auto))
                                                                                                    apply-reduce
                                                                                                    todo))))
                                                                                  
                                                                                  (then nat-simplify nat-equal-arith (auto)))
                                                                            (then-l (cut 0 (local-expand #`(≡ (Nat)
                                                                                                              (ind-Nat #,k-name #,n2-name (λ (k) (λ (ih) (add1 ih))))
                                                                                                              ((plus #,k-name) #,n2-name))
                                                                                                         'expression null)
                                                                                         'refold)
                                                                                    ((then (unfold-all #'plus)
                                                                                           symmetry
                                                                                           (then-l (cut 0 (local-expand #`(≡ (Π (Nat) (lambda (n) (Nat)))
                                                                                                                             ((λ (n) (λ (m) (ind-Nat n m (λ (k) (λ (ih) (add1 ih)))))) #,k-name)
                                                                                                                             (λ (m) (ind-Nat #,k-name m (λ (k) (λ (ih) (add1 ih))))))
                                                                                                                        'expression
                                                                                                                        null))
                                                                                                   ((then apply-reduce
                                                                                                          λ-equality
                                                                                                          (ind-Nat-equality (local-expand #'(lambda (_) (Nat)) 'expression null))
                                                                                                          (repeat (try (auto) λ-equality add1-equality)))
                                                                                                    (then-l (replace 0
                                                                                                                     (local-expand #'(Π (Nat) (lambda (n) (Nat))) 'expression null)
                                                                                                                     (local-expand #`((λ (n) (λ (m) (ind-Nat n m (λ (k) (λ (ih) (add1 ih))))))
                                                                                                                                      #,k-name)
                                                                                                                                   'expression null)
                                                                                                                     (local-expand #`(λ (m) (ind-Nat #,k-name m (λ (k) (λ (ih) (add1 ih)))))
                                                                                                                                   'expression null)
                                                                                                                     (local-expand #`(lambda (here)
                                                                                                                                       (≡ (Nat)
                                                                                                                                          (here #,n2-name)
                                                                                                                                          (ind-Nat #,k-name #,n2-name
                                                                                                                                                   (λ (k) (λ (ih) (add1 ih))))))
                                                                                                                                   'expression null)
                                                                                                                     )
                                                                                                     ((assumption 0)
                                                                                                      (repeat (auto))
                                                                                                      (then apply-reduce
                                                                                                            (ind-Nat-equality (local-expand #'(lambda (_) (Nat)) 'expression null))
                                                                                                            (repeat (try (auto) λ-equality add1-equality))
                                                                                                            )))))
                                                                                           )
                                                                                     (then-l (replace 0 (local-expand #'(Nat) 'expression null)
                                                                                                      (local-expand #`(ind-Nat #,k-name #,n2-name (λ (k) (λ (ih) (add1 ih)))) 'expression null)
                                                                                                      (local-expand #`((plus #,k-name) #,n2-name) 'expression null)
                                                                                                      (local-expand #`(lambda (here)
                                                                                                                        (≡ (Nat) here (+ #,n2-name #,k-name)))
                                                                                                                    'expression null))
                                                                                             ((assumption 0)
                                                                                              (auto)
                                                                                              (then-l (replace 0
                                                                                                             (local-expand #'(Π (Nat) (λ (n) (Nat))) 'expression null)
                                                                                                             (local-expand #`(plus #,k-name) 'expression null)
                                                                                                             (local-expand #`(another-plus #,k-name) 'expression null)
                                                                                                             (local-expand #`(lambda (here)
                                                                                                                               (≡ (Nat) (here #,n2-name) (+ #,n2-name #,k-name)))
                                                                                                                           'expression null))
                                                                                                      ((assumption 7)
                                                                                                       (repeat (auto))
                                                                                                       (then symmetry
                                                                                                             (unfold-all #'another-plus)
                                                                                                             (then-l (replace 0
                                                                                                                              (local-expand #'(Π (Nat) (lambda (n) (Nat))) 'expression null)
                                                                                                                              (local-expand #`((λ (n) (λ (m) (+ m n))) #,k-name) 'expression null)
                                                                                                                              (local-expand #`(λ (m) (+ m #,k-name)) 'expression null)
                                                                                                                              (local-expand #`(lambda (here)
                                                                                                                                               (≡ (Nat) (+ #,n2-name #,k-name) (here #,n2-name)))
                                                                                                                                            'expression
                                                                                                                                            null))
                                                                                                                     ((then apply-reduce (repeat (auto)))
                                                                                                                      (repeat (auto))
                                                                                                                      (then symmetry apply-reduce nat-equal-arith (auto))))
                                                                                                             (then λ-equality nat-equal-arith (auto))))))))))))))))))))))))))))))))
