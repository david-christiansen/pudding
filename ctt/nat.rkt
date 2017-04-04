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


(define-for-syntax (ex tm)
  (local-expand tm 'expression null))

(define-syntax (=> stx)
  (syntax-case stx ()
    [(=> S0 T)
     (syntax-property #`(Π S0 (λ (#,(generate-temporary #'x)) T))
                      'original-stx stx)]
    [(=> S0 S ... T)
     (syntax-property #`(Π S0 (λ (#,(generate-temporary #'x)) (=> S ... T)))
                      'original-stx stx)]))

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
             (subgoal (⊢ H (ex #'(≡ (Nat) j k))))])))


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
             (subgoal (⊢ H (ex #'(≡ (Nat) j k))))])))
  
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
                        #,step)])))


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
  
  (theorem plus
           (=> (Nat) (Nat) (Nat))
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
                   ((replace (Π (Nat) (λ (j) (Π (Nat) (λ (k) (Nat))))) #'plus) todo)))
  
  (theorem another-plus
           (=> (Nat) (Nat) (Nat))
           (Π-intro 0 'n)
           (try nat-equality skip)
           (Π-intro 0 'm)
           (try nat-equality skip)
           (then-l
            (nat-intro-arith '+ 2)
            ((assumption 0) (assumption 1))))

  (check-equal? ((another-plus 2) 5) 7)

  (define yet-another-plus
    (run-script #:goal (=> (Nat) (Nat) (Nat))
                (lemma #'plus 'addition)
                (assumption 0)))

  (define-for-syntax (repeat t)
    (try* (then* t
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
         [(_ free-id bound-id ((~and ap #%plain-app) tm ...))
          (syntax/loc stx
            (ap (abstract free-id bound-id tm) ...))]
         [(_ free-id bound-id ((~and lam #%plain-lambda) (x ...) tm ...))
          (syntax/loc stx
            (lam (x ...) (abstract free-id bound-id tm) ...))]
         [(_ free-id bound-id (~and e (quote any))) #'e]
         [(_ free-id bound-id (tm ...))
          (syntax/loc stx
            ((abstract free-id bound-id tm) ...))]
         [(_ _ _ other) #'other]))))

  (define-for-syntax (auto)
    (match-goal*
     ((⊢ H G)
      (syntax-parse G
        #:literal-sets (kernel-literals)
        #:literals (add1 ind-Nat)
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
        [eq:Eq
         #:with p:Pi #'eq.type
         #:with (#%plain-lambda (x:id) body1) #'eq.left
         #:with (#%plain-lambda (y:id) body2) #'eq.right
         λ-equality]
        [eq:Eq
         #:with u:Uni #'eq.type
         #:with n1:Nat-stx #'eq.left
         #:with n2:Nat-stx #'eq.right
         nat-equality]
        [eq:Eq
         #:with (#%plain-app add1 n) #'eq.left
         #:with (#%plain-app add1 m) #'eq.right
         add1-equality]
        [eq:Eq
         #:with (#%plain-app ind-Nat (quote 0) base step) #'eq.left
         ind-Nat-0-reduce]
        [eq:Eq
         #:with (#%plain-app ind-Nat a:id b:id step) #'eq.left
         #:with (#%plain-app ind-Nat a*:id b*:id step*) #'eq.right
         (ind-Nat-equality #'(lambda (_) eq.type))]
        [eq:Eq
         #:with (#%plain-app ind-Nat (quote 0) base step) #'eq.right
         (then* symmetry ind-Nat-0-reduce symmetry)]
        [eq:Eq
         #:with (#%plain-app ind-Nat (#%plain-app add1 k) base step) #'eq.left
         (then-l* (ind-Nat-add1-reduce #'k)
                  ((then* add1-equality (auto))))]
        [eq:Eq
         #:with (#%plain-app ind-Nat (#%plain-app add1 k) base step) #'eq.right
         (then* symmetry
                (then-l* (ind-Nat-add1-reduce #'k)
                         ((then* add1-equality (auto))))
                symmetry)]
        [foo
         ;; No special rules match, so try all the hypotheses then fail
         (let loop ([i 0])
           (if (< i (length H))
               (try* (assumption i)
                     (loop (add1 i)))
               (fail "Can't auto: ~a" (stx->string G))))]))))

  (define-for-syntax (auto/arith)
    (then* (try* nat-simplify skip)
           (try* nat-equal-arith skip)
           ;(try* (ind-Nat-equality (ex #'(lambda (_) (Nat)))) skip)
           (auto)
           symmetry
           (try* nat-simplify skip)
           (try* nat-equal-arith skip)
           ;(try* (ind-Nat-equality (ex #'(lambda (_) (Nat)))) skip)
           (auto)
           symmetry))
  
  (define-for-syntax (call-with-hypothesis-name num tac)
    (match-goal*
     ((⊢ H G)
      #:when (>= (length H) num)
      (tac (hypothesis-id (list-ref H num))))))

  (define-for-syntax (call-with-hypothesis-names . args)
    (match args
      [(list num ... tac)
       (match-goal*
        ((⊢ H G)
         (apply tac
                (for/list ([n num])
                  (hypothesis-id (list-ref H n))))))]
      [_ (fail "Bad call-with-hypothesis-names use")]))

  (define-for-syntax (find-redex stx hole-stx)
    (syntax-parse stx
      #:literal-sets (kernel-literals)
      [(#%plain-apply (#%plain-lambda (x:id) body ) arg)
       (values hole-stx stx (subst1 #'x #'arg #'body))]
      [((~and ap #%plain-apply) f arg)
       (define-values (ctx redex smaller)
         (find-redex #'f hole-stx))
       (values
        (quasisyntax/loc stx
          (ap #,ctx arg))
        redex
        smaller)]
      [g (error (format "Not a redex: ~a" (syntax->datum #'g)))]))

  ;; Inspect the LHS of the goal to find the head beta-redex. Reduce it at the given type, with subgoals being:
  ;;  1. The type is well-formed
  ;;  2. The original goal
  ;;  3. The redex inhabits the type
  (define-for-syntax (β type)
    (match-goal*
     ((⊢ H G)
      (with-handlers ([exn:fail?
                       (lambda (e)
                         (fail "Can't use β here: ~a" (exn-message e)))])
        (syntax-parse G
          #:literal-sets (kernel-literals)
          [eq:Eq
           (define hole #'hole)
           (define-values (ctx redex smaller) (find-redex #'eq.left hole))
           (then-l* (cut 0 (ex #`(≡ #,type #,redex #,smaller)))
                    (apply-reduce
                     (then*
                      (then* (replace type redex smaller (ex #`(lambda (#,hole) (≡ eq.type #,ctx eq.right))))
                             (try* (assumption 0) skip))
                      (thin 0))))]
          [_ (fail "Can't β")])))))
  
  (define-for-syntax (unfold-all id . ids)
    (then* (unfold id)
           (match-goal*
            ((⊢ (cons (hyp _ t _) H) G)
             (syntax-parse t
               [eq:Eq
                (let ([context (with-syntax ([G G] [id id])
                                 (ex #'(lambda (x) (abstract id x G))))])
                  (then-l* (replace #'eq.type #'eq.left #'eq.right context)
                           ((assumption 0)
                            (repeat (auto)))))])))
           (thin 0)
           (if (null? ids)
               skip
               (apply unfold-all ids))))

  (define-for-syntax reduce-both
    (then* apply-reduce symmetry apply-reduce symmetry))

  (define-syntax-rule (with-hyps ([id n] ...) . b)
    (call-with-hypothesis-names
     n ...
     (λ (id ...)
       (with-syntax ([id id] ...) . b))))
  
  ;; TODO: requires rewriting with an equality and axiomatization of +, ind-Nat's op-sem
  (theorem plus-is-plus
           (≡ (=> (Nat) (Nat) (Nat)) plus another-plus)
           (then-l
            ;; Proof is by function extensionality.
            (extensionality 'an-arg)
            ;; Three subgoals: show that the LHS has the type, that the RHS has the type, and that
            ;; they are pointwise equal for well-typed input.
            ((then (unfold-all #'plus) (repeat (auto/arith)))
             (then (unfold-all #'another-plus) (repeat (auto/arith)))
             ;; Pointwise equality.
             (then-l
              ;; By induction. In each subgoal of the induction, replace the functions with their
              ;; definitions.
              (then (nat-elim 0)
                    (unfold-all #'plus #'another-plus))
              ;; 0 case: reduce both sides, and then use simple arithmetic.
              ((then reduce-both (repeat (auto/arith)))
               ;; Successor case.
               (then reduce-both
                     (auto)
                     
                     (call-with-hypothesis-names
                      2 0
                      (lambda (k-name n2-name)
                        (then (auto)
                              (β (ex #'(=> (Nat) (Nat))))
                              (repeat (try apply-reduce (auto/arith)))
                              (then-l (cut 0 (ex #`(≡ (Nat)
                                                      (+ #,n2-name #,k-name)
                                                      ((another-plus #,n2-name) #,k-name))))
                                      ((then (unfold-all #'another-plus)
                                             symmetry
                                             (β (ex #'(=> (Nat) (Nat))))
                                             (repeat (try apply-reduce (auto/arith))))
                                       (then
                                        nat-simplify
                                        nat-equal-arith
                                        (try (auto/arith) skip)
                                        (then-l (cut 0 (ex #`(≡ (Nat)
                                                               (ind-Nat #,k-name #,n2-name (λ (k) (λ (ih) (add1 ih))))
                                                               ((plus #,k-name) #,n2-name)))
                                                    'refold)
                                               ((then (unfold-all #'plus)
                                                      symmetry
                                                      (β (ex #`(=> (Nat) (Nat))))
                                                      (repeat (try apply-reduce (auto))))
                                                (then
                                                 (replace (ex #'(Nat))
                                                               (ex #`(ind-Nat #,k-name #,n2-name (λ (k) (λ (ih) (add1 ih)))))
                                                               (ex #`((plus #,k-name) #,n2-name))
                                                               (ex #`(lambda (here)
                                                                       (≡ (Nat) (+ #,k-name #,n2-name) here))))
                                                      (try (auto)
                                                           (then (replace (ex #'(=> (Nat) (Nat)))
                                                                          (ex #`(plus #,k-name))
                                                                          (ex #`(another-plus #,k-name))
                                                                          (ex #`(lambda (here)
                                                                                  (≡ (Nat) (+ #,k-name #,n2-name) (here #,n2-name)))))
                                                                 (repeat (auto))
                                                                 (unfold-all #'another-plus)
                                                                 (try apply-reduce skip)
                                                                 symmetry
                                                                 (β (ex #'(=> (Nat) (Nat))))
                                                                 (try apply-reduce skip)
                                                                 (repeat (auto/arith))))))))))))))))))))




























