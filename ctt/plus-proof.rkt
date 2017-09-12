#lang racket

(require "ctt-core.rkt")
(require "nat.rkt")
(require (for-syntax "../goal.rkt"))
(require (for-syntax racket/list racket/match racket/promise syntax/parse))

(module+ test (require rackunit))

;;;;
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

(define-for-syntax (flip t) (then* symmetry t symmetry))

(define-for-syntax (auto/arith)
  (try* (fail-if-skip nat-simplify)
        (fail-if-skip (flip nat-simplify))
        nat-equal-arith
        (flip nat-equal-arith)
        (ind-Nat-equality (ex #'(lambda (_) (Nat))))
        (flip (ind-Nat-equality (ex #'(lambda (_) (Nat)))))
        (auto)
        (flip (auto))))
  
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
    (with-handlers (#;[exn:fail?
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

(define-for-syntax β*
  (let ([x (try* (β (E (Nat)))
                 (β (E (=> (Nat) (Nat))))
                 (β (E (=> (Nat) (Nat) (Nat)))))])
    (try* x (flip x))))
  
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
(define-for-syntax reduce-either
  (try* apply-reduce (flip apply-reduce)))
(begin-for-syntax
  (define-syntax-rule (with-hyps ([id n] ...) . b)
    (call-with-hypothesis-names
     n ...
     (λ (id ...)
       (with-syntax ([id id] ...) (then . b))))))

;;;;

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

(module+ test
  (check-equal? ((plus 2) 5) 7))

(theorem another-plus
         (=> (Nat) (Nat) (Nat))
         (Π-intro 0 'n)
         (try nat-equality skip)
         (Π-intro 0 'm)
         (try nat-equality skip)
         (then-l
          (nat-intro-arith '+ 2)
          ((assumption 0) (assumption 1))))

(module+ test (check-equal? ((another-plus 2) 5) 7))

(define yet-another-plus
  (run-script #:goal (=> (Nat) (Nat) (Nat))
              (lemma #'plus 'addition)
              (assumption 0)))

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
                   (with-hyps ([k0 2] [n2 0])
                     (auto)
                     (β (E (=> (Nat) (Nat))))
                     (repeat (try apply-reduce (auto/arith))) 
                     (then-l
                      (replace (E (Nat))
                               (E (ind-Nat k0 n2 (λ (k) (λ (ih) (add1 ih)))))
                               (E ((plus k0) n2))
                               (E (λ (here) (≡ (Nat) (+ k0 n2) here))))
                      ((then (unfold-all #'plus)
                             (flip (β (E (=> (Nat) (Nat)))))
                             (repeat (try reduce-either (auto/arith))))
                       (auto)
                       (then (replace (E (=> (Nat) (Nat)))
                                      (E (plus k0))
                                      (E (another-plus k0))
                                      (E (λ (here) (≡ (Nat) (+ k0 n2) (here n2)))))
                             (repeat (auto))
                             (unfold-all #'another-plus)
                             (repeat reduce-either)
                             (flip (β (E (=> (Nat) (Nat)))))
                             (repeat (try reduce-either (auto/arith)))))))))))))
1
