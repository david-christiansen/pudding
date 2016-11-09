#lang racket

(require "lcfish.rkt"
         racket/stxparam
         (for-syntax racket/list
                     racket/match
                     racket/port
                     racket/set
                     racket/stxparam
                     syntax/id-set
                     syntax/id-table
                     syntax/kerncase
                     syntax/parse
                     "stx-utils.rkt")
         (for-syntax (for-syntax racket/base syntax/parse)))

(module+ test (require rackunit))

(begin-for-syntax
  (struct hyp (name type visible?) #:transparent)
  (struct ⊢ (hyps goal) #:transparent)

  (define (get-goal stx)
    (leftmost (syntax-property stx 'goal)))

  (define (set-goal stx goal)
    (syntax-property stx 'goal goal))

  (define (dump-goal stx)
    (match-define (⊢ H G) (if (syntax? stx)
                              (get-goal stx)
                              stx))
    (for/list ([h (reverse H)]
               [i (in-range (length H) 0 -1)])
      (match h
        [(hyp x t visible?)
         (if visible?
             (printf "~a. [~a : ~a]\n" (sub1 i) (syntax-e x) (syntax->datum (unexpand t)))
             (printf "~a. ~a : ~a\n" (sub1 i) (syntax-e x) (syntax->datum (unexpand t))))]))
    (printf "⊢ ~a\n\n" (syntax->datum (unexpand G))))

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
     (match (get-goal hole-stx)
       [(? ⊢? g)
        (define goal (with-output-to-string
                         (lambda ()
                           (dump-goal g))))
        (log-message online-check-syntax-logger
                     'info
                     goal
                     (list (syntax-property #'(void)
                                            'mouse-over-tooltips
                                            (vector where
                                                    (syntax-position where)
                                                    (+ (syntax-position where)
                                                       (syntax-span where))
                                                    (format "~a:\n~a"
                                                            (syntax->datum where)
                                                            goal)))))]
       [_ (void)]))))




;
;
;
;    ;;;;;                         ;;;;                    ;;
;    ;;;;;;                        ;;;;                    ;;
;    ;;   ;;                         ;;                    ;;
;    ;;   ;;   ;; ;;;     ;;;        ;;     ;;   ;;    ;;; ;;     ;;;
;    ;;   ;;   ;;;;;;;   ;;;;;       ;;     ;;   ;;    ;;;;;;    ;;;;;
;    ;;   ;;   ;;;  ;   ;;   ;;      ;;     ;;   ;;   ;;  ;;;   ;;   ;;
;    ;;;;;;    ;;       ;;   ;;      ;;     ;;   ;;   ;;   ;;   ;;   ;;
;    ;;;;;     ;;       ;;;;;;;      ;;     ;;   ;;   ;;   ;;   ;;;;;;;
;    ;;        ;;       ;;;;;;;      ;;     ;;   ;;   ;;   ;;   ;;;;;;;
;    ;;        ;;       ;;           ;;     ;;   ;;   ;;   ;;   ;;
;    ;;        ;;       ;;           ;;     ;;   ;;   ;;   ;;   ;;
;    ;;        ;;       ;;;  ;       ;;     ;;  ;;;   ;;  ;;;   ;;;  ;
;    ;;        ;;        ;;;;;;   ;;;;;;;   ;;;;;;;    ;;;;;;    ;;;;;;
;    ;;        ;;         ;;;;    ;;;;;;;    ;;; ;;    ;;; ;;     ;;;;
;
;
;


(struct U (level) #:transparent)
(struct Nat () #:transparent)
(struct Absurd () #:transparent)
(struct Listof (element-type) #:transparent)
(struct Π (domain codomain) #:transparent)
(struct ≡ (type left right) #:transparent)

;; TODO: Missing types here are Int (replacing Nat), Less, Set, Quotient, Union, Product

(define (ind-Nat target base step)
  (if (zero? target)
      base
      (step (ind-Nat (sub1 target) base step))))


;
;
;
;     ;;;;;                         ;;
;    ;;;;;;;                        ;;
;    ;;   ;                         ;;
;    ;;       ;;    ;;  ;; ;;;    ;;;;;;;    ;;;;     ;;    ;;
;    ;;;      ;;    ;;  ;;;;;;;   ;;;;;;;   ;;;;;;    ;;    ;;
;     ;;;     ;;    ;;  ;;;  ;;     ;;      ;;   ;;    ;;  ;;
;      ;;;     ;;  ;;   ;;   ;;     ;;           ;;     ;;;;
;       ;;;    ;;  ;;   ;;   ;;     ;;        ;;;;;     ;;;;
;        ;;;    ;  ;;   ;;   ;;     ;;       ;;;;;;      ;;
;         ;;    ;;;;    ;;   ;;     ;;      ;;   ;;     ;;;;
;    ;    ;;     ;;;    ;;   ;;     ;;      ;;   ;;    ;;;;;;
;   ;;;  ;;;     ;;;    ;;   ;;     ;;  ;   ;;   ;;    ;;  ;;
;    ;;;;;;      ;;     ;;   ;;     ;;;;;;  ;;;;;;;   ;;    ;;
;     ;;;;       ;;     ;;   ;;      ;;;;    ;;; ;;   ;;    ;;
;               ;;
;               ;;
;               ;;


;; The arguments should be:
;;  1. bound-id-table mapping bound identifiers to new syntax objects
;;  2. The syntax object within which to substitute (only supporting some core forms right now)
(define-for-syntax ((subst* to-subst) stx)
  (kernel-syntax-case stx #f
    [(quote e) #'(quote e)]
    [x (identifier? #'x)
       (let ([val (bound-id-table-ref to-subst #'x #f)])
         (if val val #'x))]
    [(#%plain-app e ...)
     #`(#%plain-app #,@(map (subst* to-subst) (syntax-e #'(e ...))))]
    [(#%plain-lambda (arg ...) body ...)
     #`(#%plain-lambda (arg ...) #,@(map (subst* to-subst) (syntax-e #'(body ...))))]
    [other (error (format "rename-bound: Unsupported syntax: ~a" (syntax->datum #'other)))]))

(define-for-syntax (subst to-subst stx) ((subst* to-subst) stx))

;; Arguments:
;;  ctxt - a set of bound variables
;;  stx1, stx2 - objectx to compare
(define-for-syntax (α-equiv? ctxt stx1 stx2)
  (kernel-syntax-case #`(#,stx1 #,stx2) #f
    [((quote e1) (quote e2))
     (equal? (syntax->datum #'e1) (syntax->datum #'e2))]
    [(x1 x2)
     (and (identifier? #'x1) (identifier? #'x2))
     (begin
       (cond
         [(set-member? ctxt #'x1)
          (bound-identifier=? #'x1 #'x2)]
         [(set-member? ctxt #'x2)
          #f]
         [else (free-identifier=? #'x1 #'x2)]))]
    [((#%plain-app e1 ...) (#%plain-app e2 ...))
     (let ([l1 (syntax-e #'(e1 ...))]
           [l2 (syntax-e #'(e2 ...))])
       (and (= (length l1) (length l2))
            (andmap (lambda (x y) (α-equiv? ctxt x y)) l1 l2)))]
    [((#%plain-lambda (arg1 ...) body1 ...) (#%plain-lambda (arg2 ...) body2 ...))
     (let ([arglist1 (syntax-e #'(arg1 ...))]
           [arglist2 (syntax-e #'(arg2 ...))]
           [body-list1 (syntax-e #'(body1 ...))]
           [body-list2 (syntax-e #'(body2 ...))])
       (if (and (= (length arglist1) (length arglist2)))
           (let ([substitution (make-immutable-bound-id-table (map cons arglist2 arglist1))])
             (andmap (lambda (b1 b2)
                       (α-equiv? (bound-id-set-union ctxt (immutable-bound-id-set arglist1))
                                 b1 (subst substitution b2)))
                     body-list1
                     body-list2))
           #f))]))



(define-syntax (run-script stx)
  (syntax-parse stx
    [(run-script #:goal g tactic ...)
     #`(syntax-parameterize ([tactic-debug-hook #,dump-goal])
         (define-syntax (go s)
           (parameterize ([current-tactic-location #'#,stx])
             (set-goal (hole-with-tactic (then tactic ...))
                       (⊢ null (local-expand #'g 'expression null)))))
         (go))]))

(define-for-syntax (constructs? struct-type-name identifier)
  ;; this seems wrong, but the struct transformer binding's notion of constructor is not
  ;; the right thing here...
  (free-identifier=? (syntax-property identifier 'constructor-for)
                     struct-type-name))

(begin-for-syntax
  (define-syntax-class Uni
    #:literal-sets (kernel-literals)
    #:attributes (level)
    (pattern (#%plain-app u:id (quote i))
             #:when (and (constructs? #'U #'u)
                         (exact-nonnegative-integer? (syntax-e #'i)))
             #:with level (syntax-e #'i)))

  (define-syntax-class Eq
    #:literal-sets (kernel-literals)
    #:attributes (type left right)
    (pattern (#%plain-app eq:id type right left)
             #:when (constructs? #'≡ #'eq)))

  (define-syntax-class Abs
    #:literal-sets (kernel-literals)
    #:attributes ()
    (pattern (#%plain-app abs:id)
             #:when (constructs? #'Absurd #'abs))))


(define-for-syntax (todo hole make-hole)
  ((fail (with-output-to-string (lambda () (dump-goal (get-goal hole)))))
   hole make-hole))

;; For showing error messages etc
(define-for-syntax (unexpand stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [u:Uni
     #'(U u.level)]
    [eq:Eq
     #`(≡ #,(unexpand #'eq.type) #,(unexpand #'eq.left) #,(unexpand #'eq.right))]
    [(#%plain-app e ...)
     (datum->syntax stx (map unexpand (syntax->list #'(e ...))))]
    [(#%plain-lambda (x ...) e ...)
     #`(λ (x ...)
         #,(datum->syntax #'(e ...) (map unexpand (syntax->list #'(e ...)))))]
    [other #'other]))

;
;
;
;    ;;;;;               ;;;;                          ;;;;;                 ;;;;
;    ;;;;;;              ;;;;                          ;;;;;;               ;;;;;;
;    ;;   ;;               ;;                          ;;  ;;               ;;  ;
;    ;;   ;;  ;;   ;;      ;;       ;;;                ;;   ;;    ;;;       ;;      ;; ;;;
;    ;;   ;;  ;;   ;;      ;;      ;;;;;               ;;   ;;   ;;;;;    ;;;;;;;   ;;;;;;;
;    ;;   ;;  ;;   ;;      ;;     ;;   ;;              ;;   ;;  ;;   ;;   ;;;;;;;   ;;;  ;;
;    ;;;;;;   ;;   ;;      ;;     ;;   ;;              ;;   ;;  ;;   ;;     ;;      ;;   ;;
;    ;;;;;    ;;   ;;      ;;     ;;;;;;;              ;;   ;;  ;;;;;;;     ;;      ;;   ;;
;    ;;  ;;   ;;   ;;      ;;     ;;;;;;;              ;;   ;;  ;;;;;;;     ;;      ;;   ;;
;    ;;  ;;   ;;   ;;      ;;     ;;                   ;;   ;;  ;;          ;;      ;;   ;;
;    ;;  ;;;  ;;   ;;      ;;     ;;                   ;;   ;;  ;;          ;;      ;;   ;;
;    ;;   ;;  ;;  ;;;      ;;     ;;;  ;               ;;  ;;   ;;;  ;      ;;      ;;   ;;
;    ;;   ;;  ;;;;;;;   ;;;;;;;    ;;;;;;              ;;;;;;    ;;;;;;     ;;      ;;   ;;
;    ;;   ;;   ;;; ;;   ;;;;;;;     ;;;;               ;;;;;      ;;;;      ;;      ;;   ;;
;
;
;

(begin-for-syntax
  (define-syntax-parameter subgoal
    (lambda (_) (raise-syntax-error 'subgoal "Not in a rule")))

  ;; TODO: find the right name here
  (define-syntax-parameter not-applicable
    (lambda (_) (raise-syntax-error 'not-applicable "Not in a rule")))

  (define-syntax (rule stx)
    (syntax-parse stx
      [(_ goal-pat #:when condition result ...+)
       (syntax/loc stx
         (lambda (hole make-hole)
           ((tactic-info-hook) hole)
           (struct exn:fail:this-rule exn:fail ()
             #:extra-constructor-name make-exn:fail:this-rule)
           (define (make-subgoal g)
             (set-goal (make-hole) g))
           (syntax-parameterize ([subgoal (make-rename-transformer #'make-subgoal)]
                                 [not-applicable
                                  (lambda (nope-stx)
                                    (syntax-case nope-stx ()
                                      [(_ msg)
                                       #'(raise (make-exn:fail:this-rule
                                                 msg
                                                 (current-continuation-marks)))]
                                      [(_)
                                       #'(raise (make-exn:fail:this-rule
                                                 (string-append
                                                  "Not applicable at goal:\n"
                                                  (with-output-to-string
                                                      (lambda ()
                                                        (dump-goal (get-goal hole)))))
                                                 (current-continuation-marks)))]))])
             (with-handlers ([exn:fail:this-rule?
                              (lambda (e)
                                ((fail (exn-message e)) hole make-hole))])
               (match (get-goal hole)
                 [goal-pat #:when condition result ...]
                 [other ((fail (string-append "Wrong goal:\n"
                                              (with-output-to-string
                                                  (lambda () (dump-goal other)))))
                         hole make-hole)])))))]
      [(_ goal-pat result ...+)
       (syntax/loc stx
         (rule goal-pat #:when #t result ...))]))

  (define ((guard-goal pred tac) hole make-hole)
    (match (get-goal hole)
      [#f ((fail "No goal found.") hole make-hole)]
      [g #:when (pred g)
         ((tactic-info-hook) hole)
         (tac hole make-hole)]
      [g ((fail (string-append "Wrong goal:\n" (with-output-to-string (lambda () (dump-goal g)))))
          hole make-hole)]))

  (define emit-void (emit #'(void))))



;
;
;                ;;
;   ;;   ;;      ;;                                    ;;;;;               ;;;;
;   ;;   ;;                                            ;;;;;;              ;;;;
;   ;;; ;;;                                            ;;   ;;               ;;
;   ;;; ;;;    ;;;;       ;;;;       ;;;               ;;   ;;  ;;   ;;      ;;       ;;;       ;;;;
;   ;;; ;;;    ;;;;     ;;;;;;;     ;;;;;;             ;;   ;;  ;;   ;;      ;;      ;;;;;    ;;;;;;;
;   ;;;; ;;      ;;     ;;   ;     ;;;  ;              ;;   ;;  ;;   ;;      ;;     ;;   ;;   ;;   ;
;   ;; ; ;;      ;;     ;;         ;;                  ;;;;;;   ;;   ;;      ;;     ;;   ;;   ;;
;   ;; ; ;;      ;;     ;;;;       ;;                  ;;;;;    ;;   ;;      ;;     ;;;;;;;   ;;;;
;   ;;   ;;      ;;      ;;;;;     ;;                  ;;  ;;   ;;   ;;      ;;     ;;;;;;;    ;;;;;
;   ;;   ;;      ;;        ;;;;    ;;                  ;;  ;;   ;;   ;;      ;;     ;;           ;;;;
;   ;;   ;;      ;;          ;;    ;;                  ;;  ;;;  ;;   ;;      ;;     ;;             ;;
;   ;;   ;;      ;;     ;;   ;;    ;;;  ;              ;;   ;;  ;;  ;;;      ;;     ;;;  ;    ;;   ;;
;   ;;   ;;   ;;;;;;;;  ;;;;;;;     ;;;;;;             ;;   ;;  ;;;;;;;   ;;;;;;;    ;;;;;;   ;;;;;;;
;   ;;   ;;   ;;;;;;;;   ;;;;;       ;;;               ;;   ;;   ;;; ;;   ;;;;;;;     ;;;;     ;;;;;
;
;
;



(begin-for-syntax
  (define-match-expander at-hyp
    (lambda (stx)
      (syntax-case stx ()
        [(_ i before this-hyp after)
         #'(? (lambda (H) (> (length H) i))
              (app (lambda (H) (split-at H i))
                   before
                   (cons this-hyp after)))])))

  (define (assumption n)
    (rule (⊢ H G)
          (define assumptions (length H))
          (cond
            [(not (exact-nonnegative-integer? n))
             (not-applicable (format "Bad assumption number ~a" n))]
            [(>= n assumptions)
             (not-applicable
              (format "Assumption ~a requested, but there are only ~a" n assumptions))]
            [else
             (match-define (at-hyp n Δ (hyp x ty hidden?) Γ) H)
             (cond
               [hidden?
                (not-applicable (format "Assumption ~a is hidden" n))]
               [(α-equiv? (immutable-bound-id-set (map hyp-type Γ))
                          ty
                          G)
                x]
               [else (not-applicable (format "Mismatched assumption ~a. Expected ~a, got ~a"
                                             n
                                             G
                                             ty))])]))))

;
;
;                          ;;
;   ;;   ;;                ;;
;   ;;   ;;
;   ;;   ;;
;   ;;   ;;   ;; ;;;     ;;;;     ;;    ;;    ;;;      ;; ;;;     ;;;;      ;;;
;   ;;   ;;   ;;;;;;;    ;;;;     ;;    ;;   ;;;;;     ;;;;;;;  ;;;;;;;    ;;;;;
;   ;;   ;;   ;;;  ;;      ;;     ;;    ;;  ;;   ;;    ;;;  ;   ;;   ;    ;;   ;;
;   ;;   ;;   ;;   ;;      ;;     ;;    ;;  ;;   ;;    ;;       ;;        ;;   ;;
;   ;;   ;;   ;;   ;;      ;;      ;;  ;;   ;;;;;;;    ;;       ;;;;      ;;;;;;;
;   ;;   ;;   ;;   ;;      ;;      ;;  ;;   ;;;;;;;    ;;        ;;;;;    ;;;;;;;
;   ;;   ;;   ;;   ;;      ;;      ;;  ;;   ;;         ;;          ;;;;   ;;
;   ;;   ;;   ;;   ;;      ;;       ;  ;    ;;         ;;            ;;   ;;
;   ;;   ;;   ;;   ;;      ;;       ;;;;    ;;;  ;     ;;       ;;   ;;   ;;;  ;
;    ;;;;;    ;;   ;;   ;;;;;;;;    ;;;;     ;;;;;;    ;;       ;;;;;;;    ;;;;;;
;     ;;;     ;;   ;;   ;;;;;;;;     ;;       ;;;;     ;;        ;;;;;      ;;;;
;
;
;

(begin-for-syntax
  (define (intro-universe i)
    (if (exact-nonnegative-integer? i)
        (guard-goal (lambda (g)
                      (match-define (⊢ H G) g)
                      (syntax-parse G
                        [u:Uni
                         (> (syntax-e (attribute u.level)) i)]
                        [_ #f]))
                    (emit (with-syntax ([i i])
                            #'(U i))))
        (fail (format "Not a universe level: ~a" i))))

  (define equal-universe
    (guard-goal (match-lambda
                  [(⊢ H G)
                   (syntax-parse G
                     #:literal-sets (kernel-literals)
                     [eq:Eq
                      #:with u1:Uni #'eq.type
                      #:with u2:Uni #'eq.left
                      #:with u3:Uni #'eq.right
                      (and (< (syntax-e (attribute u2.level))
                              (syntax-e (attribute u1.level)))
                           (= (syntax-e (attribute u2.level))
                              (syntax-e (attribute u3.level))))]
                     [_ #f])]
                  [_ #f])
                emit-void)))

(module+ test
  (define u2
    (run-script #:goal (U 5)
                (intro-universe 2)))
  (check-equal? u2 (U 2))
  (define yep
    (run-script #:goal (≡ (U 5) (U 2) (U 2))
                equal-universe))
  (check-equal? yep (void)))


;
;
;                                                        ;;
;    ;;;;;;                                  ;;;;        ;;       ;;
;    ;;;;;;                                  ;;;;                 ;;
;    ;;                                        ;;                 ;;
;    ;;        ;;; ;;   ;;   ;;    ;;;;        ;;      ;;;;     ;;;;;;;   ;;    ;;
;    ;;        ;;;;;;   ;;   ;;   ;;;;;;       ;;      ;;;;     ;;;;;;;   ;;    ;;
;    ;;;;;    ;;  ;;;   ;;   ;;   ;;   ;;      ;;        ;;       ;;      ;;    ;;
;    ;;;;;    ;;   ;;   ;;   ;;        ;;      ;;        ;;       ;;       ;;  ;;
;    ;;       ;;   ;;   ;;   ;;     ;;;;;      ;;        ;;       ;;       ;;  ;;
;    ;;       ;;   ;;   ;;   ;;    ;;;;;;      ;;        ;;       ;;        ;  ;;
;    ;;       ;;   ;;   ;;   ;;   ;;   ;;      ;;        ;;       ;;        ;;;;
;    ;;       ;;   ;;   ;;   ;;   ;;   ;;      ;;        ;;       ;;         ;;;
;    ;;       ;;  ;;;   ;;  ;;;   ;;   ;;      ;;        ;;       ;;  ;      ;;;
;    ;;;;;;    ;;;;;;   ;;;;;;;   ;;;;;;;   ;;;;;;;   ;;;;;;;;    ;;;;;;     ;;
;    ;;;;;;    ;;; ;;    ;;; ;;    ;;; ;;   ;;;;;;;   ;;;;;;;;     ;;;;      ;;
;                  ;;                                                       ;;
;                  ;;                                                       ;;
;                  ;;                                                       ;;


(begin-for-syntax
  ;; This really needs dependent refinement!
  (define (equality-formation A)
    (rule (⊢ H G)
          (syntax-parse G
            [u:Uni
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #`(≡ u #,A #,A) 'expression null)))
                (≡ #,A
                   #,(subgoal (⊢ H A))
                   #,(subgoal (⊢ H A))))]
            [other (not-applicable)])))
  (define equality-equality
    (rule (⊢ H G)
          (syntax-parse G
            [eq:Eq
             #:with u:Uni #'eq.type
             #:with inner1:Eq #'eq.left
             #:with inner2:Eq #'eq.right
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #'(≡ u inner1.type inner2.type)
                                              'expression
                                              null)))
                #,(subgoal (⊢ H (local-expand #'(≡ inner1.type inner1.left inner2.left)
                                              'expression
                                              null)))
                #,(subgoal (⊢ H (local-expand #'(≡ inner1.type inner1.right inner2.right)
                                              'expression
                                              null)))
                (void))]
            [_ (not-applicable)])))

  (define equality-identity
    (rule (⊢ H G)
          (syntax-parse G
            #:literals (void)
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with (#%plain-app void) #'eq.left
             #:with (#%plain-app void) #'eq.right
             #:with (~and todo eq2:Eq) #'eq.type
             (subgoal (⊢ H #'eq2))]
            [_ (not-applicable)])))

  (define (assumption-refl n)
    (rule (⊢ H G)
          (define assumptions (length H))
          (cond
            [(not (exact-nonnegative-integer? n))
             (not-applicable (format "Bad assumption number ~a" n))]
            [(>= n assumptions)
             (not-applicable (format "Assumption ~a requested, but there are only ~a" n assumptions))]
            [else
             ;; Hiddenness is ignored, because this extract is always trivial.
             (match-define (at-hyp n Δ (hyp x ty _) Γ)
               H)
             (syntax-parse G
               #:literal-sets (kernel-literals)
               [(#%plain-app eq in-ty h1 h2)
                #:when (and (constructs? #'≡ #'eq)
                            ;; TODO: this doesn't give the expected answer with bound-id=?,
                            ;; but this may also be wrong. Think about it, and ask Sam.
                            (free-identifier=? x #'h1)
                            (free-identifier=? x #'h2)
                            (let ([Γ-ids (immutable-bound-id-set (map hyp-type Γ))])
                              (α-equiv? Γ-ids #'in-ty ty)))
                #'(void)]
               [_ (not-applicable (format "Assumption/goal mismatch ~a. Expected ~a, got ~a."
                                          n
                                          (syntax->datum
                                           (local-expand #`(≡ #,ty #,x #,x) 'expression null))
                                          (syntax->datum G)))])]))))


(module+ test
  (define U1≡U0
    (run-script #:goal (U 3)
                (then-l (equality-formation (local-expand #'(U 2) 'expression null))
                        (equal-universe
                         (intro-universe 1)
                         (intro-universe 0)))))
  (check-equal? U1≡U0 (≡ (U 2) (U 1) (U 0)))

  (define an-eq-eq
    (run-script #:goal (≡ (U 2)
                          (≡ (U 1) (U 0) (U 0))
                          (≡ (U 1) (U 0) (U 0)))
                equality-equality
                equal-universe))
  (check-true (void? an-eq-eq)))

;
;
;                                                        ;;
;    ;;;;;;;                                  ;;         ;;
;    ;;;;;;;                                  ;;
;    ;;                                       ;;
;    ;;       ;;   ;;   ;; ;;;       ;;;    ;;;;;;;    ;;;;       ;;;     ;; ;;;      ;;;;
;    ;;       ;;   ;;   ;;;;;;;     ;;;;;;  ;;;;;;;    ;;;;      ;;;;;    ;;;;;;;   ;;;;;;;
;    ;;;;;;   ;;   ;;   ;;;  ;;    ;;;  ;     ;;         ;;     ;;; ;;;   ;;;  ;;   ;;   ;
;    ;;;;;;   ;;   ;;   ;;   ;;    ;;         ;;         ;;     ;;   ;;   ;;   ;;   ;;
;    ;;       ;;   ;;   ;;   ;;    ;;         ;;         ;;     ;;   ;;   ;;   ;;   ;;;;
;    ;;       ;;   ;;   ;;   ;;    ;;         ;;         ;;     ;;   ;;   ;;   ;;    ;;;;;
;    ;;       ;;   ;;   ;;   ;;    ;;         ;;         ;;     ;;   ;;   ;;   ;;      ;;;;
;    ;;       ;;   ;;   ;;   ;;    ;;         ;;         ;;     ;;   ;;   ;;   ;;        ;;
;    ;;       ;;  ;;;   ;;   ;;    ;;;  ;     ;;  ;      ;;     ;;; ;;;   ;;   ;;   ;;   ;;
;    ;;       ;;;;;;;   ;;   ;;     ;;;;;;    ;;;;;;  ;;;;;;;;   ;;;;;    ;;   ;;   ;;;;;;;
;    ;;        ;;; ;;   ;;   ;;      ;;;       ;;;;   ;;;;;;;;    ;;;     ;;   ;;    ;;;;;
;
;
;


;; Function rules

;; For trampolining through the macro expander to get the right scopes.
;; Communicates with make-assumption-hole and →-intro.
(define-syntax (assumption-hole stx)
  (define make-next (syntax-property stx 'next-hole))
  (define goal-maker (syntax-property stx 'goal-maker))
  (define params (syntax-property stx 'params))
  (syntax-case stx ()
    [(_ x)
     (call-with-parameterization
      params
      (lambda ()
        (make-next (goal-maker #'x))))]))

(define-for-syntax (make-assumption-hole next-hole x goal-maker)
  (syntax-property
   (syntax-property
    (syntax-property #`(assumption-hole #,x)
                     'goal-maker
                     goal-maker)
    'next-hole next-hole)
   'params (current-parameterization)))

(define-syntax (side-conditions stx)
  (syntax-parse stx
    [(_ condition ... result)
     (for ([c (syntax->list #'(condition ...))])
       (local-expand c 'expression null))
     #'result]))

(begin-for-syntax
  (define (Π-formation x dom)
    (rule (⊢ H G)
          (syntax-parse G
            [u:Uni
             (define dom-ok
               (subgoal (⊢ H (local-expand #`(≡ u #,dom #,dom) 'expression null))))
             #`(side-conditions
                #,dom-ok
                (Π #,dom
                   (λ (#,x) #,(make-assumption-hole (lambda (g) (subgoal g))
                                                    x
                                                    (lambda (good-x)
                                                      (⊢ (cons (hyp good-x dom #f) H)
                                                         G))))))]
            [_ (not-applicable)])))

  (define (Π-in-uni (new-var (gensym 'y)))
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [(#%plain-app eq
                          u:Uni
                          (#%plain-app pi1 a (#%plain-lambda (x) c))
                          (#%plain-app pi2 b (#%plain-lambda (y) d)))
             #:when (and (constructs? #'Π #'pi1)
                         (constructs? #'Π #'pi2))
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #`(≡ u a b) 'expression null)))
                (λ (#,new-var)
                  #,(make-assumption-hole (lambda (g) (subgoal g))
                                          new-var
                                          (lambda (good-var)
                                            (⊢ (cons (hyp good-var #'a #f) H)
                                               (let ([renamed-c (subst (make-bound-id-table
                                                                        (list (cons #'x good-var)))
                                                                       #'c)]
                                                     [renamed-d (subst (make-bound-id-table
                                                                        (list (cons #'y good-var)))
                                                                       #'d)])
                                                 (local-expand #`(≡ u #,renamed-c #,renamed-d)
                                                               'expression
                                                               null))))))
                (void))]
            [_ (not-applicable)])))

  (define (Π-intro i (var #f))
    (if (exact-nonnegative-integer? i)
        (rule (⊢ H G)
              (syntax-parse G
                #:literal-sets (kernel-literals)
                [(#%plain-app pi dom (#%plain-lambda (x:id) cod))
                 #:when (constructs? #'Π #'pi)
                 (define y (if (symbol? var) var (syntax-e #'x)))
                 #`(side-conditions
                    #,(subgoal (⊢ H (local-expand #`(≡ (U #,i) dom dom)
                                                  'expression
                                                  null)))
                    (λ (#,y)
                      #,(make-assumption-hole (lambda (g) (subgoal g))
                                              y
                                              (lambda (the-var)
                                                (⊢ (cons (hyp the-var #'dom #f) H)
                                                   (subst (make-bound-id-table
                                                           (list (cons #'x the-var)))
                                                          #'cod))))))]
                [_ (not-applicable)]))
        (fail (format "Π-intro: not a valid level: ~a" i))))

  )

(module+ test
  (define U1→U1
    (run-script #:goal (U 2)
                (then-l
                 (Π-formation 'x #'(U 1))
                 (equal-universe (intro-universe 1)))))
  (check-true (Π? U1→U1))
  (check-equal? (Π-domain U1→U1) (U 1))
  (check-equal? ((Π-codomain U1→U1) "any-old-thing") (U 1))

  (define U1→U1:U2
    (run-script #:goal (≡ (U 2)
                          (Π (U 1) (λ (_) (U 1)))
                          (Π (U 1) (λ (_) (U 1))))
                (then-l (Π-in-uni 'y)
                        (equal-universe equal-universe))))
  (check-true (void? U1→U1:U2))

  (define U1-identity
    (run-script #:goal (Π (U 1) (λ (_) (U 1)))
                (then-l (Π-intro 2 'some-uni)
                        (equal-universe (assumption 0)))))
  (check-true (procedure? U1-identity))
  (check-equal? (U1-identity (Nat)) (Nat))

  (define U1-refl
    (run-script #:goal (Π (U 2) (λ (ty) (≡ (U 2) ty ty)))
                (then-l (Π-intro 3 't)
                        (equal-universe (assumption-refl 0)))))
  (check-true (procedure? U1-refl))
  (check-equal? (U1-refl (Nat)) (void))

  (define U1-refl-proof
    (run-script #:goal (≡ (≡ (U 2) (U 1) (U 1)) (void) (void))
                equality-identity
                equal-universe))
  )



;
;
;                                                                  ;;
;      ;;      ;;                                          ;;      ;;       ;;
;      ;;      ;;                                          ;;               ;;
;     ;;;;     ;;                                          ;;               ;;
;     ;;;;     ;; ;;;     ;;;;    ;;   ;;    ;; ;;;    ;;; ;;    ;;;;     ;;;;;;;   ;;    ;;
;     ;;;;     ;;;;;;   ;;;;;;;   ;;   ;;    ;;;;;;;   ;;;;;;    ;;;;     ;;;;;;;   ;;    ;;
;     ;  ;     ;;;  ;;  ;;   ;    ;;   ;;    ;;;  ;   ;;  ;;;      ;;       ;;      ;;    ;;
;    ;;  ;;    ;;   ;;  ;;        ;;   ;;    ;;       ;;   ;;      ;;       ;;       ;;  ;;
;    ;;  ;;    ;;   ;;  ;;;;      ;;   ;;    ;;       ;;   ;;      ;;       ;;       ;;  ;;
;    ;;  ;;    ;;   ;;   ;;;;;    ;;   ;;    ;;       ;;   ;;      ;;       ;;        ;  ;;
;    ;;;;;;    ;;   ;;     ;;;;   ;;   ;;    ;;       ;;   ;;      ;;       ;;        ;;;;
;   ;;;;;;;;   ;;   ;;       ;;   ;;   ;;    ;;       ;;   ;;      ;;       ;;         ;;;
;   ;;    ;;   ;;;  ;;  ;;   ;;   ;;  ;;;    ;;       ;;  ;;;      ;;       ;;  ;      ;;;
;   ;;    ;;   ;;;;;;   ;;;;;;;   ;;;;;;;    ;;        ;;;;;;   ;;;;;;;;    ;;;;;;     ;;
;   ;;    ;;   ;; ;;;    ;;;;;     ;;; ;;    ;;        ;;; ;;   ;;;;;;;;     ;;;;      ;;
;                                                                                     ;;
;                                                                                     ;;
;                                                                                     ;;

(begin-for-syntax
  (define absurd-formation
    (rule (⊢ H G)
          (syntax-parse G
            [u:Uni
             #'(Absurd)]
            [_ (not-applicable)])))
  (define absurd-equality
    (rule (⊢ H G)
          (syntax-parse G
            [eq:Eq
             #:with u:Uni #'eq.type
             #:with a1:Abs #'eq.left
             #:with a2:Abs #'eq.right
             #'(void)]
            [_ (not-applicable)])))
  (define (absurd-elim n)
    (rule (⊢ (at-hyp n Δ (hyp x ty _) Γ) G)
          #:when (syntax-parse ty [a:Abs #t] [_ #f])
          #`(error #,x)))
  (define absurd-member
    (rule (⊢ H G)
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (error)
            [eq:Eq
             #:with (#%plain-app error x) #'eq.left
             #:with (#%plain-app error y) #'eq.right
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #'(≡ (Absurd) x y)
                                              'expression
                                              null)))
                (void))]
            [_ (not-applicable)]))))

(module+ test
  (define absurd-ty
    (run-script #:goal (U 0)
                absurd-formation))
  (check-equal? absurd-ty (Absurd))
  (define absurd-is-absurd
    (run-script #:goal (≡ (U 0) (Absurd) (Absurd))
                absurd-equality))
  (check-equal? absurd-is-absurd (void))
  (define absurd→absurd
    (run-script #:goal (Π (Absurd) (λ (_) (Absurd)))
                (then-l
                 (Π-intro 0 'h)
                 (absurd-equality (assumption 0)))))
  (check-true (procedure? absurd→absurd))

  (define absurdities-abound
    (run-script #:goal (Π (Absurd)
                          (λ (oops)
                            (≡ (Nat) (error oops) (error oops))))
                (Π-intro 0 'h)
                (try absurd-equality absurd-member)
                (assumption-refl 0)))
  (check-true (procedure? absurdities-abound)))


;
;
;
;   ;;   ;;               ;;                                     ;;;;
;   ;;;  ;;               ;;                                     ;;;;
;   ;;;  ;;               ;;                                       ;;
;   ;;;; ;;    ;;;;     ;;;;;;;   ;;   ;;    ;; ;;;    ;;;;        ;;       ;;;;
;   ;; ; ;;   ;;;;;;    ;;;;;;;   ;;   ;;    ;;;;;;;  ;;;;;;       ;;     ;;;;;;;
;   ;; ; ;;   ;;   ;;     ;;      ;;   ;;    ;;;  ;   ;;   ;;      ;;     ;;   ;
;   ;; ;;;;        ;;     ;;      ;;   ;;    ;;            ;;      ;;     ;;
;   ;;  ;;;     ;;;;;     ;;      ;;   ;;    ;;         ;;;;;      ;;     ;;;;
;   ;;  ;;;    ;;;;;;     ;;      ;;   ;;    ;;        ;;;;;;      ;;      ;;;;;
;   ;;   ;;   ;;   ;;     ;;      ;;   ;;    ;;       ;;   ;;      ;;        ;;;;
;   ;;   ;;   ;;   ;;     ;;      ;;   ;;    ;;       ;;   ;;      ;;          ;;
;   ;;   ;;   ;;   ;;     ;;  ;   ;;  ;;;    ;;       ;;   ;;      ;;     ;;   ;;
;   ;;   ;;   ;;;;;;;     ;;;;;;  ;;;;;;;    ;;       ;;;;;;;   ;;;;;;;   ;;;;;;;
;   ;;   ;;    ;;; ;;      ;;;;    ;;; ;;    ;;        ;;; ;;   ;;;;;;;    ;;;;;
;
;
;
