#lang racket

(require "../lcfish.rkt"
         "../lift-tooltips.rkt"
         "../lift-errors.rkt"
         "../engine/hole.rkt"
         "../tooltip-info.rkt"
         "../rule.rkt"
         (for-syntax "../seal.rkt" "../engine/refinement.rkt")
         (for-syntax "../goal.rkt" "../engine/proof-state.rkt")
         (for-syntax "unsafe.rkt")
         racket/stxparam
         (for-syntax racket/list
                     racket/format
                     racket/match
                     racket/string
                     racket/port
                     racket/contract
                     racket/set
                     racket/stxparam
                     racket/syntax
                     syntax/id-set
                     syntax/id-table
                     syntax/kerncase
                     syntax/parse
                     "../stx-utils.rkt")
         (for-syntax (for-syntax racket/base syntax/parse)))

(provide (for-syntax Uni Eq Pi
                     hyp
                     ⊢
                     at-hyp
                     α-equiv?/hyps
                     make-assumption-hole
                     constructs?
                     subst* subst subst1
                     Π-intro extensionality Π-in-uni
                     λ-equality apply-reduce
                     equality-equality replace symmetry
                     assumption assumption-refl thin
                     cut
                     lemma unfold
                     todo ADMIT
                     stx->string)
         (struct-out Π)
         (struct-out ≡)
         (struct-out U)
         (struct-out Absurd)
         side-conditions
         run-script theorem)



(module+ test (require rackunit))

(let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
  (begin (tt)))
(module+ test
  (let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
    (begin (tt))))

(begin-for-syntax
  (struct hyp (name type hidden?)
    #:transparent
    #:methods gen:hypothesis
    [(define (hypothesis-id h) (hyp-name h))
     (define (hypothesis-shows h) (hyp-type h))
     (define (hypothesis->string h)
       (format (if (hyp-hidden? h)
                   "[~a : ~a]"
                   "~a : ~a")
               (syntax->datum (hyp-name h))
               (stx->string (hyp-type h))))])
  (struct ⊢ (hyps goal)
    #:transparent
    #:methods gen:proof-goal
    [(define (hypotheses g)
       (⊢-hyps g))
     (define (goal g)
       (⊢-goal g))
     (define (goal->string g)
       (stx->string (⊢-goal g)))])

  (define/contract (dump-goal g)
    (-> (or/c ⊢?) string?)
    (if (syntax? g)
        (proof-goal->string (get-hole-goal g))
        (proof-goal->string g)))

  (no-more-tactics-hook (lambda (hole-stx)
                          (define message
                            (string-append "Unsolved goal:\n"
                                           (dump-goal (get-hole-goal hole-stx))))
                          (define exn
                            (make-exn:fail:syntax message
                                                  (current-continuation-marks)
                                                  (list (get-hole-loc hole-stx))))
                          (save-error exn)
                          ((error-display-handler) message exn)
                          ;#;
                          (raise-syntax-error 'run-script
                                              message
                                              (get-hole-loc hole-stx))))
  (basic-handler (lambda (exn)
                   (save-error exn)
                   (when (exn:srclocs? exn)
                     (define locs
                       ((exn:srclocs-accessor exn) exn))
                     (for ([l locs])
                       (save-tooltip (exn-message exn) l)))
                   ((error-display-handler) (exn-message exn) exn)
                   (seal-ctt (refinement #`(raise #,exn) (⊢ '() #'here) #'here))))

  (tactic-info-hook (tooltip-info dump-goal)))




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

(module the-universe racket
  (provide (all-defined-out))
  (struct U (level) #:transparent)
  (struct Absurd () #:transparent)
  (struct Listof (element-type) #:transparent)
  (struct Π (domain codomain) #:transparent)
  (struct ≡ (type left right) #:transparent))

(require (submod "." the-universe))

;; TODO: Missing types here are Int (replacing Nat), Less, Set, Quotient, Union, Product


(define (ind-Listof target base step)
  (cond [(pair? target)
         (step (car target)
               (cdr target)
               (ind-Listof (cdr target) base step))]
        [else
         base]))

(define axiom (void))

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

(begin-for-syntax
  ;; The arguments should be:
  ;;  1. free-id-table mapping bound identifiers to new syntax objects
  ;;  2. The syntax object within which to substitute (only supporting some core forms right now)
  (define/contract ((subst* to-subst) stx)
    (-> free-id-table? (-> syntax? syntax?))
    (syntax-parse stx
      #:literal-sets (kernel-literals)
      [(quote e) #'(quote e)]
      [x
       #:when (identifier? #'x)
       (let ([val (free-id-table-ref to-subst #'x #f)])
         (if val val #'x))]
      [((~and ap #%plain-app) e ...)
       (syntax-disarm #`(ap #,@(map (subst* to-subst) (syntax-e #'(e ...)))) #f)]
      [((~and lam #%plain-lambda) (arg ...) body ...)
       #`(lam (arg ...) #,@(map (subst* to-subst) (syntax-e #'(body ...))))]
      [(#%expression e)
       ((subst* to-subst) #'e)]
      [other (error (format "subst*: Unsupported syntax: ~a" (syntax->datum #'other)))]))

  (define (subst to-subst stx) ((subst* to-subst) stx))

  (define (simple-subst from to)
    (make-immutable-free-id-table (list (cons from to))))

  (define (subst1 from to expr)
    (subst (simple-subst from to) expr)))
  

(define-for-syntax (subst-in-hyp σ h)
  (match-define (hyp name type visible?) h)
  (hyp name (subst σ h) visible?))


(define-for-syntax (hyps->id-set H)
  (for/fold ([ids (immutable-bound-id-set)])
            ([h H])
    (bound-id-set-add ids (hyp-name h))))

(begin-for-syntax
  ;; Arguments:
  ;;  ctxt - a set of bound variables
  ;;  stx1, stx2 - objectx to compare
  (define/contract (α-equiv? ctxt stx1 stx2)
    (-> immutable-bound-id-set? syntax? syntax? boolean?)
    (define (arglist->set xs)
      (for/fold ([the-set (immutable-bound-id-set)])
                ([id xs])
        (bound-id-set-add the-set id)))
    (syntax-parse #`(#,stx1 #,stx2)
      #:literal-sets (kernel-literals)
      [((quote e1) (quote e2))
       (equal? (syntax->datum #'e1) (syntax->datum #'e2))]
      [((#%expression e1) e2)
       (α-equiv? ctxt #'e1 #'e2)]
      [(e1 (#%expression e2))
       (α-equiv? ctxt #'e1 #'e2)]
      [(x1:id x2:id)
       (begin
         (cond
           ;;;TODO: Ask Sam about what should be bound vs free here
           [(set-member? ctxt #'x1)
            (free-identifier=? #'x1 #'x2)]
           [(set-member? ctxt #'x2)
            (displayln `(nope ,#'x1 ,#'x2))
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
             (let ([substitution (make-immutable-free-id-table (map cons arglist2 arglist1))])
               (andmap (lambda (b1 b2)
                         (α-equiv? (bound-id-set-union ctxt (arglist->set arglist1))
                                   b1 (subst substitution b2)))
                       body-list1
                       body-list2))
             #f))]
      [_
       #f])))

(define-for-syntax (α-equiv?/hyps H a b)
  (define binders
    (for/fold ([the-set (immutable-bound-id-set)])
              ([h H])
      (bound-id-set-add the-set (hyp-name h))))
  (α-equiv? binders a b))

(define-for-syntax (constructs? struct-type-name identifier)
  ;; this seems wrong, but the struct transformer binding's notion of constructor is not
  ;; the right thing here...
  (and (identifier? (syntax-property identifier 'constructor-for))
       (free-identifier=? (syntax-property identifier 'constructor-for)
                          struct-type-name)))

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
    (pattern (#%plain-app eq:id type left right)
             #:when (constructs? #'≡ #'eq)))

  (define-syntax-class Abs
    #:literal-sets (kernel-literals)
    #:attributes ()
    (pattern (#%plain-app abs:id)
             #:when (constructs? #'Absurd #'abs)))

  (define-syntax-class Lst
    #:literal-sets (kernel-literals)
    #:attributes (type)
    (pattern (#%plain-app l:id type)
             #:when (constructs? #'Listof #'l)))

  (define-syntax-class Pi
    #:literal-sets (kernel-literals)
    #:attributes (dom var cod)
    (pattern (#%plain-app pi dom (#%plain-lambda (var) cod))
             #:when (constructs? #'Π #'pi))))


(define-for-syntax (stx->string stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [x
     #:when (syntax-property #'x 'original-stx)
     (stx->string (syntax-property #'x 'original-stx))]
    [(#%plain-app e ...)
     (~a (map stx->string (syntax->list #'(e ...))))]
    [(#%plain-lambda (x ...) e ...)
     (format "(λ ~a ~a)"
             (map stx->string (syntax->list #'(x ...)))
             (string-join (map stx->string (syntax->list #'(e ...))) " "))]
    [(quote e) (format "'~a" (syntax->datum #'e))]
    [p:Pi
     (format "(Π ~a (λ (~a) ~a)" (stx->string #'p.dom) (stx->string #'p.var) (stx->string #'p.cod))]
    [(#%expression e) (stx->string #'e)]
    [x:id
     #:when (syntax-property #'x 'constructor-for)
     (~a (syntax-e (syntax-property #'x 'constructor-for)))]
    [other (~a (syntax->datum #'other))]))

(define-for-syntax (todo hole make-hole)
  ((fail (dump-goal (get-hole-goal hole)))
   hole make-hole))

;; For showing error messages etc
(define-for-syntax (unexpand stx) stx
  #;(syntax-parse stx
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
;   ;;;;;;;;  ;;                                                                   
;   ;;;;;;;;  ;;                                                                   
;      ;;     ;;                                                                   
;      ;;     ;; ;;;      ;;;       ;;;      ;; ;;;     ;;;     ; ;; ;;     ;;;;   
;      ;;     ;;;;;;;    ;;;;;     ;;;;;     ;;;;;;;   ;;;;;    ;;;;;;;;  ;;;;;;;  
;      ;;     ;;;  ;;   ;;   ;;   ;;; ;;;    ;;;  ;   ;;   ;;   ;; ;; ;;  ;;   ;   
;      ;;     ;;   ;;   ;;   ;;   ;;   ;;    ;;       ;;   ;;   ;; ;; ;;  ;;       
;      ;;     ;;   ;;   ;;;;;;;   ;;   ;;    ;;       ;;;;;;;   ;; ;; ;;  ;;;;     
;      ;;     ;;   ;;   ;;;;;;;   ;;   ;;    ;;       ;;;;;;;   ;; ;; ;;   ;;;;;   
;      ;;     ;;   ;;   ;;        ;;   ;;    ;;       ;;        ;; ;; ;;     ;;;;  
;      ;;     ;;   ;;   ;;        ;;   ;;    ;;       ;;        ;; ;; ;;       ;;  
;      ;;     ;;   ;;   ;;;  ;    ;;; ;;;    ;;       ;;;  ;    ;; ;; ;;  ;;   ;;  
;      ;;     ;;   ;;    ;;;;;;    ;;;;;     ;;        ;;;;;;   ;; ;; ;;  ;;;;;;;  
;      ;;     ;;   ;;     ;;;;      ;;;      ;;         ;;;;    ;; ;; ;;   ;;;;;   
;                                                                                  
;                                                                                  
;                                                                                  


(define-syntax (run-script stx)
  (ensure-lifted-tooltips)
  (syntax-parse stx
    [(run-script #:goal g tactic ...)
     #`(let ()
         (define-syntax (go s)
           (init-hole
            unseal-ctt
            (make-skip seal-ctt)
            (then tactic ...)
            (⊢ null (local-expand #'g 'expression null))
            #'#,#'(tactic ...)))
         (go))]))

(begin-for-syntax
  ;; The result of running a tactic script is a transformer environment binding with metadata
  ;; about the new value that expands to the extract syntax in phase 0.
  (struct theorem-definition (type extract renamer)
    #:transparent
    #:property prop:rename-transformer (struct-field-index renamer)))

(define-syntax (theorem stx)
  (syntax-parse stx
    [(_ name:id goal tactic1 tactic ...)
     (define runtime-name (syntax-property (generate-temporary #'name) 'original-stx #'name))
     (with-syntax ([runtime runtime-name]
                   [unseal #'unseal-ctt]
                   [seal #'seal-ctt])
       (quasisyntax/loc stx
         (begin
           (define-for-syntax expanded-goal (local-expand #'goal 'expression null))    
           (define-syntax (get-extract s)
             (init-hole unseal
                        (make-skip seal)
                        (then tactic1 tactic ...)
                        (⊢ null expanded-goal)
                        #'#,#'(tactic1 tactic ...)))
           (define-for-syntax the-extract (local-expand #'(get-extract) 'expression null))
           (define-syntax (my-extract s) the-extract)
           (define runtime (my-extract))
           (define-syntax name (theorem-definition expanded-goal the-extract #'runtime)))))]))

(module+ test
  (define-for-syntax (emit stx)
    (rule _ #:seal seal-ctt stx))
  (theorem garbage (cons '(lotsa stuff) #f) (emit #'(cons #t #t)))

  ;; Test the rename transformer bit
  (check-equal? garbage (cons #t #t))

  ;; Test the compile time info bit
  (define-syntax (test-unfold-garbage stx)
    (define-values (thm transformer?)
      (syntax-local-value/immediate #'garbage))
    (if transformer?
        (match thm
          [(theorem-definition ty ext _)
           ;; Check that the type is saved correctly
           (syntax-parse ty
             #:literal-sets (kernel-literals)
             #:literals (cons)
             [(#%plain-app cons (quote (l s)) (quote #f))
              (if (and (eqv? (syntax-e #'l) 'lotsa) (eqv? (syntax-e #'s) 'stuff))
                  (syntax-parse ext
                    #:literal-sets (kernel-literals)
                    #:literals (cons)
                    [(#%plain-app cons (quote #t) (quote #t))
                     #''succeeded]
                    [_ #''failed-1])
                  #''failed-2)]
             [_ #''failed-3])])
        #''failed))
  (check-eqv? 'succeeded test-unfold-garbage))



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
  

  (define ((guard-goal pred tac) hole make-hole)
    (match (get-hole-goal hole)
      [#f ((fail "No goal found.") hole make-hole)]
      [g #:when (pred g)
         (tac hole make-hole)]
      [g ((fail (string-append "Wrong goal:\n" (dump-goal g)))
          hole make-hole)]))
  )



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

  (define (thin i)
    (rule (⊢ (at-hyp i Δ _ Γ) G)
          #:seal seal-ctt
          (subgoal (⊢ (append Δ Γ) G))))
  
  (define (assumption n)
    (rule (⊢ H G) #:seal seal-ctt
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
               [(α-equiv?/hyps H ty G)
                x]
               [else
                (not-applicable (format "Mismatched assumption ~a. Expected ~a, got ~a"
                                             n
                                             (stx->string G)
                                             (stx->string ty)))])])))

  (define (lemma the-lemma [name 'lemma])
    (rule (⊢ H G)
          #:seal seal-ctt
          #:when (and (identifier? the-lemma))
          (define-values (thm transformer?)
            (syntax-local-value/immediate the-lemma))
          (match thm
            [(theorem-definition ty _ _)
             #`(let-syntax ([#,name (make-rename-transformer #'#,the-lemma)])
                 #,(make-assumption-hole (lambda (g) (subgoal g))
                                         (lambda (good-name)
                                           (⊢ (cons (hyp good-name ty #f) H)
                                              G))
                                         name))]
            [_ (not-applicable (format "Not a theorem: ~a. Got: ~a" the-lemma thm))])))

  (define (unfold the-lemma [name 'unfolding])
    (rule (⊢ H G)
          #:seal seal-ctt
          #:when (and (identifier? the-lemma))
          (define-values (thm transformer?)
            (syntax-local-value/immediate the-lemma))
          (match thm
            [(theorem-definition ty ext _)
             #`(let ([#,name (void)])
                 #,(make-assumption-hole (lambda (g) (subgoal g))
                                         (lambda (good-name)
                                           (define hyp-ty
                                             (local-expand
                                              #`(≡ #,ty #,the-lemma #,ext)
                                              'expression
                                              null))
                                           (⊢ (cons (hyp good-name hyp-ty #f) H)
                                              G))
                                         name))]
            [_ (not-applicable (format "Not a theorem: ~a. Got: ~a" the-lemma thm))])))

  (define (cut i T (name 'H))
    (rule (⊢ H G)
          #:seal seal-ctt
          (define-values (Δ Γ) (split-at H i))
          (with-syntax ([new-H (subgoal (⊢ Γ T))])
            #`((lambda (#,name)
                 #,(make-assumption-hole (lambda (g) (subgoal g))
                                         (lambda (good-name)
                                           (⊢ (append Δ (list (hyp good-name T #f)) Γ)
                                              G))
                                         name))
               new-H))))
  
  (define ADMIT
    (rule (⊢ H G)
          #:seal seal-ctt
          #'(error "Admitted")))
  
  ;; TODO: test me
  (define (explicit-intro term)
    (rule (⊢ H G)
          #:seal seal-ctt
          (define term-core (local-expand term 'expression null))
          #`(side-conditions #,(subgoal (⊢ H
                                           (local-expand
                                            #`(≡ #,G #,term-core #,term-core)
                                            'expression
                                            null)))
                             #,term-core))))


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
    (rule (⊢ H G)
          #:seal seal-ctt
          (if (not (exact-nonnegative-integer? i))
              (not-applicable (format "Invalid universe level: ~a" i))
              (syntax-parse G
                [u:Uni
                 (if (> (syntax-e (attribute u.level)) i)
                     (with-syntax ([i i])
                       #'(U i))
                     (not-applicable "Universe too big"))]
                [_ (not-applicable (format "Not a universe: ~a" G))]))))

  (define equal-universe
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with u1:Uni #'eq.type
             #:with u2:Uni #'eq.left
             #:with u3:Uni #'eq.right
             #:when (and (< (syntax-e (attribute u2.level))
                            (syntax-e (attribute u1.level)))
                         (= (syntax-e (attribute u2.level))
                            (syntax-e (attribute u3.level))))
             #'(void)]
            [_ (not-applicable)])))

  (define (cumulativity j)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             #:with u:Uni #'eq.type
             #:when (α-equiv? (hyps->id-set H) #'eq.left #'eq.right)
             (define i (syntax-e #'u.level))
             (if (< j i)
                 (subgoal (⊢ H (local-expand #`(≡ (U #,j) eq.left eq.right)
                                             'expression
                                             null)))
                 (not-applicable "Universe too big for cumulativity"))]))))

(module+ test
  (define u2
    (run-script #:goal (U 5)
                (intro-universe 2)))
  (check-equal? u2 (U 2))
  (define yep
    (run-script #:goal (≡ (U 5) (U 2) (U 2))
                equal-universe))
  (check-equal? yep (void))

  (theorem u-bigger (≡ (U 4) (U 0) (U 0))
           (cumulativity 3)
           equal-universe))


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
          #:seal seal-ctt
          (syntax-parse G
            [u:Uni
             (with-syntax ([A A]
                           [g1 (subgoal (⊢ H (local-expand #`(≡ u #,A #,A) 'expression null)))]
                           [g2 (subgoal (⊢ H A))]
                           [g3 (subgoal (⊢ H A))])
               #'(side-conditions
                  g1
                  (≡ A g2 g3)))]
            [other (not-applicable)])))
  (define equality-equality
    (rule (⊢ H G)
          #:seal seal-ctt
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
          #:seal seal-ctt
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
          #:seal seal-ctt
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
               [(#%plain-app eq in-ty h1:id h2:id)
                #:when (and (constructs? #'≡ #'eq)
                            ;; TODO: this doesn't give the expected answer with bound-id=?,
                            ;; but this may also be wrong. Think about it, and ask Sam.
                            (free-identifier=? x #'h1)
                            (free-identifier=? x #'h2)
                            (let ([Γ-ids (immutable-bound-id-set (map hyp-name Γ))])
                              (α-equiv? Γ-ids #'in-ty ty)))
                #'(void)]
               [_ (not-applicable (format "Assumption/goal mismatch ~a. Expected ~a, got ~a."
                                          n
                                          (syntax->datum
                                           (local-expand #`(≡ #,ty #,x #,x) 'expression null))
                                          (syntax->datum G)))])])))

  (define (replace type left right ctxt #:universe (i 0))
    (rule (⊢ H G)
          #:seal seal-ctt
          (define rewrite-ctxt (local-expand ctxt 'expression null))
          (syntax-parse rewrite-ctxt
            #:literal-sets (kernel-literals)
            [(#%plain-lambda (x) body)
             (define left-body (subst1 #'x left #'body))
             (if (α-equiv? (hyps->id-set H) left-body G)
                 ;; TODO fix binding and such
                 #`(side-conditions #,(subgoal (⊢ H
                                                  (local-expand #`(≡ #,type #,left #,right)
                                                                'expression
                                                                null)))
                                    #,(subgoal (⊢ (cons (hyp #'x type #f) H)
                                                  (local-expand #`(≡ (U #,i)
                                                                     #,type
                                                                     #,type)
                                                                'expression
                                                                null)))
                                    #,(subgoal (⊢ H (subst1 #'x right #'body))))
                 (not-applicable (format "replace: Expected ~a, got ~a"
                                         (stx->string left-body)
                                         (stx->string G))))]
            [_ (not-applicable "Malformed rewrite context. Must be a single-arg λ, but was ~a" rewrite-ctxt)])))

  (define symmetry
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             (subgoal (⊢ H (local-expand (syntax/loc G (≡ eq.type eq.right eq.left)) 'expression null)))]
            [_ (not-applicable)])))
  
  (define (transitivity middle)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #`(≡ eq.type eq.left #,middle) 'expression null)))
                #,(subgoal (⊢ H (local-expand #`(≡ eq.type #,middle eq.right) 'expression null)))
                (void))]
            [_ (not-applicable)]))))


(module+ test
  (define U1≡U0
    (run-script #:goal (U 3)
                (then-l (equality-formation
                         (local-expand #'(U 2) 'expression null))
                        [equal-universe
                         (intro-universe 1)
                         (intro-universe 0)])))
  (check-equal? U1≡U0 (≡ (U 2) (U 1) (U 0)))

  (define an-eq-eq
    (run-script #:goal (≡ (U 2)
                          (≡ (U 1) (U 0) (U 0))
                          (≡ (U 1) (U 0) (U 0)))
                equality-equality
                equal-universe))
  (check-true (void? an-eq-eq))

  )

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
(define-syntax (assumption-hole stx)
  (define make-subgoal (syntax-property stx 'make-subgoal))
  (define goal-maker (syntax-property stx 'goal-maker))
  (syntax-case stx ()
    [(_ x y ...)
     (make-subgoal
      (apply goal-maker (syntax->list #'(x y ...))))]))

(define-for-syntax (make-assumption-hole make-subgoal goal-maker . xs)
  (syntax-property
   (syntax-property
    #`(assumption-hole #,@xs)
    'goal-maker
    goal-maker)
   'make-subgoal make-subgoal))

(define-syntax (side-conditions stx)
  (syntax-parse stx
    [(_ condition ... result)
     (for ([c (syntax->list #'(condition ...))])
       (local-expand c 'expression null))
     #'result]))

(begin-for-syntax
  (define (Π-formation x dom)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [u:Uni
             (define dom-ok
               (subgoal (⊢ H (local-expand #`(≡ u #,dom #,dom) 'expression null))))
             #`(side-conditions
                #,dom-ok
                (Π #,dom
                   (λ (#,x)
                     #,(make-assumption-hole (lambda (g) (subgoal g))
                                             (lambda (good-x)
                                               (⊢ (cons (hyp good-x dom #f) H)
                                                  G))
                                             x))))]
            [_ (not-applicable)])))

  (define (Π-in-uni (new-var (gensym 'y)))
    (rule (⊢ H G)
          #:seal seal-ctt
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
                                          (lambda (good-var)
                                            (⊢ (cons (hyp good-var #'a #f) H)
                                               (let ([renamed-c (subst (make-free-id-table
                                                                        (list (cons #'x good-var)))
                                                                       #'c)]
                                                     [renamed-d (subst (make-free-id-table
                                                                        (list (cons #'y good-var)))
                                                                       #'d)])
                                                 (local-expand #`(≡ u #,renamed-c #,renamed-d)
                                                               'expression
                                                               null))))
                                          new-var))
                (void))]
            [_ (not-applicable)])))

  (define (Π-intro i (var #f))
    (if (exact-nonnegative-integer? i)
        (rule (⊢ H G)
              #:seal seal-ctt
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
                                              (lambda (the-var)
                                                (⊢ (cons (hyp the-var #'dom #f) H)
                                                   (subst (make-free-id-table
                                                           (list (cons #'x the-var)))
                                                          #'cod)))
                                              y)))]
                [_ (not-applicable)]))
        (fail (format "Π-intro: not a valid level: ~a" i))))

  (define λ-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with (#%plain-app pi dom (#%plain-lambda (x:id) cod)) #'eq.type
             #:with (#%plain-lambda (y:id) body1) #'eq.left
             #:with (#%plain-lambda (z:id) body2) #'eq.right
             #`(let ((x (void)))
                 #,(make-assumption-hole (lambda (g) (subgoal g))
                                         (lambda (the-var)
                                           (⊢ (cons (hyp the-var #'dom #f) H)
                                              (local-expand #`(≡ cod
                                                                 #,(subst1 #'y the-var #'body1)
                                                                 #,(subst1 #'z the-var #'body2))
                                                            'expression null)))
                                         #'x))]
            [other (not-applicable)])))

  (define (extensionality (var 'arg))
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with pi:Pi #'eq.type
             #`(side-conditions
                (let ([#,var (void)])
                  #,(make-assumption-hole
                     (lambda (g) (subgoal g))
                     (lambda (the-var)
                       (⊢ (cons (hyp the-var #'pi.dom #f)
                                H)
                          (local-expand #`(≡ #,(subst1 the-var #'pi.var #'pi.cod)
                                             (#%plain-app eq.left #,the-var)
                                             (#%plain-app eq.right #,the-var))
                                        'expression
                                        null)))
                     var))
                #,(subgoal (⊢ H (local-expand #'(≡ eq.type eq.left eq.left) 'expression null)))
                #,(subgoal (⊢ H (local-expand #'(≡ eq.type eq.right eq.right) 'expression null))))])))

  (define apply-reduce
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            (eq:Eq
             #:with (#%plain-app (#%plain-lambda (x:id ...) body:expr) arg:expr ...) #'eq.left
             #:when (= (length (syntax->list #'(x ...))) (length (syntax->list #'(arg ...))))
             (subgoal (⊢ H (local-expand #`(≡ eq.type
                                              #,(subst (make-immutable-free-id-table
                                                        (map syntax-e
                                                             (syntax->list #'((x . arg) ...))))
                                                       #'body)
                                              eq.right)
                                         'expression
                                         null))))
            (_ (not-applicable))))))

(module+ test
  (define U1→U1
    (run-script #:goal (U 2)
                (then-l
                 (Π-formation 'x #'(U 1))
                 [equal-universe (intro-universe 1)])))
  (check-true (Π? U1→U1))
  (check-equal? (Π-domain U1→U1) (U 1))
  (check-equal? ((Π-codomain U1→U1) "any-old-thing") (U 1))

  (define U1→U1:U2
    (run-script #:goal (≡ (U 2)
                          (Π (U 1) (λ (_) (U 1)))
                          (Π (U 1) (λ (_) (U 1))))
                (then-l (Π-in-uni 'y)
                        [equal-universe equal-universe])))
  (check-true (void? U1→U1:U2))

  (define U1-identity
    (run-script #:goal (Π (U 1) (λ (_) (U 1)))
                (then-l (Π-intro 2 'some-uni)
                        [equal-universe (assumption 0)])))
  (check-true (procedure? U1-identity))
  (check-equal? (U1-identity (U 0)) (U 0))

  (define U1-refl
    (run-script #:goal (Π (U 2) (λ (ty) (≡ (U 2) ty ty)))
                (then-l (Π-intro 3 't)
                        [equal-universe (assumption-refl 0)])))
  (check-true (procedure? U1-refl))
  (check-equal? (U1-refl (U 0)) (void))

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
          #:seal seal-ctt
          (syntax-parse G
            [u:Uni
             #'(Absurd)]
            [_ (not-applicable)])))
  (define absurd-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [eq:Eq
             #:with u:Uni #'eq.type
             #:with a1:Abs #'eq.left
             #:with a2:Abs #'eq.right
             #'(void)]
            [_ (not-applicable)])))
  (define (absurd-elim n)
    (rule (⊢ (at-hyp n Δ (hyp x ty _) Γ) G)
          #:seal seal-ctt
          #:when (syntax-parse ty [a:Abs #t] [_ #f])
          #`(error #,x)))
  (define absurd-member
    (rule (⊢ H G)
          #:seal seal-ctt
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
                 [absurd-equality (assumption 0)])))
  (check-true (procedure? absurd→absurd))

  (define absurdities-abound
    (run-script #:goal (Π (Absurd)
                          (λ (oops)
                            (≡ (U 0) (error oops) (error oops))))
                (Π-intro 1 'h)
                (try absurd-equality absurd-member)
                (assumption-refl 0)))
  (check-true (procedure? absurdities-abound)))




;                                                    
;                                                    
;                ;;                                  
;    ;;          ;;                 ;;               
;    ;;                             ;;               
;    ;;                             ;;               
;    ;;        ;;;;       ;;;;    ;;;;;;;     ;;;;   
;    ;;        ;;;;     ;;;;;;;   ;;;;;;;   ;;;;;;;  
;    ;;          ;;     ;;   ;      ;;      ;;   ;   
;    ;;          ;;     ;;          ;;      ;;       
;    ;;          ;;     ;;;;        ;;      ;;;;     
;    ;;          ;;      ;;;;;      ;;       ;;;;;   
;    ;;          ;;        ;;;;     ;;         ;;;;  
;    ;;          ;;          ;;     ;;           ;;  
;    ;;          ;;     ;;   ;;     ;;  ;   ;;   ;;  
;    ;;;;;;;  ;;;;;;;;  ;;;;;;;     ;;;;;;  ;;;;;;;  
;    ;;;;;;;  ;;;;;;;;   ;;;;;       ;;;;    ;;;;;   
;                                                    
;                                                    
;                                                    

(begin-for-syntax
  (define listof-ctor
    (syntax-parse (local-expand #'(Listof (U 0)) 'expression null)
      #:literal-sets (kernel-literals)
      [(#%plain-app l _) #'l]))
  
  (define list-formation
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [u:Uni
             #`(#%plain-app #,listof-ctor #,(subgoal (⊢ H #'u)))])))

  (define list-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with u:Uni #'eq.type
             #:with l1:Lst #'eq.left
             #:with l2:Lst #'eq.right
             (subgoal (local-expand #`(≡ u l1.type l2.type) 'expression null))])))

  (define (list-intro-nil i)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [l:Lst
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #`(≡ (U #,i) l.type l.type) 'expression null)))
                null)])))

  (define (list-nil-equality i)
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            [eq:Eq
             #:with (quote ()) #'eq.left
             #:with (quote ()) #'eq.right
             #:with l:Lst #'eq.type
             #`(side-conditions #,(subgoal (⊢ H (local-expand #`(≡ (U #,i) l.type l.type) 'expression null))))])))

  (define list-intro-cons
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            [l:Lst
             #'(cons #,(subgoal (⊢ H #'l.type)) #,(subgoal (⊢ H #'l)))])))

  (define list-cons-equality
    (rule (⊢ H G)
          #:seal seal-ctt
          (syntax-parse G
            #:literal-sets (kernel-literals)
            #:literals (cons)
            [eq:Eq
             #:with lst:Lst #'eq.type
             #:with (#%plain-app cons x xs) #'eq.left
             #:with (#%plain-app cons y ys) #'eq.right
             #`(side-conditions
                #,(subgoal (⊢ H (local-expand #'(≡ lst.type x y) 'expression null)))
                #,(subgoal (⊢ H (local-expand #'(≡ lst xs ys) 'expression null)))
                (void))])))

  (define (list-elim n)
    (rule (⊢ (and H (at-hyp n Δ (hyp xs l #f) Γ)) G)
          #:seal seal-ctt
          (syntax-parse l
            #:literal-sets (kernel-literals)
            [lst:Lst
             (define base
               (subgoal (⊢ H (subst1 xs #''() G))))
             (define y #'y)
             (define ys #'ys)
             (define ih #'ih)
             (define step
               #`(λ (#,y #,ys #,ih)
                   #,(make-assumption-hole
                      (lambda (g) (subgoal g))
                      (lambda (y ys ih)
                        (⊢ (cons (hyp ih (subst1 xs ys G) #f)
                                 (cons (hyp ys #'lst #f)
                                       (cons (hyp y #'lst.type #f)
                                             H)))
                           (subst1 xs (local-expand #`(cons #,y #,ys) 'expression null) G)))
                      y ys ih)))
             #`(ind-Listof #,xs #,base #,step)]))))

;                                                              
;                                                              
;                                                              
;     ;;;;;              ;;                             ;;     
;    ;;;;;;;             ;;                             ;;     
;    ;;   ;              ;;                             ;;     
;    ;;       ;;   ;;    ;; ;;;     ;;;;      ;;;     ;;;;;;;  
;    ;;;      ;;   ;;    ;;;;;;   ;;;;;;;    ;;;;;    ;;;;;;;  
;     ;;;     ;;   ;;    ;;;  ;;  ;;   ;    ;;   ;;     ;;     
;      ;;;    ;;   ;;    ;;   ;;  ;;        ;;   ;;     ;;     
;       ;;;   ;;   ;;    ;;   ;;  ;;;;      ;;;;;;;     ;;     
;        ;;;  ;;   ;;    ;;   ;;   ;;;;;    ;;;;;;;     ;;     
;         ;;  ;;   ;;    ;;   ;;     ;;;;   ;;          ;;     
;    ;    ;;  ;;   ;;    ;;   ;;       ;;   ;;          ;;     
;   ;;;  ;;;  ;;  ;;;    ;;;  ;;  ;;   ;;   ;;;  ;      ;;  ;  
;    ;;;;;;   ;;;;;;;    ;;;;;;   ;;;;;;;    ;;;;;;     ;;;;;; 
;     ;;;;     ;;; ;;    ;; ;;;    ;;;;;      ;;;;       ;;;;  
;                                                              
;                                                              
;                                                              
