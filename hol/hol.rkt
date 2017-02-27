#lang racket
(require
  "../lift-errors.rkt"
  "../lcfish.rkt"
  "../engine/hole.rkt"
  (for-syntax "../engine/proof-state.rkt")
  (for-syntax "terms.rkt" racket/match syntax/parse (for-syntax racket/base syntax/parse) racket/set)
  "../lift-tooltips.rkt")

(module+ test
  (require rackunit)
  (let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
    (begin (tt))))

(let-syntax ([tt (lambda (stx) (ensure-lifted-tooltips) (ensure-error-reports) #'(void))])
  (begin (tt)))

(begin-for-syntax
  #;(current-tactic-handler (lambda (exn) (raise exn)))

  (tactic-info-hook
   (lambda (hole-stx)
     (define where (get-hole-loc hole-stx))
     (match (get-hole-goal hole-stx)
       [(⊢ Γ p)
        (define goal
          (format "~a" p))
        (define message
          (format "~a:\n~a"
                  (syntax->datum where)
                  goal))
        (save-tooltip message where)]
       [_ (void)])))
  
  (define-syntax (can stx)
    (syntax-parse stx
      [(_ expr)
       #'(with-handlers ([exn:fail? (lambda (e) #f)])
           expr
           #t)]))
  
  (define (leftmost v)
    (if (pair? v) (leftmost (car v)) v))

  (define (in-plist lst)
    (define stop (gensym))
    (define remaining lst)
    (in-producer (lambda ()
                   (match remaining
                     [(? null?) (values stop stop)]
                     [(cons x (cons y xs))
                      (set! remaining xs)
                      (values x y)]
                     [_ (raise-argument-error 'in-plist "even-length list" lst)]))
                 (lambda (x y)
                   (or (eqv? x stop) (eqv? y stop)))))

  
  ;; Sequents are the basis of the logic. The context is a set
  ;; of terms, the body is a term.
  (struct ⊢ (context conclusion) #:transparent)

  (define · (empty-term-set))
  
  (define (REFL hole make-hole)
    (define goal (get-hole-goal hole))
    (match goal
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              tm1)
             tm2))
       #:when (α-equiv? tm1 tm2)
       #'#t]
      [g ((fail (format "Not reflexive: ~a" g)) hole make-hole)]))

  (define ((TRANS tm2) hole make-subgoal)
    (define goal (get-hole-goal hole))
    (match goal
      [(⊢ Γ (term-app
             (term-app
              (term-const '= t)
              tm1)
             tm3))
       (define g1
         (recheck
          (term-app
           (term-app
            (term-const '= t)
            tm1)
           tm2)))
       (define g2
         (recheck
          (term-app
           (term-app
            (term-const '= t)
            tm2)
           tm3)))
       (with-syntax ([h1 (make-subgoal hole (⊢ Γ g1))]
                     [h2 (make-subgoal hole (⊢ Γ g2))])
         #'(begin h1 h2))]))
  
  (define (MK_COMB hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              (term-app s u))
             (term-app t v)))
       (define g1
         (recheck (term-app
                   (term-app (term-const '= #f)
                             s)
                   t)))
       (define g2
         (recheck (term-app
                   (term-app (term-const '= #f)
                             u)
                   u)))
       (with-syntax ([h1 (make-hole hole (⊢ Γ g1))]
                     [h2 (make-hole hole (⊢ Γ g2))])
         #'(begin h1 h2))]))

  (define (ABS hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              (term-abs x1 _  body1))
             (term-abs x2 _ body2)))
       #:when (eqv? x1 x2)
       (define g
         (recheck (term-app
                   (term-app
                    (term-const '= #f)
                    body1)
                   body2)))
       (make-hole hole (⊢ Γ g))]
      [other
       ((fail (format "ABS doesn't apply to ~a" other)) hole make-hole)]))
  (define (BETA hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              (term-app
               (term-abs x1 _ t1)
               (term-var x2 _)))
             t2))
       #:when (and (set-empty? Γ)
                   (eqv? x1 x2)
                   (α-equiv? t1 t2))
       #'#t]
      [other ((fail (format "BETA doesn't apply: ~a" other)) hole make-hole)]))
  (define (ASSUME hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ p)
       (if (set-member? Γ p)
           #'#t
           ((fail (format "Not an assumption: ~a" p)) hole make-hole))]))
  (define ((EQ_MP p) hole make-hole)
    (define Σ (make-hasheqv))
    (match (get-hole-goal hole)
      [(⊢ Γ q)
       #:when (and (can (unify (type-of q) (type-app 'bool '()) Σ))
                   (can (unify (type-of p) (type-app 'bool '()) Σ)))
       (define g1
         (⊢ Γ (recheck
               (term-app
                (term-app
                 (term-const '= #f)
                 p)
                q))))
       (define g2
         (⊢ Γ p))
       (with-syntax ([h1 (set-goal (make-hole hole) g1)]
                     [h2 (set-goal (make-hole hole) g2)])
         #'(begin h1 h2))]))
  (define (DEDUCT_ANTISYM_RULE hole make-hole)
    (define Σ (make-hasheqv))
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              p)
             q))
       #:when (and (can (unify (type-of p) (type-app 'bool '()) Σ))
                   (can (unify (type-of q) (type-app 'bool '()) Σ)))
       (define g1
         (⊢ (set-add Γ p) q))
       (define g2
         (⊢ (set-add Γ q) p))
       (with-syntax ([h1 (set-goal (make-hole hole) g1)]
                     [h2 (set-goal (make-hole hole) g2)])
         #'(begin h1 h2))]))

  (define ((INST Γ p . vars) hole make-hole)
    (define Σ (make-hasheqv))
    (define σ (make-hasheqv
               (for/list ([(v t) (in-plist vars)])
                 (cons v t))))
    (define Γ-inst
      (for/set ([h Γ])
        (term-subst h σ Σ)))
    (define p-inst
      (term-subst p σ Σ))
    (match (get-hole-goal hole)
      [(⊢ Δ q)
       #:when (and (set-empty? (set-subtract Γ-inst Δ))
                   (α-equiv? p-inst q))
       (set-goal (make-hole hole) (⊢ Γ p))]))

  (define ((INST_TYPE Γ p . vars) hole make-hole)
    (define Σ
      (make-hasheqv
       (for/list ([(α t) (in-plist vars)])
         (cons α t))))
    (define Γ-inst
      (for/set ([h Γ])
        (type-inst-in-term h Σ)))
    (define p-inst (type-inst-in-term p Σ))
    (match (get-hole-goal hole)
      [(⊢ Δ q)
       #:when (and (set-empty? (set-subtract Γ-inst Δ))
                   (can (unify (type-of p-inst)
                               (type-of q)
                               Σ))
                   (α-equiv? p-inst q))
       (set-goal (make-hole hole) (⊢ Γ p))]))

  (define (ETA_AX hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '= _)
              (term-abs x _ (term-app t1 (term-var y _))))
             t2))
       #:when (and (eqv? x y)
                   (not (free-in? x t1))
                   (α-equiv? t1 t2))
       #'#t]))

  (define (SELECT_AX hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ (term-app
             (term-app
              (term-const '⇒ _)
              (term-app
               P1
               (term-var x _)))
             (term-app
              P2
              (term-app
               (term-const 'ε _)
               P3))))
       #:when (and (α-equiv? P1 P2)
                   (α-equiv? P2 P3))
       #'#t]))
  
  (define ((UNFOLD c) hole make-hole)
    (match (get-hole-goal hole)
      [(⊢ Γ p)
       (define Δ
         (for/set ([h (in-set Γ)])
           (unfold c h)))
       (define q (unfold c p))
       (make-hole hole (⊢ Δ q))])))

(define-syntax (run-script stx)
  (syntax-parse stx
    [(run-script #:goal g tactic ...)
     #`(let-syntax ([go (lambda (s)
                          (init-hole (then tactic ...)
                                     (⊢ · (check g))
                                     #'#,stx))])
         (go))]))



(module+ test
  (check-true
   (run-script
    #:goal (parse-term '(= (λ (x) x) (λ (y) y)))
    REFL))

  (check-true
   (run-script
    #:goal (parse-term '(= (λ (x) x) (λ (y) y)))
    (TRANS (parse-term '(λ (z) z)))
    REFL))

  (check-true
   (run-script
    #:goal (parse-term '(= ((λ (x) x) ⊤) ((λ (y) y) ⊤)))
    MK_COMB REFL))

  (check-true
   (run-script
    #:goal (parse-term '(= ((λ (x) x) ⊤) ((λ (x) x) ⊤)))
    (then-l MK_COMB
            (ABS))
    REFL))

  (check-true
   (run-script
    #:goal (parse-term '⊤)
    (UNFOLD '⊤)
    REFL))

  #;
  (run-script
   #:goal (parse-term '(= (λ (x) x) (λ (y z) y)))
   REFL))
