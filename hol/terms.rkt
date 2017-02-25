#lang racket

(require (for-syntax syntax/parse))
(provide parse-term recheck type-of α-equiv?
         empty-term-set unify term-subst
         type-inst-in-term free-in? unfold
         check
         (struct-out type-app)
         (struct-out type-var)
         (struct-out term-var)
         (struct-out term-app)
         (struct-out term-const)
         (struct-out term-abs))

;; The initial type constants
(define the-type-constants
  (make-hasheqv '((→ . 2) (bool . 0) (ind . 0))))

(define (write-type ty port mode)
  (pretty-print (type->sexp ty) port))

(struct type-var (name)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-type)])
(struct type-app (op args)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-type)])

(define (type->sexp t)
  (match t
    [(type-var α) α]
    [(type-app op '()) op]
    [(type-app op args) `(op . ,args)]))

(define (type? t)
  (match t
    [(type-var _) #t]
    [(type-app op args)
     (define this-op (assv op (unbox the-type-constants)))
     (and this-op
          (= (length args) (cdr this-op))
          (andmap type? args))]
    [_ #f]))

(define (type-subst t Σ)
  (match t
    [(type-var α)
     (dict-ref Σ α t)]
    [(type-app op args)
     (type-app op (map (λ (τ) (type-subst τ Σ)) args))]))

(define (occurs? α τ)
  (match τ
    [(type-var β) (eqv? α β)]
    [(type-app _ args) (ormap (λ (t) (occurs? α t)) args)]))

(struct exn:cant-unify exn:fail (t1 t2))
(define (raise-cant-unify msg t1 t2)
  (raise (exn:cant-unify (format "Can't unify: ~a ~a. ~a" t1 t2 msg)
                         (current-continuation-marks)
                         t1
                         t2)))

(define (unify τ1 τ2 the-subst)
  (define (helper t1 t2)
    (match* ((type-subst t1 the-subst)
             (type-subst t2 the-subst))
      [((type-app op1 args1) (type-app op2 args2))
       (if (eqv? op1 op2)
           (type-app op1
                     (for/list ([a1 args1] [a2 args2])
                       (helper a1 a2)))
           (raise-cant-unify "Mismatched operators" t1 t2))]
      [((type-var α) (and t (type-app op args)))
       (if (occurs? α t)
           (raise-cant-unify "Unification would be infinite" t1 t2)
           (begin (hash-set! the-subst α t)
                  t))]
      [((and t (type-app op args)) (type-var α))
       (helper (type-var α) t)]
      [((type-var α) (type-var β))
       (hash-set! the-subst α (type-var β))
       (type-var β)]))
  (helper τ1 τ2))

(define (unapply tm (args '()))
  (match tm
    [(term-app rator rand)
     (unapply rator (cons (term->sexp rand) args))]
    [other (cons (term->sexp other) args)]))

(define (term->sexp tm)
  (match tm
    [(term-var x _) x]
    [(term-const c _) c]
    [(term-app rator rand)
     (unapply rator (list (term->sexp rand)))]
    [(term-abs x _ body) `(λ (,x) ,(term->sexp body))]))

(define (write-term t port mode)
  (display (term->sexp t) port))

(struct term-var (name type)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-term)])
(struct term-const (name type)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-term)])
(struct term-app (rator rand)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-term)])
(struct term-abs (var type body)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc write-term)])


(struct constant (type def) #:transparent)

(define the-constants
  (let ((bool (type-app 'bool '()))
        (→ (lambda (a b)
              (type-app '→ (list a b))))
        (α (type-var 'α))
        (prim (lambda (c t)
                (cons c (constant t (term-const c t))))))
    (make-hasheqv
     (list (prim #t bool)
           (prim #f bool)
           (prim '= (→ α (→ α bool)))
           (prim 'ε (→ (→ α bool) α))))))

;; Consistently replace the names of variables in a type with
;; fresh variables (to make polymorphism easy)
(define (freshen ty)
  (define vars (make-hasheqv))
  (define (fresh-for α)
    (hash-ref! vars α (thunk (gensym))))
  (define (helper τ)
    (match τ
      [(type-var α) (type-var (fresh-for α))]
      [(type-app op args) (type-app op (map helper args))]))
  (helper ty))

;; Place type information onto a term, if possible. Return the annotated term and the type.
(define (type-check tm ctx Σ)
  (match tm
    [(term-var x #f)
     (define ty (dict-ref ctx x (thunk (type-var (gensym x)))))
     (values (term-var x ty) ty)]
    [(term-var x τ)
     (define ty (type-subst τ Σ))
     (values (term-var x ty) ty)]
    [(term-const name t)
     (define the-const
       (dict-ref the-constants
                 name
                 (lambda () (error (format "Unknown constant ~a" name)))))
     (define abs-ty (freshen (constant-type the-const)))
     (define the-type (if t (unify t abs-ty Σ) abs-ty))
     (values (term-const name the-type) the-type)]
    [(term-app rator rand)
     (define α (type-var (gensym)))
     (define β (type-var (gensym)))
     (define-values (checked-rator rator-ty-1)
       (type-check rator ctx Σ))
     (define rator-ty
       (unify rator-ty-1
              (type-app '→ (list α β))
              Σ))
     (define-values (checked-rand rand-ty-1)
       (type-check rand ctx Σ))
     (define rand-ty
       (unify rand-ty-1 α Σ))
     (values (term-app checked-rator checked-rand)
             (type-subst β Σ))]
    [(term-abs x t body)
     (define x-ty (if t t (type-var (gensym))))
     (define-values (checked-body body-ty)
       (type-check body (cons (cons x x-ty) ctx) Σ))
     (values (term-abs x (type-subst x-ty Σ) checked-body)
             (type-subst (type-app '→ (list x-ty body-ty)) Σ))]))

(define (unfold c tm)
  (match tm
    [(? term-var?) tm]
    [(term-const c t)
     (define cdef (hash-ref the-constants c #f))
     (if cdef
         (let ([Σ (make-hasheqv)]
               [def (constant-def cdef)])
           (unify t (constant-type cdef) Σ)
           (type-inst-in-term def Σ))
         (error 'unknown-constant))]
    [(term-app rator rand)
     (term-app (unfold c rator) (unfold c rand))]
    [(term-abs x t body)
     (term-abs x t (unfold c body))]))

(define (type-inst-in-term tm Σ)
  (match tm
    [(term-var x t) (term-var x (type-subst t Σ))]
    [(term-const c t) (term-const c (type-subst t Σ))]
    [(term-app rator rand)
     (term-app (type-inst-in-term rator Σ) (type-inst-in-term rand Σ))]
    [(term-abs x t body)
     (term-abs x (type-subst t Σ) (type-inst-in-term body Σ))]))

(define (check tm)
  (define Σ (make-hasheq))
  (define-values (checked _) (type-check tm '() Σ))
  (type-inst-in-term checked Σ))

(define (erase tm)
  (match tm
    [(term-var x _) (term-var x #f)]
    [(term-const c _) (term-const c #f)]
    [(term-app rator rand) (term-app (erase rator) (erase rand))]
    [(term-abs x t body) (term-abs x #f body)]))

(define (recheck tm)
  (check (erase tm)))

;; Get the type of a term that is assumed to be well-typed
(define (type-of tm)
  (match tm
    [(term-var _ t) t]
    [(term-const _ t) t]
    [(term-app rator rand)
     (match (type-of rator)
       [(type-app '→ (list d r)) r])]
    [(term-abs x t body)
     (type-app '→ (list t (type-of body)))]))

(define (free-in? x tm)
  (match tm
    [(term-var y _) (eqv? x y)]
    [(? term-const?) #f]
    [(term-app rator rand) (or (free-in? x rator) (free-in? x rand))]
    [(term-abs y _ body) (and (not (eqv? x y)) (free-in? x body))]))

(define (rename-free tm from to)
  (match tm
    [(term-var x t)
     (if (eqv? x from)
         (term-var to t)
         (term-var x t))]
    [(term-app rator rand)
     (term-app (rename-free rator from to)
               (rename-free rand from to))]
    [(term-abs x t body)
     (cond [(eqv? x from)
            tm]
           [(eqv? x to)
            (let ([fresh (gensym x)])
              (term-abs fresh
                        (rename-free (rename-free body x fresh)
                                     from
                                     to)))]
           [else (term-abs x t (rename-free body from to))])]
    [else tm]))

;; Here, σ is a dictionary mapping variables to well-typed terms and Σ is a type substitution.
(define (term-subst tm σ Σ)
  (match tm
    [(term-var x t)
     (define σ-x
       (dict-ref σ x #f))
     (if σ-x
         (let* ([t2 (type-of σ-x)]
                [t3 (unify t t2 Σ)])
           σ-x)
         (term-var x t))]
    [(? term-const? c) c]
    [(term-app rator rand)
     (term-app (term-subst rator σ Σ)
               (term-subst rand σ Σ))]
    [(term-abs x t body)
     (cond [(dict-ref σ x #f)
            (term-abs x t (term-subst tm (dict-remove σ x) Σ))]
           [(for/or ([new-tm (in-dict-values σ)])
              (free-in? x new-tm))
            (define z (gensym x))
            (term-abs z t (term-subst (rename-free body x z) σ Σ))]
           [else
            (term-abs x t (term-subst body σ Σ))])]))

(define (α-equiv? tm1 tm2)
  (match* (tm1 tm2)
    [((term-var x _) (term-var y _))
     (eqv? x y)]
    [((term-const c1 _) (term-const c2 _))
     (eqv? c1 c2)]
    [((term-app rator1 rand1) (term-app rator2 rand2))
     (and (α-equiv? rator1 rator2)
          (α-equiv? rand1 rand2))]
    [((term-abs x1 _ body1) (term-abs x2 _ body2))
     (α-equiv? body1 (rename-free body2 x2 x1))]
    [(_ _) #f]))

;; A set of terms. Right now, just a stupid list.
(struct term-set
  (terms)
  #:methods gen:set
  [(define (set-member? st tm)
     (for/and ([t (term-set-terms st)])
       (α-equiv? tm t)))
   (define (set-add st tm)
     (if (set-member? st tm)
         st
         (term-set (cons tm (term-set-terms st)))))
   (define (set-remove st tm)
     (term-set (remove tm (term-set-terms st) α-equiv?)))
   (define (set->list st)
     (term-set-terms st))])

(define (empty-term-set) (term-set '()))

(define (parse-term sexp)
  (define (apply-to-args tm args)
    (cond [(null? args) tm]
          [else (apply-to-args (term-app tm (car args)) (cdr args))]))
  (define (curry vars body)
    (cond [(null? vars) body]
          [else (term-abs (car vars) #f (curry (cdr vars) body))]))
  (match sexp
    [(list 'λ (list-rest x xs) body)
     (curry (cons x xs) (parse-term body))]
    [(list-rest op args)
     (apply-to-args (parse-term op) (map parse-term args))]
    [s
     #:when (symbol? s)
     (define c (dict-ref the-constants s #f))
     (if c (term-const s #f) (term-var s #f))]
    [else (error 'cant-parse)]))

(define (parse-type sexp)
  (match sexp
    [(list-rest op args)
     (define arity (dict-ref the-type-constants op #f))
     (if (and arity (= arity (length args)))
         (type-app op (map parse-type args))
         (error 'bad-type-op))]
    [(? symbol? s)
     (define arity (dict-ref the-type-constants s #f))
     (if (and arity)
         (if (= arity 0)
             (type-app s '())
             (error 'arity))
         (type-var s))]
    [else (error 'bad-type)]))

;; Definitional extensions are performed by extending the set
;; of constants.
(define (add-const name tm)
  (when (hash-ref the-constants name #f)
    (error 'already-defined))
  (define body (recheck tm))
  (define type (type-of body))
  (hash-set! the-constants name (constant type body)))

(define-syntax (define-const stx)
  (syntax-parse stx
    [(_ c:id tm)
     (syntax/loc stx
         (void (add-const 'c (parse-term 'tm))))]))

(define-const ⊤
  (= (λ (p) p) (λ (p) p)))
(define-const ∧
  (λ (p q) (= (λ (f) (f p q)) (λ (f) (f ⊤ ⊤)))))
(define-const ⇒ (λ (p q) (= (∧ p q) p)))
(define-const ∀
  (λ (P) (= P (λ (x) ⊤))))
(define-const ∃
  (λ (P)
    (∀ (λ (q)
         (⇒ (∀ (λ (x)
                 (⇒ (P x) q)))
            q)))))
(define-const ∨
  (λ (p q)
    (∀ (λ (r)
         (⇒ (⇒ p r)
            (⇒ (⇒ q r)
               r))))))
(define-const ⊥
  (∀ (λ (p) p)))
(define-const ¬
  (λ (p)
    (⇒ p ⊥)))
(define-const ∃!
  (λ (P)
    (∧ (∃ P)
       (∀ (λ (x)
            (∀ (λ (y)
                 (⇒ (∧ (P x) (P y))
                    (= x y)))))))))

