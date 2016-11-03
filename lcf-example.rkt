#lang racket

(struct refinement (subgoals validation)
  #:transparent)

(struct exn:fail:refinement exn:fail (rule goal)
  #:extra-constructor-name make-exn:fail:refinement)

(define (raise-refinement-error rule msg goal)
  (raise (make-exn:fail:refinement
          (format "~a: ~s with goal ~s" rule msg goal)
          (current-continuation-marks)
          rule
          goal)))

;; Sequents
(struct ⊢ (hypotheses goal) #:transparent)

;; Goal AST
(struct Int () #:transparent)
(struct String () #:transparent)
(struct → (dom cod) #:transparent)

(define ((int-intro i) goal)
  (match goal
    [(⊢ _ (Int))
     (if (integer? i)
         (refinement null (lambda () (datum->syntax #'here i)))
         (raise-refinement-error 'int-intro "Not an integer" goal))]
    [_ (raise-refinement-error 'int-intro "Wrong goal" goal)]))

(define (plus goal)
  (match goal
    [(⊢ H (Int))
     (refinement (list (⊢ H (Int)) (⊢ H (Int)))
                 (lambda (x y)
                   (with-syntax ([x x] [y y])
                       #'(+ x y))))]
    [_ (raise-refinement-error 'plus "Wrong goal" goal)]))

(define ((→-intro x) goal)
  (match goal
    [(⊢ H (→ a b))
     #:when (not (assoc x H))
     (refinement (list (⊢ (cons (cons x a) H) b))
                 (lambda (body)
                   (with-syntax ([x x] [body body])
                     #'(lambda (x) body))))]
    [_ (raise-refinement-error '→-intro "Wrong goal" goal)]))


(define-match-expander at-hyp
  (lambda (stx)
    (syntax-case stx ()
        [(_ i before this-hyp after)
         #'(? (lambda (H) (> (length H) i))
              (app (lambda (H) (split-at H i))
                   before
                   (cons this-hyp after)))])))

(define ((assumption n) goal)
  (match goal
    [(⊢ (at-hyp n Δ (cons x a) Γ) G)
     #:when (equal? a G)
     (refinement null (lambda () (datum->syntax #f x)))]
    [_ (raise-refinement-error 'assumption "Wrong goal" goal)]))


;;;; Tacticals from LCF paper
(define (ID goal) (refinement (list goal) (lambda (x) x)))

(define ((ORELSE t1 t2) goal)
  (with-handlers ([exn:fail:refinement? (lambda (e) (t2 goal))])
    (t1 goal)))

(define (splits lengths lst)
  (cond
    [(null? lengths)
     (list lst)]
    [(pair? lengths)
     (let-values ([(here rest) (split-at lst (car lengths))])
       (cons here (splits (cdr lengths) rest)))]))

(define ((THEN t1 t2) goal)
  (match (t1 goal)
    [(refinement subs rebuild)
     (let ([new-subs (map t2 subs)])
       (refinement
        (apply append (map refinement-subgoals new-subs))
        (lambda xs
          (apply rebuild
                 (for/list ([out (in-list (splits (map (compose length refinement-subgoals)
                                                       new-subs)
                                                  xs))]
                            [sub-refinement new-subs])
                   (apply (refinement-validation sub-refinement) out))))))]))

(define ((REPEAT t) g)
  ((ORELSE (THEN t (REPEAT t)) ID) g))

;;; Not in the paper, but really handy
(define ((THENL t1 t2s) goal)
  (match (t1 goal)
    [(refinement subs rebuild)
     (let ([new-subs (for/list ([t t2s]
                                [subgoal subs])
                       (t subgoal))])
       (refinement
        (apply append (map refinement-subgoals new-subs))
        (lambda xs
          (apply rebuild
                 (for/list ([out (in-list (splits (map (compose length refinement-subgoals)
                                                       new-subs)
                                                  xs))]
                            [sub-refinement new-subs])
                   (apply (refinement-validation sub-refinement) out))))))]))

(define (run-proof tactic goal)
  (if (not (⊢? goal))
      (run-proof tactic (⊢ null goal))
      ((refinement-validation (tactic goal)))))

(define demo1 (run-proof (THEN (→-intro 'x) (assumption 0)) (→ (Int) (Int))))
(define demo2 (run-proof (THENL (THEN (→-intro 'x) plus)
                                (list (assumption 0) (int-intro 1)))
                         (→ (Int) (Int))))