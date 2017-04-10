#lang racket/base

(require (for-syntax racket/base racket/match "engine/proof-state.rkt"  "goal.rkt"
                     (for-syntax racket/base syntax/parse))
         "engine/hole.rkt"
          "lcfish.rkt"
          (for-syntax racket/contract)
         racket/match (for-syntax racket/stxparam) racket/control)

(provide (for-syntax subgoal not-applicable rule))

(begin-for-syntax

  (begin-for-syntax
    (define-splicing-syntax-class rule-options
      (pattern (~seq #:when when #:seal seal))
      (pattern (~seq #:seal seal #:when when))
      (pattern (~seq #:seal seal)
               #:with when #'#t)
      (pattern (~seq #:when when)
               #:with seal #'(lambda (x) x))
      (pattern (~seq)
               #:with when #'#t
               #:with seal #'(lambda (x) x))))

  (define-syntax-parameter subgoal
    (lambda (_) (raise-syntax-error 'subgoal "Not in a rule")))

  (define-syntax-parameter not-applicable
    (lambda (_)
      (raise-syntax-error 'not-applicable "Not in a rule")))

  (define-syntax (rule stx)
    (syntax-parse stx
      [(_ goal-pat opts:rule-options result ... last-result)
       (quasisyntax/loc stx
         (tactic
          (lambda (hole make-subgoal)
            (struct exn:fail:this-rule exn:fail ()
              #:extra-constructor-name make-exn:fail:this-rule)
            (define subgoal-count ;; TODO: move the counter to metaprogramming-time
              (let ([i (box 0)])
                (lambda ()
                  (define old-i (unbox i))
                  (set-box! i (add1 old-i))
                  old-i)))
            (define (sub g)
              (subgoal-with-tactic hole g (make-subgoal (subgoal-count))))
            (syntax-parameterize ([subgoal (make-rename-transformer #'sub)]
                                  [not-applicable
                                   (lambda (nope-stx)
                                     (syntax-case nope-stx ()
                                       [(_ msg arg (... ...))
                                        #'(raise (make-exn:fail:this-rule
                                                  (format msg arg (... ...))
                                                  (current-continuation-marks)))]
                                       [(_)
                                        #'(raise (make-exn:fail:this-rule
                                                  (string-append
                                                   "Not applicable:\n"
                                                   (proof-goal->string (get-hole-goal hole)))
                                                  (current-continuation-marks)))]))])
              (with-handlers ([exn:fail:this-rule?
                               (lambda (e)
                                 ((fail (exn-message e)) hole make-subgoal))]
                              [exn:fail:syntax?
                               (λ (e) ((fail (exn-message e)) hole make-subgoal))])
                (match (get-hole-goal hole)
                  [goal-pat #:when opts.when
                            (contract (λ (x) (not (void? x)))
                                      (call-with-continuation-barrier
                                       (lambda () result ... (opts.seal (refine hole last-result))))
                                      '#,stx
                                      'the-rule-macro)]
                  [other ((fail (format "Wrong goal:\n~a" other)) hole make-subgoal)]))))))])))
