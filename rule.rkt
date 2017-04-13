#lang racket/base

(require (for-syntax racket/base racket/match "engine/proof-state.rkt" "goal.rkt" "engine/machine.rkt"
                     (for-syntax racket/base syntax/parse))
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
         (TACTIC
          (lambda (hole make-subgoal fk)
            (struct exn:fail:this-rule exn:fail ()
              #:extra-constructor-name make-exn:fail:this-rule)
            (define subgoal-count
              (let ([i (box 0)])
                (lambda ()
                  (define j (unbox i))
                  (set-box! i (add1 j))
                  j)))
            (define (sub g) (make-subgoal (subgoal-count) hole g))
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
                                 (fk (exn-message e)))]
                              [exn:fail:syntax?
                               (λ (e) (fk (exn-message e)))])
                (define the-goal (get-hole-goal hole))
                (match the-goal
                  [goal-pat #:when opts.when
                            (contract (λ (x) (not (void? x)))
                                      (call-with-continuation-barrier
                                       (lambda () result ... (opts.seal the-goal last-result)))
                                      '#,stx
                                      'the-rule-macro)]
                  [other (fk (format "Wrong goal:\n~a" other))]))))))])))
