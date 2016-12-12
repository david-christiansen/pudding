#lang racket

(require racket/generic)

(provide (all-defined-out))

(define-generics hypothesis
  (hypothesis-id hypothesis)
  (hypothesis-shows hypothesis)
  (hypothesis->string hypothesis))

(define-generics proof-goal
  (hypotheses proof-goal)
  (goal proof-goal))

(define (proof-goal->string g)
  (define H (hypotheses g))
  (define G (goal g))
  (string-join
   (append
    (for/list ([h (reverse H)]
               [i (in-range (length H) 0 -1)])
      (format "~a. ~a" i (hypothesis->string h)))
    (list (format "⊢ ~a" (syntax->datum G))))
   "\n"))
