#lang racket

(require racket/generic)

(provide (all-defined-out))

(define-generics hypothesis
  (hypothesis-id hypothesis)
  (hypothesis-shows hypothesis)
  (hypothesis->string hypothesis))

(define-generics proof-goal
  (hypotheses proof-goal)
  (goal proof-goal)
  (goal->string proof-goal))

(define (proof-goal->string g)
  (define H (hypotheses g))
  (define G (goal g))
  (string-join
   (append
    (for/list ([h (reverse H)]
               [i (in-range (sub1 (length H)) -1 -1)])
      (format "~a. ~a" i (hypothesis->string h)))
    (list (format "⊢ ~a" (goal->string g))))
   "\n"))
