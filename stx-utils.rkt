#lang racket

(provide leftmost)

(define (leftmost v)
  (cond
    [(pair? v) (leftmost (car v))]
    [else v]))