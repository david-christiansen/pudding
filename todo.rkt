#lang racket

(define-syntax (todo stx)
  (syntax-property (syntax/loc stx (error 'todo)) 'goal (syntax->datum stx)))


(define x (todo 'hey) )