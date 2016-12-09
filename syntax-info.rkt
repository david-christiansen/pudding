#lang racket

(provide (struct-out syntax-info)
         syntax-loc
         partial-syntax-loc)

(struct syntax-info (source position span)
  #:prefab)

(define (syntax-loc stx)
  (syntax-info (syntax-source stx) (syntax-position stx) (syntax-span stx)))

(define (partial-syntax-loc stx)
  (syntax-info (syntax-source stx) (syntax-position stx) #f))
