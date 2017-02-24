#lang racket

(provide (for-syntax save-hole ensure-saved-holes))

(begin-for-syntax
  (define lifted-holes? (box #f))
  (define lifted-holes (box null))
  (define (ensure-saved-holes)
    (when (and (syntax-transforming-with-lifts?)
               (not (unbox lifted-holes?)))
      (syntax-local-lift-module-end-declaration #'(the-holes))
      (set-box! lifted-holes? #t)))
  (define (save-hole hole-stx)
    (ensure-saved-holes)
    (set-box! lifted-holes
              (cons hole-stx (unbox lifted-holes)))))
(begin-for-syntax
  (struct exn:many-errs exn:fail (locations)
    #:property prop:exn:srclocs
    (lambda (exn)
      (exn:many-errs-locations exn))))

(define-syntax (the-holes stx)
  (define holes (unbox lifted-holes))
  #`(list #,@holes))

