#lang racket

(require (for-syntax syntax/define syntax/parse racket/syntax))
(require "engine/refinement.rkt")

(provide make-stamp define-stamp sealed? local-expand-sealed)

(struct sealed (local-expander))

(define (local-expand-sealed s)
  ((sealed-local-expander s) s))

(define (make-stamp name)
  (define-values (type ctor pred acc mut)
    (make-struct-type (string->symbol (string-append (symbol->string name) "-theorem"))
                      struct:sealed 1 0 #f null #f #;(current-inspector) #f '(0) #f name))
  (define unseal (lambda (x) (acc x 0)))
  (define (local-expander x)
    (match-define (refinement stx goal loc) (unseal x))
    (seal (refinement (local-expand stx 'expression null) goal loc)))
  (define seal (lambda (x) (ctor local-expander x)))
  (values seal unseal))

(define-syntax (define-stamp stx)
  (syntax-parse stx
    [(_ name:id)
     (with-syntax ([seal (format-id #'name "seal-~a" #'name
                                    #:source #'name)]
                   [unseal (format-id #'name "unseal-~a" #'name
                                      #:source #'name)])
      (syntax/loc stx
        (define-values (seal unseal) (make-stamp 'name))))]))

(define-syntax (seal-with-barrier stx)
  (syntax-parse stx
    [(_ seal:expr e:expr)
     (syntax/loc stx
       (call-with-continuation-barrier
        (lambda ()
          (seal e))))]))

(define-syntax (barrier-under-lambda stx)
  (syntax-parse stx
    #:literals (lambda)
    [(_ stamp (lambda args body))
     (syntax/loc stx
       (lambda args (barrier-under-lambda stamp body)))]
    [(_ stamp (lambda args body ...))
     (syntax/loc stx
       (seal-with-barrier stamp (begin body ...)))]
    [(_ stamp e:expr)
     (syntax/loc stx
       (seal-with-barrier stamp e))]))

(define-syntax (define/seal stx)
  (define/syntax-parse (_ stamp name-and-args body ...) stx)
  (define-values (name expr)
    (normalize-definition #'(define name-and-args body ...) #'lambda #t #t))
  (with-syntax ([name name] [expr expr])
  (syntax/loc stx (define name (barrier-under-lambda stamp expr)))))

(module+ test
  (require rackunit syntax/macro-testing racket/control)
  (define-stamp foo)
  ;(define-values (seal-foo unseal-foo) (make-stamp 'foo))

  (define/seal seal-foo (bless f x)
    (if (eq? x 5) (error "nope") (f x)))

  (define wurble (box #f))

  (define (fake-seal x)
    (prompt (bless (lambda (z) (control k (begin (set-box! wurble k)
                                                 (k z))))
                   0)))
  (check-exn #rx"cannot capture past continuation barrier"
             (thunk (fake-seal 5))))

