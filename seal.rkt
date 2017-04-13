#lang racket

(require (for-syntax syntax/define syntax/parse racket/syntax))
(require "engine/refinement.rkt")

(provide make-stamp define-stamp sealed?)

(struct sealed ())

(define (make-stamp name)
  (define-values (type ctor pred acc mut)
    (make-struct-type (string->symbol (string-append (symbol->string name) "-theorem"))
                      struct:sealed 2 0 #f null #f #;(current-inspector) #f '(0) #f name))
  (define unseal-name (string->symbol (format "unseal-~a" name)))
  (define seal-name (string->symbol (format "seal-~a" name)))

  (define unseal
    (procedure-rename
     (lambda (goal x)
       (if (eq? goal (acc x 1))
           (acc x 0)
           (raise-argument-error unseal-name (format "A validation for goal ~a" (acc x 1)) 1 goal x)))
     unseal-name))
  (define seal
    (procedure-rename
     (lambda (goal x) (ctor x goal))
     seal-name))
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

