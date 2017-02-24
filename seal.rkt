#lang racket

(require (for-syntax syntax/define syntax/parse)
         racket/control)

(provide logic logic-name unseal)

(struct logic (name injection projection))

(define (make-logic name)
  (define-values (type ctor pred acc mut)
    (make-struct-type (string->symbol (string-append (symbol->string name) "-theorem"))
                      #f 1 0 #f null (current-inspector) #f '(0) #f name))
  (logic name ctor (lambda (x) (acc x 0))))

(define (seal logic v)
  ((logic-injection logic) v))


(define (unseal logic v)
  ((logic-projection logic) v))



(define-syntax (seal-with-barrier stx)
  (syntax-parse stx
    [(_ logic:expr e:expr)
     #'(call-with-continuation-barrier (lambda () (seal logic e)))]))

(define-syntax (barrier-under-lambda stx)
  (syntax-parse stx
    #:literals (lambda)
    [(_ logic (lambda args body))
     #'(lambda args (barrier-under-lambda logic body))]
    [(_ logic (lambda args body ...))
     #'(seal-with-barrier logic (begin body ...))]
    [(_ logic e:expr) #'(seal-with-barrier logic e)]))

(define-syntax (define/seal stx)
  (define/syntax-parse (_ logic name-and-args body ...) stx)
  (define-values (name expr)
    (normalize-definition #'(define name-and-args body ...) #'lambda #t #t))
  (with-syntax ([name name] [expr expr])
  (syntax/loc stx (define name (barrier-under-lambda logic expr)))))

(define foo (make-logic 'foo))

(define/seal foo (bless f x)
  (if (eq? x 5) (error "nope") (f x)))

(define wurble (box #f))

(define (fake-seal x)
  (prompt (bless (lambda (z) (control k (begin (set-box! wurble k)
                                               (k z))))
                 0)))

