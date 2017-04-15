#lang racket/base

(require racket/promise racket/stream (for-syntax racket/base syntax/parse))

(provide dcons unfold-dstream)

(module+ test
  (require rackunit))

;;; A dependent stream is a stream in which the cdr is computed from
;;; the value of the car when requested.

(struct depcons (first rest)
  #:methods gen:stream
  [(define (stream-empty? stream) #f)
   (define (stream-first stream)
     (force (depcons-first stream)))
   (define (stream-rest stream)
     (force (depcons-rest stream)))])

(define-syntax (dcons stx)
  (syntax-parse stx
    [(_ a:expr (x:id) d:expr)
     #'(let ([fst (delay a)])
         (depcons fst (delay ((lambda (x) d) (force fst)))))]))

(define (unfold-dstream seed step)
  (dcons seed (x) (unfold-dstream (step x) step)))

(module+ test
  (define (nats-from i)
    (dcons i (x) (nats-from (add1 x))))
  (define nats (nats-from 0))
  (check-equal? (stream-ref (stream-map add1 nats) 4) 5)

  (define more-nats (unfold-dstream 0 add1))
  (check-equal? (stream-ref more-nats 55) 55))
