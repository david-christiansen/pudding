#lang racket/base

(require racket/contract)

(provide make-rstream list->rstream rstream-forever
         rstream-next
         rstream-snapshot rstream-rewind!)

(module+ test
  (require rackunit))

(struct rstream (contents))

(define the-streams (box (make-weak-hasheq)))

(define/contract (make-rstream contents)
  (-> (-> exact-nonnegative-integer? any/c) rstream?)
  (define s (rstream contents))
  (hash-set! (unbox the-streams) s 0)
  s)

(define (rstream-next s)
  (define pos (hash-ref (unbox the-streams) s))
  (hash-set! (unbox the-streams) s (add1 pos) )
  ((rstream-contents s) pos))

(define (rstream-snapshot)
  (hash-copy (unbox the-streams)))

(define (rstream-rewind! snapshot)
  (for ([(s pos) (in-hash snapshot)])
    (hash-set! (unbox the-streams) s pos)))

(define (rstream-forever x)
  (make-rstream (lambda (i) x)))

(define (list->rstream xs (default #f))
  (define l (length xs))
  (make-rstream (lambda (i)
                  (if (< i l)
                      (list-ref xs i)
                      default))))

(module+ test
  (define nums (list 1 2 3 4 5))
  (define num-stream (list->rstream nums))
  (check-equal? (rstream-next num-stream) 1)
  (check-equal? (rstream-next num-stream) 2)
  (check-equal? (rstream-next num-stream) 3)
  (define s (rstream-snapshot))
  (check-equal? (rstream-next num-stream) 4)
  (check-equal? (rstream-next num-stream) 5)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f)
  (rstream-rewind! s)
  (check-equal? (rstream-next num-stream) 4)
  (check-equal? (rstream-next num-stream) 5)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f)
  (rstream-rewind! s)
  (check-equal? (rstream-next num-stream) 4)
  (check-equal? (rstream-next num-stream) 5)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f)
  (check-equal? (rstream-next num-stream) #f))
