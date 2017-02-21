#lang racket

(provide build-goal-info handle-expansion)

(require syntax/parse
         "syntax-info.rkt")

;; Need to ensure non-false values are put in the goal-table
(struct wrap (prop) #:prefab)

;; traverse fully expanded syntax and produce a list suitable for building
;; an interval-map. This maps intervals of if expressions to information
;; about their syntax to swap the then/else branches and negate the test
(define (build-goal-info stx source)
  (define goal-info (make-hash))
  (let loop ([stx stx])
    (define prop (syntax-property stx 'goal))
    (when (and prop (equal? source (syntax-source stx)))
      (hash-update! goal-info
                    (syntax-loc stx)
                    (λ (old)
                      (define new-span (syntax-span stx))
                      (cond
                        [old
                         (match-define (wrap old-prop) old)
                         (wrap (and (equal? old-prop prop) old-prop))]
                        [else (wrap prop)]))
                    #f))
    (when (syntax->list stx)
      (for ([sub-stx (in-syntax stx)])
        (loop sub-stx))))
  (build-pre-interval-map goal-info))

(define (build-pre-interval-map table)
  (sort (for*/list ([(k v) (in-hash table)]
                    [prop (in-value (wrap-prop v))]
                    #:when prop)
          (match-define (syntax-info _ pos span) k)
          (cons (cons (sub1 pos) (sub1 (+ pos span)))
                prop))
        (match-lambda**
         [((cons start1 end1) (cons start2 end2))
          (or (< start1 start2)
              (and (= start1 start2)
                   (>= end1 end2)))])
        #:key car))

(define (handle-expansion stx path source cust)
  (and (syntax? stx)
       (build-goal-info stx source)))
