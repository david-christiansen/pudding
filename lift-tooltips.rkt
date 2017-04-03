#lang racket

(require (for-syntax syntax/srcloc))
(provide (for-syntax save-tooltip ensure-lifted-tooltips))

(begin-for-syntax
  (define lifted-tooltips? (box #f))
  (define lifted-tooltips (box null))
  (define (ensure-lifted-tooltips)
    (when (and (syntax-transforming-with-lifts?) (not (unbox lifted-tooltips?)))
      (syntax-local-lift-module-end-declaration #'(tooltips))
      (set-box! lifted-tooltips? #t)))

  (define-logger online-check-syntax)
  
  (define (save-tooltip msg where)
    (ensure-lifted-tooltips)
    (define tooltip
      (vector where
              (sub1 (source-location-position where))
              (+ (sub1 (source-location-position where))
                 (source-location-span where))
              msg))
    (log-message online-check-syntax-logger
                 'info
                 "tooltip"
                 (list (syntax-property #'(void) 'mouse-over-tooltips tooltip)))
    (set-box! lifted-tooltips
              (cons tooltip (unbox lifted-tooltips)))))

(define-syntax (tooltips stx)
  (syntax-property #'(void)
                   'mouse-over-tooltips
                   (unbox lifted-tooltips)))

(define-syntax (self-tooltip stx)
  (save-tooltip (format "Source: ~a" (syntax->datum stx)) stx)
  (syntax-case stx ()
    [(_ e) #'e]))

(define-syntax (local-self-tooltip stx)
  (syntax-case stx ()
    [(_ e)
     (local-expand (syntax/loc stx (self-tooltip e)) 'expression null)
     #'(void)]))

(void (local-self-tooltip (+ 1 1)))
(void (self-tooltip 3))
