#lang racket

(provide (for-syntax save-error ensure-error-reports))

(begin-for-syntax
  (define lifted-errors? (box #f))
  (define lifted-errors (box null))
  (define (ensure-error-reports)
    (when (and (syntax-transforming-with-lifts?)
               (not (unbox lifted-errors?)))
      (syntax-local-lift-module-end-declaration #'(report-errors))
      (set-box! lifted-errors? #t)))
  (define (save-error exn)
    (ensure-error-reports)
    (set-box! lifted-errors
              (cons exn (unbox lifted-errors)))))
(begin-for-syntax
  (struct exn:many-errs exn:fail (locations)
    #:property prop:exn:srclocs
    (lambda (exn)
      (exn:many-errs-locations exn))))

(define-syntax (report-errors stx)
  (define exns (unbox lifted-errors))
  (define where
    (for/list ([exn (in-list exns)]
               #:when (exn:srclocs? exn)
               [loc ((exn:srclocs-accessor exn) exn)])
      loc))
  
  (if (not (null? where))
      (raise (exn:many-errs (format "~a issues found" (length exns))
                            (current-continuation-marks)
                            '()
                            #;where))
      #'(void)))

