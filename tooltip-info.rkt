#lang racket/base

(provide (for-syntax tooltip-info))
(require "lift-tooltips.rkt" (for-syntax "engine/proof-state.rkt" racket/match racket/base))

(define-for-syntax (tooltip-info show)
  (lambda (loc goal mode)
    (when loc
      (save-tooltip (lambda ()
                      (string-append (format "~a: ~a\n"
                                             (match mode
                                               ['in "In"]
                                               ['out "Out"])
                                             (syntax->datum loc))
                                     (show goal)))
                    loc))))
