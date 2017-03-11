#lang racket

(provide (for-syntax tooltip-info))
(require "lift-tooltips.rkt" (for-syntax "engine/proof-state.rkt"))

(define-for-syntax (tooltip-info show)
  (lambda (loc goal)
    (when loc
      (save-tooltip (string-append (format "~a\n" (syntax->datum loc))
                                   (show goal))
                    loc))))
