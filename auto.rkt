#lang racket/base
(require (for-syntax racket/base
                     racket/contract)
         "lcfish.rkt"
         "engine/hole.rkt")

(provide (for-syntax auto-tactics register/auto auto))

(begin-for-syntax
  (define/contract auto-tactics
    (parameter/c tactic/c (listof tactic/c))
    (make-parameter (list (fail "Can't auto."))
                    (lambda (new-tac)
                      (cons new-tac (auto-tactics)))))

  (define/contract (register/auto . tacs)
    (->* () #:rest (listof tactic/c) void?)
    (for ([t (in-list tacs)])
      (auto-tactics t)))
  
  (define/contract (auto (extras '()))
    (->* () ((listof tactic/c)) tactic/c)
    (define tactics (append extras (auto-tactics)))
    (if (pair? tactics)
        (apply try* tactics)
        (fail "No auto tactics available"))))