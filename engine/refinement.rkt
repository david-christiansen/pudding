#lang racket/base

(provide (struct-out refinement))

(struct refinement (stx goal loc) #:transparent)

