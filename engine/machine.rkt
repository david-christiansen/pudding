#lang racket

(provide (struct-out ID)
         (struct-out THEN)
         (struct-out THENL)
         (struct-out ORELSE)
         (struct-out FAIL)
         (struct-out TACTIC)
         LCF?

         (struct-out LCF-state)

         (struct-out THEN-frame)
         (struct-out THENL-frame)
         (struct-out ORELSE-frame)
         LCF-frame?)

;; Abstract syntax of core tactic language. Nodes in the AST may,
;; however, be lazily generated, allowing for circular tactic
;; programs.
(struct LCF () #:transparent)
(struct ID LCF () #:transparent)
(struct THEN LCF (first second) #:transparent)
(struct THENL LCF (first seconds) #:transparent)
(struct ORELSE LCF (tactic fallback) #:transparent)
(struct FAIL LCF (message) #:transparent)
;; Here, tactic is a (-> hole-stx (-> nat goal hole-stx) sealed-hole-stx)
(struct TACTIC LCF (tactic) #:transparent)

;; The state of the machine has two parts: an explicit machine state,
;; and an implicit context given by macro expansion. The continuation
;; is given as a list of frames.
;; Here's the explicit part of the state.
(struct LCF-state (control continuation goal) #:transparent)

;; Continuation frames
(struct LCF-frame () #:transparent)
(struct THEN-frame LCF-frame (second) #:transparent)
(struct THENL-frame LCF-frame (seconds) #:transparent)
;; Because the state of the abstract machine is partially implicit,
;; failure handling must capture a Racket continuation. This is stored
;; in cont.
(struct ORELSE-frame LCF-frame (cont) #:transparent)
