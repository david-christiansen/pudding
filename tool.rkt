#lang racket/gui
(require drracket/tool framework racket/runtime-path data/interval-map)

(provide tool@)


(define-runtime-path expansion-handler.rkt "expansion-handler.rkt")

(define tool@
  (unit
    (import drracket:tool^)
    (export drracket:tool-exports^)

    (define echoer (box #f))
    (define (echo msg)
      (define f (unbox echoer))
      (when f
        (f msg)))

    (define goal-setter (box #f))
    (define (set-goal-list gs)
      (define f (unbox goal-setter))
      (when f
        (f gs)))

    (define hole-info #f)
    (define (update-hole-info! [info #f])
      (set! hole-info (and info (make-interval-map info))))

    (define hole-finding-text-mixin
      (mixin (racket:text<%>) ()
        (super-new)

        (inherit get-start-position)

        (define (update-pos)
          (define pos (get-start-position))
          (define h (and hole-info
                         (interval-map-ref hole-info pos #f)))
          (if h
              (echo (format "Pos: ~a, hole: ~a" pos h))
              (echo (format "Pos: ~a" pos))))

        (define/public (set-goals gs)
          (update-hole-info! gs)

          (echo (format "Goals: ~a" gs)))

        (define/augment (after-set-position)
          (update-pos))))

    (define extra-panel-mixin
      (mixin (drracket:unit:frame<%>) ()
        (super-new)

        (define/override (get-definitions/interactions-panel-parent)
          (define super-res (super get-definitions/interactions-panel-parent))
          (define new-panel
            (new panel:vertical-dragable% [parent super-res]))
          (define p
            (new panel:horizontal-dragable% [parent new-panel]))
          (define msg
            (new list-box%
                 [parent p]
                 [label #f]
                 [choices (list "Hole 1" "Hole 2" "...")]
                 [style '(single)]
                 [columns '("Where")]))
          (define p2
            (new group-box-panel%
                 [parent p]
                 [label "Details"]))
          (define echo-area
            (new text-field%
                 [parent p2]
                 [label "Echo area"]))

          (set-box! echoer
                    (lambda (new-msg)
                      (send echo-area set-value new-msg)))

          (set-box! goal-setter
                    (lambda (gs)
                      (void)
                      ))
          new-panel)))

    (define (phase1) (void))
    (define (phase2) (void))

    (drracket:get/extend:extend-definitions-text hole-finding-text-mixin)
    (drracket:get/extend:extend-unit-frame extra-panel-mixin)
    (drracket:module-language-tools:add-online-expansion-handler
         expansion-handler.rkt
         'handle-expansion
         (λ (text info)
           (send text set-goals info)))))



