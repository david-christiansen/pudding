#lang racket/gui
(require drracket/tool framework racket/runtime-path data/interval-map)

(provide tool@)



(define-runtime-path expansion-handler.rkt "expansion-handler.rkt")

(define tool@
  (unit
    (import drracket:tool^)
    (export drracket:tool-exports^)

    (struct goal-info (start end meta))

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

    (define editor-mover (box #f))
    (define (editor-move-to pos [end 'same])
      (define f (unbox editor-mover))
      (when f
        (f pos end)))

    (define hole-info #f)
    (define (update-hole-info! [info #f])
      (set! hole-info (and info (make-interval-map info)))
      (if hole-info
          (set-goal-list (for/list ([(k v) (in-dict hole-info)])
                           (list k v)))
          (set-goal-list null)))

    (define hole-finding-text-mixin
      (mixin (racket:text<%>) ()
        (super-new)

        (inherit get-start-position set-position get-active-canvas scroll-to-position)

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
          (update-pos))

        (set-box! editor-mover
                  (lambda (pos [end 'same])
                    (queue-callback (thunk (set-position pos end)))
                    (queue-callback (thunk (scroll-to-position pos #f end)))
                    (define canvas (get-active-canvas))
                    (when canvas
                      (send canvas focus))))))

    (define extra-panel-mixin
      (mixin (drracket:unit:frame<%>) ()
        (super-new)

        (define/override (get-definitions/interactions-panel-parent)
          (define super-res (super get-definitions/interactions-panel-parent))
          (define new-panel
            (new panel:vertical-dragable% [parent super-res]))
          (define p
            (new panel:horizontal-dragable% [parent new-panel] [style '(deleted)]))
          (define msg
            (new list-box%
                 [parent p]
                 [label #f]
                 [choices (list "Hole 1" "Hole 2" "...")]
                 [style '(single)]
                 [columns '("Where")]
                 [callback (lambda (list-box evt)
                             (when (eqv? (send evt get-event-type) 'list-box)
                               (match (send list-box get-selections)
                                 [(list) (void)]
                                 [(list n)
                                  (match-define (goal-info start end meta)
                                    (send list-box get-data n))
                                  (editor-move-to start end)]
                                 [_ (void)])))]))
          (define p2
            (new group-box-panel%
                 [parent p]
                 [label "Details"]))
          (define echo-area
            (new text-field%
                 [parent p2]
                 [label #f]
                 [style '(multiple)]))

          (set-box! echoer
                    (lambda (new-msg)
                      (queue-callback (thunk (send echo-area set-value new-msg)))))

          (set-box! goal-setter
                    (lambda (gs)
                      (send msg clear)
                      (if (null? gs)
                          (send new-panel change-children (lambda (subareas)
                                                            (for/list ([area (in-list subareas)]
                                                                       #:when (not (eq? area p)))
                                                              area)))
                          (begin
                            (send new-panel change-children
                                  (lambda (subareas)
                                    (append
                                     (for/list ([area (in-list subareas)]
                                                #:when (not (eq? area p)))
                                       area)
                                     (list p))))
                            (for ([g gs])
                              (send msg append (format "~a" g) (goal-info (caar g) (cdar g) (cdr g))))))))
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



