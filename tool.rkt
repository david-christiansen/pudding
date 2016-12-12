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


    (define hole-finding-text-mixin
      (mixin (racket:text<%> drracket:unit:definitions-text<%>) ()
        (super-new)

        (inherit get-start-position set-position get-active-canvas scroll-to-position get-tab)

        (define (update-pos)
          (define pos (get-start-position))
          (define tab-info (hash-ref hole-info (get-tab) #f))
          (define h (and hole-info
                         tab-info
                         (interval-map-ref tab-info pos #f)))
          (if h
              (echo (format "Pos: ~a, hole: ~a" pos h))
              (echo (format "Pos: ~a" pos))))

        (define hole-info (make-hasheq))
        (define (set-hole-info! [info #f])
          (define tab (get-tab))
          (hash-set! hole-info tab
                     (and info (make-interval-map info)))
          (update-hole-info!))

        (define/public (update-hole-info!)
          (define tab (get-tab))
          (define frame (send tab get-frame))
          (match (hash-ref hole-info tab #f)
            [#f (send frame set-goal-list
                    null)]
            [info
             (send frame set-goal-list
                   (for/list ([(k v) (in-dict info)])
                     (list k v)))]))

        (define/public (set-goals gs)
          (set-hole-info! gs))

        (define/augment (after-set-position)
          (update-pos))))

    (define extra-panel-mixin
      (mixin (drracket:unit:frame<%>) ()

        (inherit get-definitions-text)

        (define/augment (on-tab-change from to)
          (send (get-definitions-text) update-hole-info!))

        (define goal-list-listeners (box null))
        (define/public (set-goal-list gs)
          (for ([l (unbox goal-list-listeners)])
            (send l on-new-goal-list gs)))

        (define/override (get-definitions/interactions-panel-parent)
          (define super-res (super get-definitions/interactions-panel-parent))
          (define new-panel
            (new (class panel:vertical-dragable%
                   (super-new)
                   (inherit change-children)
                   (define/public (on-new-goal-list gs)
                     (change-children
                      (lambda (subareas)
                        (append
                         (for/list ([area (in-list subareas)]
                                    #:when (not (eq? area hole-holder)))
                           area)
                         (if (null? gs)
                             null
                             (list hole-holder)))))))
                 [parent super-res]))
          (define hole-holder
            (new panel:horizontal-dragable% [parent new-panel] [style '(deleted)]))
          (define hole-list-box
            (new (class list-box%
                   (super-new)
                   (inherit append clear)
                   (define/public (on-new-goal-list gs)
                     (clear)
                     (for ([g gs])
                       (send hole-list-box append
                             (format "~a" g) (goal-info (caar g) (cdar g) (cdr g))))))
                 [parent hole-holder]
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
                                  (define defns (get-definitions-text))
                                  (queue-callback (thunk (send* defns
                                                           (set-position start end)
                                                           (scroll-to-position start #f end))
                                                         (define canvas (send defns get-active-canvas))
                                                         (when canvas (send canvas focus))))]
                                 [_ (void)])))]))

          (define p2
            (new group-box-panel%
                 [parent hole-holder]
                 [label "Details"]))
          (define echo-area
            (new text-field%
                 [parent p2]
                 [label #f]
                 [style '(multiple)]))

          (set-box! goal-list-listeners (list hole-list-box new-panel))

          (set-box! echoer
                    (lambda (new-msg)
                      (queue-callback (thunk (send echo-area set-value new-msg)))))
          new-panel)

        (super-new)))

    (define (phase1) (void))
    (define (phase2) (void))

    (drracket:get/extend:extend-definitions-text hole-finding-text-mixin)
    (drracket:get/extend:extend-unit-frame extra-panel-mixin)
    (drracket:module-language-tools:add-online-expansion-handler
     expansion-handler.rkt
     'handle-expansion
     (λ (text info)
       (send text set-goals info)))))



