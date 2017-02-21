#lang racket/gui
(require drracket/tool framework racket/runtime-path data/interval-map)

(provide tool@)

(define-runtime-path expansion-handler.rkt "expansion-handler.rkt")

(define tool@
  (unit
    (import drracket:tool^)
    (export drracket:tool-exports^)

    (struct goal-info (start end meta index) #:transparent)


    (define hole-finding-text-mixin
      (mixin (racket:text<%> drracket:unit:definitions-text<%>) ()
        (super-new)

        (inherit get-start-position set-position get-active-canvas scroll-to-position get-tab
                 position-line)

        (define (update-pos)
          (define pos (get-start-position))
          (define tab-info (hash-ref hole-info (get-tab) #f))
          (match (and hole-info
                      tab-info
                      (interval-map-ref tab-info pos #f))
            [#f (send (send (get-tab) get-frame) set-current-goal #f)]
            [(and g (goal-info _ _ _ i))
             (send (send (get-tab) get-frame) set-current-goal g)]))

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
                     v))]))

        (define/public (set-goals gs)
          (set-hole-info!
           (for/list ([g gs]
                      [i (in-range 10000)])
             (cons (cons (caar g) (cdar g))
                   (goal-info (caar g) (cdar g) (cdr g) i)))))

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

        (define current-goal-listeners (box null))
        (define/public (set-current-goal g)
          (for ([l (unbox current-goal-listeners)])
            (send l on-new-current-goal g)))

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
                   (inherit append clear get-selection select set-selection)
                   (define/public (on-new-goal-list gs)
                     (clear)
                     (define defns (get-definitions-text))
                     (for ([g gs])
                       (define line (send defns position-line (goal-info-start g)))
                       (define col (- (goal-info-start g) (send defns line-start-position line)))
                       (send hole-list-box append
                             (format "~a:~a: ~a" (add1 line) (add1 col) (goal-info-meta g))
                             g)))
                   (define/public (on-new-current-goal g)
                     (if g
                         (set-selection (goal-info-index g))
                         (let ([sel (get-selection)])
                           (when sel (select sel #f))))))
                 [parent hole-holder]
                 [label #f]
                 [choices (list)]
                 [style '(single)]
                 [columns '("Where")]
                 [callback (lambda (list-box evt)
                             (when (eqv? (send evt get-event-type) 'list-box)
                               (match (send list-box get-selections)
                                 [(list) (void)]
                                 [(list n)
                                  (match-define (goal-info start end meta _)
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
          (define details
            (new (class text-field%
                   (super-new)
                   (inherit set-value)
                   (define/public (on-new-current-goal g)
                     (if g
                         (set-value (format "Goal ~a:\n\t~a" (goal-info-index g) (goal-info-meta g)))
                         (set-value ""))))
                 [parent p2]
                 [label #f]
                 [style '(multiple)]))

          (set-box! goal-list-listeners (list hole-list-box new-panel))
          (set-box! current-goal-listeners (list hole-list-box details))

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



