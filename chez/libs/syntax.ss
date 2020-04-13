
(def-syn defsyn
  (syn-ruls ()
    ( [_ f (expr body ...)] ;;;one ;must be bef (_ f g), or will make wrong meanings
      (def-syn f
        (syn-ruls ()
          (expr
            (bgn body ...) ) ) ) ) ;
    ( [_ f g]
      (def-syn f
        (syn-ruls ()
          ( [_ . args] ;
            (g . args) ) ) ) )
    ( [_ f (expr ...) ...]   ;multiple
      (def-syn f
        (syn-ruls ()
          ( expr
            ...
          )
          ...
) ) ) ) )
(ali defsyt defsyn)


;sy-

(defsyn sy-rev% ;
  ([_ () (ret ...)] nil)
  ([_ (x) (ret ...)]
    '(x ret ...) )
  ([_ (x ys ...) (ret ...)]
    (sy-rev% [ys ...] [x ret ...]) )
)
(defsyn sy-rev
  ([_ (xs ...)]
    [sy-rev% (xs ...) ()] )
  ([_ xs ...]
    [sy-rev% (xs ...) ()] )
)


;quo/sym-

(define (sym-redu sym-f xs) ;(quo-redu 'setq '(a 1))
  (ev (cons sym-f xs)) ;
  ;(ev `(sym-f ,@xs)) ;map-q 1st-q
)