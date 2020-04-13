
(def-syn (if% stx)
  (syn-case stx (else)
    ([_ () (bd ...)]
    #'(cond bd ...) )
    ([_ (last-expr) (bd ...)]
    #'(if% () (bd ... [else last-expr])) )
    ([_ (k e more ...) (bd ...)]
    #'(if% (more ...) (bd ... [k e])) )
) )
(def-syn (if* stx)
  (syn-case stx ()
    ([_ bd ...]
      #'(if% [bd ...] []) ;
      ;#'[sy-redu cond (group (bd ...) 2)] ;sy-group
) ) )
(ali if~ if*)