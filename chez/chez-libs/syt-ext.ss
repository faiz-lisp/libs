
(defm (sy-redu g (x ...))
  (g x ...)
)

;

(defsyn sy/num-not-defa-vals%
  ([_ () n] n)
  ([_ ((x vx)) n]       (sy/num-not-defa-vals% () n))
  ([_ (x) n]            (sy/num-not-defa-vals% () (fx1+ n)))
  ([_ ((x vx) y ...) n] (sy/num-not-defa-vals% (y ...) n))
  ([_ (x y ...) n]      (sy/num-not-defa-vals% (y ...) (fx1+ n))) ;
)
(defsyn sy/num-not-defa-vals
  ([_ . xs] (sy/num-not-defa-vals% xs 0))
)
