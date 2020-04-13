
(defsyn defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( [_ f args body ...]
    (define f
      (eval ;
        (foldr
          [lam(a b)(append~ a (list b))]
          `(lam() body ...)
          [map (lam(x)`(lam(,x))) 'args] ;
) ) ) ) )
(defsyn defn-snest ;(lam(a)(lam(b) body...))
  ( [_ f args body ...]
    (define f
      (eval
        (foldr
          [lam(a b) (append a (list b))]
          `(bgn body ...)
          (map [lam(x) `(lam (,x) )] 'args) ;
) ) ) ) )

(defsyn lam-nest% ;(_ (a b) bd...) -> [lam(a)[lam(b) bd...]]
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    [lam(x) (lam-nest% (ys ...) [ret ...])] ) ;
)
(defsyn lam-rnest%
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    (lam-rnest% (ys ...) [lam(x) [ret ...]]) )
)

(defsyn lam-rnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) [lam() bd ...]] )
)
(defsyn lam-srnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) (bgn bd ...)] )
)
(defsyn lam-nest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [lam() bd ...]] )
)
(defsyn lam-snest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [bgn bd ...]] )
)

(defn call-nest (g . xs)
  (defn ~ (g xs)
    (if (nilp xs) (g)
      (~ (g (car xs)) (cdr xs))
  ) )
  (~ g xs)
)
(alias callnest call-nest)

(defn call-snest (g . ys)
  (defn ~ (g ys)
    (if (nilp ys) g
      [~ (g (car ys)) (cdr ys)]
  ) )
  (~ g ys)
)
(alias callsnest call-snest)