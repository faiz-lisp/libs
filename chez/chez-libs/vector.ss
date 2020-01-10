

(def-syn vec-for
  (syn-ruls (in)
    ( [_ i in ve body ...]
      (quiet
        (vector-map ;
          (lambda (i)
            body ... )
          ve )
) ) ) )



(def (vec-range n)
  [def (_ n ret)
    (for (i n)
      (vector-set-fixnum! ret i i) )
    ret ]
  [_ n (make-vector n)]
)

;vec: mk-vec n; vec-fill!; vec-set! v i x; 

(def-syn (ve-push* stx)
  (syn-case stx () ;
    ([_ args ... x]
      (identifier? #'x) ;
      #'[setq x (ve-cons* args ... x)] ) ;mk-vec will slower than list's
    ([_ . args]
      #'(ve-cons* . args)
) ) )

(def (vec-nilp x) ;
  (if [vecp x]
    (=0 (veclen x))
    Fal
) )
(alias vnilp vec-nilp)

(def num->lis (curry apply/reducing-num cons))

(def vnil (vec))
(def (vec-car v) (vec-ref v 0))
(def (vecadr v) (vec-ref v 1))

(def (vec-consp v) (and (vecp v) [>0(veclen v)]))

(defn num->vec (n)   ;vec-flat ;@(lis->vec (range n))
  (let ([ve (mk-vec n)])
    (for (i n)
      (vec-set! ve i i) )
    ve
) )

(def (ve-last ve)
  (vec-ref ve [1- (veclen ve)])
)

(defn vec-cons (x vy) ;* . xxv
  (if (vecp vy)
    (let ([ve (mk-vec [1+ (veclen vy)])])
      (vec-set! ve 0 x)
      (vec-copy! ve 1 vy)
      ve
    )
    nil ;
) )
(def [ve-cons* . xxv]
  (letn ([vy (last xxv)][n (len xxv)][m (1- n)])
    (if (vecp vy)
      (let ([ve (mk-vec [+ m (veclen vy)])])
        (vec-copy! ve 0 (lis->vec [ncdr xxv -1])) ;->lis flat
        (vec-copy! ve m vy)
        ve )
      nil
) ) )
(alias vecons vec-cons)

(defn vec-conz (vx y)
  (if (vecp vx)
    (letn ([n (veclen vx)][ve (mk-vec [1+ n])])
      (vec-copy! ve 0 vx)
      (vec-set! ve n y)
      ve
    )
    nil ;
) )
(alias veconz vec-conz)

(alias vec-copy vector-copy)
(alias mk-vec make-vector)
(alias vec-len vector-length)
(alias vec-set-fnum! vector-set-fixnum!)
(alias vec-set! vector-set-fixnum!)
(alias vecar vec-car)

(def (vec-head ve n) ;
  (letn ([ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve i]) )
    ret
) )

(def (vec-tail ve m)
  (letn ([n [-(vec-len ve)m]][ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve [+ m i]]) )
    ret
) )
(def vec-cdr (rcurry vec-tail  1))
(alias vecdr vec-cdr)

(defn vec-dmap (g xs) ;
  (def [_ xs]
    (if [vec-nilp xs] vnil
      (let ([a (vecar xs)][d (vecdr xs)]) ;
        (if (vec-consp a) ;
          [vecons [_ a] [_ d]] ;flat & bump/hunch
          [vecons (g a) [_ d]]
  ) ) ) )
  [_ xs]
)

(def (vec-foldl g x ve)
  (vec-for y in ve
    [set! x (g x y)] ) ;
  x
)

(def (vec-redu g ve)
  (vec-foldl g (vec-car ve) (vecdr ve)) ;
)

(def (vec-swap! ve i j) ;!
  (let ([t 0])
    (set! t (vec-ref ve i))
    (vec-set-fnum! ve i (vec-ref ve j))
    (vec-set-fnum! ve j t)
) )

(def (vec-rev! ve)
  (letn ([n (veclen ve)] [m (1- n)] [h (quot n 2)])
    (for (i h)
      (vec-swap! ve i [- m i])
) ) )

(def vec-copy! ;
  (case-lam
    [(ve) (vec-copy ve)]
    [(des i) (vec-tail des i)]    
    [(des i src)
      [vec-copy! des i src (veclen src)] ] ;
    [(des i src n)
      (letn ([dn (veclen des)][m (min n [- dn i])])
        (for (j m)
          (vec-set! des (+ i j) (vec-ref src j)) ) ) ]
) )

(def (vec-append . vz)
  (letn ([n (len vz)][ns (map veclen vz)][ret (mk-vec [redu + ns])])
    (for (i n)
      (vec-copy! ret (redu + [list-head ns i]) (xth vz i)) )
    ret
) )



;algo for vec-sort