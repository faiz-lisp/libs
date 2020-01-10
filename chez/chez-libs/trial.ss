
(def-syn lam* ;% @?
  (syn-ruls()
    ([_ x1 bd ...]
      (lam x2
        (redu [ev `(lam ,(flat 'x1) bd ...)] ;redu ev
          (flat x2) )
    ) )
) )

;

(def (redu~/fold g xs) ;-> curry/compose~ ;elements of xs must be simular
  (if (nilp xs) (g)
    (foldl g (car xs) (cdr xs)) ;wrong sometimes: values map echo ;echo ~> '(*v) ;evs ;i/o
) ) ;curry?

(def (curry~ g . args)
  (lam xs
    (redu~ g ;
      (append~ args xs)
) ) )
(def (rcurry~ g . args)
  (lam xs
    (redu~ g
      (append~ xs args)
) ) )

;

(def (cls) [for(42)(newln)])

(def car.ori car)
(def cdr.ori cdr)
(def (car% xs)
  (if (atomp xs) Err
    (car xs) ;.ori
) )
(def (cdr% xs)
  (if (atomp xs) Err
    (cdr xs)
) )



(defn member?@ (x xs)
  (cond
    ( [nil? xs] *f)
    ( (or [eql x (car xs)] ;
        (member? x (cdr xs))
) ) ) )


(def (repeats xs n) ;ng
  (redu (curry map li) (xn2lis xs n))
) ;仍然漏了部分重复的情况