
(def (len* x)
  ((if* [str? x] string-length
        [vecp x] vector-length
        [nump x] (rcurry nbits 10)
    length )
    x
) )
(def len%
  (case-lam
    [(x) (len* x)]
    [(x base)
      ;(if (nump x)
        (nbits x base) ;)
    ]
) )




(def (len-cmp f . xs) [redu f (map len xs)]) ;redu? len*?


(def (len0? x) (= (len x) 0))
(ali len0 len0?)
(def len>0 (compose >0 len))
(def len<0 (compose <0 len))
(def len>=0 (compose >=0 len))
(def len<=0 (compose <=0 len))
(def len1   (compose =1 len))
(def len>1 (compose >1 len))
(def len<1 (compose <1 len))
(def len>=1 (compose >=1 len))
(def len<=1 (compose <=1 len))


(def len-1 (compose 1- len))