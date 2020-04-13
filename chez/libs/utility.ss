
(defn ~remov-same (xs) ;@
  (def (_ xs ts)
    (if (nilp xs) ts
      (let ([a(car xs)] [d(cdr xs)])
        (if (mem? a ts) ;
          [_ d ts]
          [_ d (cons a ts)] ;
  ) ) ) )
  [_ xs nil]
)

;(def/defa (remov-1? x xs [g eql])
;(def/defa (remov-1?/g x xs [g eql])
;(defa-def (remov-1?/g [x] [xs] [g eql])
(def (remov-1?/g x xs g) ;result / #f
  (call/cc (lam [k]
      (def (_ xs)
        (if (nilp xs) [k Fal]
          (let ([a(car xs)] [d(cdr xs)])
            (if (g a x) d
              (cons a [_ d])
      ) ) ) )
      (_ xs)
) ) )



(def (remov-nil xs)
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)] [d (cdr xs)])
        (if (nilp a)
          [_ d]
          (cons a [_ d]) ;
  ) ) ) )
  [_ xs]
)
(def (~remov-nil xs)
  (def (_ xs ret)
    (if (nilp xs) ret
      (let ([a(car xs)] [d(cdr xs)])
        (if (nilp a)
          [_ d ret]
          [_ d (cons a ret)]
  ) ) ) )
  [_ xs nil]
)

(def (remov-1 x xs)
  (let ([g (eq/eql x)]) ;
    (def (_ xs)
      (if (nilp xs) nil
        (let ([a(car xs)] [d(cdr xs)])
          (if (g a x) d
            (cons a [_ d])
    ) ) ) )
    (_ xs)
) )
(def (remov-all x xs)
  ;
  (let ([g (eq/eql x)]) ;
    (def (_ xs)
      (if (nilp xs) nil
        (let ([a (car xs)] [d (cdr xs)])
          (if (g a x) ;
            [_ d]
            (cons a [_ d])
    ) ) ) )
    (_ xs)
) )

(def (remov-n x xs n)
  (let ([g (eq/eql x)])
    (def [_ xs n]
      (if [or (= n 0) (nilp xs)] xs ;
        (if* [< n 0] [remov-all x xs] ;g
          [= n 1] [remov-1 x xs]
          (let ([a (car xs)] [d (cdr xs)])
            (if (g a x)
              [_ d (1- n)]
              (cons a [_ d n]) ;
    ) ) ) ) )
    [_ xs n]
) )

(def/defa (remov x xs [n -1]) ;@
  (if [< n 0]
    (if [nilp x]
      (remov-nil xs)      
      (remov-n x xs n) ;(remov-all x xs)
    )
    (remov-n x xs n)
) )

(defn remov-nth% (xs . nths)
  (def (_ xs nths n)
    (if (nilp xs) nil
      (if (nilp nths) xs
        (if [eq (car nths) n]
          [_ (cdr xs) (cdr nths) (1+ n)]
          (cons (car xs) [_ (cdr xs) nths (1+ n)])
  ) ) ) )
  (_ xs [sort < (filter >0 nths)] 1) ;
)
(defn remov-nth (xs . nths)
  (def (_ xs nths n)
    (if (nilp xs) nil
      (if (nilp nths) xs
        (if [eq (car nths) n]
          [_ (cdr xs) (cdr nths) (1+ n)]
          (cons (car xs) [_ (cdr xs) nths (1+ n)])
  ) ) ) )
  ;(_ xs [sort < (filter >0 nths)] 1) ;
  (_ xs nths 1) ;
)


(defn remov-same (xs)
  (def (_ xs ts)
    (if (nilp xs) ts
      (let ([a (car xs)])
        (if (mem? a ts) ;
          [_ (cdr xs) ts]
          [_ (cdr xs) (cons a ts)] ;
  ) ) ) )
  (rev [_ xs nil]) ;
)