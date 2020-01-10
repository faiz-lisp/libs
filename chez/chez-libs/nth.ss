

(defn chg-nth (xs n . ys)
  [def (_ xs n ys)
    (if (nilp xs) xs
      (cond
        [(< n 1) (_ xs (1+ n) (cdr ys))]
        [(= n 1) (r-merge ys xs)]
        [else
          (cons (car xs) [_ (cdr xs) (1- n) ys])
  ] ) ) ]
  (_ xs n ys)
)

;chg-nths, xs nths, y; .., n; cond case1 case2; init;
(defn chg-nths (xs nths y) ; nths is sorted and uniqueness
  (def (_ xs nths n)
    (if (nilp xs) nil
      (if (nilp nths) xs
        (if [eq (car nths) n]
          (cons y
            [_ (cdr xs) (cdr nths)  (1+ n)] )
          (cons (car xs)
            [_ (cdr xs) nths  (1+ n)] )
  ) ) ) )
  (_ xs nths 1)
)

(defsyn set-xth!% ;chg-nth
  ( [_ xs i y]
    (letn [ (n (1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ]
      (set! xs (append pre (cons y pos)) ) ;
) ) )
(defsyn set-xth! ;chg-nth
  ( [_ xs i y]
    (letn [ (n (1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ]
      (set! xs (append! pre (cons y pos)) ) ;!
) ) )
(defsyn set-nth!
  ([_ xs n y] (set-xth! xs (1- n) y))
)
(defsyn swap-xths!
  ( [_ xs i j]
    (let ([t (nth xs i)])
      (set-xth! xs i (nth xs j))
      (set-xth! xs j t)
  ) )
  ( [_ xs i ys j]
    (let ([t (nth xs i)])
      (set-xth! xs i (nth ys j))
      (set-xth! ys j t)
) ) )
(defsyn swap-nths!
  ( (_ xs m n)
    (swap-xths! xs (1- m) (1- n)) )
  ( (_ xs m ys n)
    (swap-xths! xs (1- m) ys (1- n)) )
)