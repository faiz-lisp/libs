
(ali permu permutation)

;---

(def (most g xz) ;(most (lam(l r)(?(> l r)l r)) '(1 2 3))
  (def (_ xs yz)
    (cond [(nilp yz) xs] ;faiz chk last time
      [else
        (_ [g xs (car yz)] (cdr yz)) ]
  ) )
  (_ (car xz) (cdr xz))
)

(defn longest xz ;(longest '(1 2) '() '(2 3)) ~> '(2 3)?
  (most
    [lam (l r)
      (? [len-cmp > l r] l r) ]
    xz
) )

(defn r-merge (xs ys) ;%
  (let ([m (len xs)] [n (len ys)])
    (if [>= m n] (ncdr xs [- n m])
      (append xs (ncdr ys m))
) ) )

(def l-merge (swap-para r-merge))

(defn tru? (b)
  (if (eq *t b) *t *f)
)

(defn fal? (b)
  (if (eq *f b) *t *f)
)

(defn neq (x y) (not(eq x y)) )

(defn !eql(x y) (not(eql x y)) )

(defn tyeq (x y)
  (eq(ty x)(ty y))
)

(defn ty-neq (x y)
  (neq(ty x)(ty y))
)

(def (sym< x y) (redu-map string<? sym->str(li x y)) )
(def (sym> x y) (redu-map string>? sym->str(li x y)) )

(defn atom-cmp (x y)
  (letn ( [type (ty x)]
          [<>
            (case type
              ("string" (li string<? string>?))
              ("char"   (li char<? char>?))
              ("symbol" [li sym< sym>])
              ("number" (li < >))
              ;vector
              (else nil)
        ) ] )
    (if (eq type (ty y))
      (if (nilp <>)
        (if (eql x y) = nil) ;
        (cond
          ([(car <>) x y] '<)
          ([(cadr <>) x y] '>)
          (else '=)
      ) )
      nil ;
) ) )

(defn mk<>= (f xs cmp)
  (let ([resl(redu f xs)])
    (if (nilp resl) nil
      (eq resl cmp)
) ) )

(defn atom>(x y) (mk<>= atom-cmp (li x y) '>))
(defn atom<(x y) (mk<>= atom-cmp (li x y) '<))

(def (stru-cmp xs ys)
  (def (_ xs ys)
    (if (nilp xs) '= ;
      (if (atomp xs) ;? < atom nil pair list
        (atom-cmp xs ys)
        (letn ([x(car xs)] [y(car ys)])
          (if (atomp x)
            (if (ty-neq x y) nil
              (let ([resl (atom-cmp x y)])
                (case resl
                  (= [_ (cdr xs) (cdr ys)])
                  (else resl)
            ) ) )
            (let ([resl [_ x y]])
              (case resl
                (= [_ (cdr xs) (cdr ys)])
                (else resl)
  ) ) ) ) ) ) )
  (_ xs ys)
)

(defn stru>(x y) (mk<>= stru-cmp (li x y) '>))
(defn stru<(x y) (mk<>= stru-cmp (li x y) '<))

(def (find-ref xs x st ed)
  (let ([ed (if(nilp ed)(len-1 xs)ed)][= (eq/eql x)])
    (def (_ xs x i)
      (if [= x (car xs)] ;
        i
        (if [>= i ed]
          nil
          (_ (cdr xs) x (1+ i))
    ) ) )
    (_ xs x st)
) )

(defn permutation (xs) ;(_ n xs-range n0) ;how ab repeating cases?
  (def (_ r xs ys)
    (if (nilp xs) r
      (letn[(a (car xs))
            (d (cdr xs))
            (ts (remov-1 a ys)) ;
            (zss(permutation ts))
           ]
        (if (nilp zss) `((,a)) ;
          (_ (append~ r [map(curry~ cons a)zss]) d ys)
  ) ) ) )
  (_ nil xs xs)
)

(def_ (combinations items k)
  (cond
    ((= k 0) (list '())) ;
    ((= k 1) (map list items))
    ((>= k (len items)) (list items))
    (else
      (append~ ;
        [_ (rest items) k]
        (map (curry~ cons (car items)) ;
             [_ (rest items) (1- k)]
) ) ) ) )

(def (permu-n xs n)
  (redu~ append~
    (map permu (combinations xs n))
) )

(def_ (subsets xs) ;_ '(1 2) ~> '(() (1)(2)(3) (1 2)(2 3)(1 3))
  (if (nilp xs) (list nil)
    (let ([rest [_ (cdr xs)]])
      (append rest
        (map [curry cons (car xs)] rest)
) ) ) )

;algo

(def (filter% g xs)
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)][d (cdr xs)])
        (if (g a)
          (cons a [_ d]) ;cons mk _ slower than filter
          [_ d]
  ) ) ) )
  (_ xs)
)
(defn filter2 (g xs) ;~> '(tagets rests)
  (def (_ xs ll rr) ; ll rr
    (if (nilp xs)
      (li ll rr) ;pair
      (let ([a (car xs)][d (cdr xs)])
        (if (g a)
          [_ d (cons a ll) rr]
          [_ d ll (cons a rr)] ;
  ) ) ) )
  (_ xs nil nil)
)

(def (most-match g? xs) ;_-left
  (def (~ ret xs)
    (if (nilp xs) ret
      (let ([a (car xs)])
        (~(if (g? a ret) a ret)
          (cdr xs)
  ) ) ) )
  (~ (car xs) (cdr xs))
)

(def (maxs . ns)
  (def (_ x m ns)
    (if (nilp ns) (li x m) ;
      (let ([a (car ns)] [d (cdr ns)])
        (cond
          [(> a x) [_ a 1 d]]
          [(< a x) [_ x m d]]
          [else    [_ x (1+ m) d]]
  ) ) ) )
  (if (nilp ns) nil
    (_ (car ns) 1 (cdr ns))
) )

(defn_ exist-cond? (g x xs)
  (if (nilp xs) *f ;<-nil
    (let ([a (car xs)])
      (if (g x a) *t
        [_ g x (cdr xs)]
) ) ) )

(defn_ exist-relate? (g xs)
  (if (nilp xs) *f
    (let ([b (exist-cond? g (car xs) (cdr xs))])
      (if b *t
        [_ g (cdr xs)]
) ) ) )

;(alias defnest defn-nest)

;(_ f-test nvars gs xs (repeat? *t) goal)
(defn exist-match? (g cnt  xs) ;nested-g cnt-of-vars testing-data
  (defn ~ (g cnt  xs i  ret)
    (if (>= i (len xs))
      *f
      (if (<= cnt 0)
        (letn ( [tes (try (g))]
                [b   (if (not(cond? tes)) tes *f)] )
          (if b ret *f) ) ;end
        (letn ( [x (xth xs i)]
                [b (~ (g x) (1- cnt)  xs 0  ret)]  ) ;inner
          (if b (cons x b)
            (~ g cnt  xs (1+ i)  ret) ;outer
  ) ) ) ) )
  (~ g cnt  xs 0  nil)
)

;todo: Dijkstra

;--- inner

(def (most% g xs . yz) ;(most (lam(l r)(?(> l r)l r)) 1 2 3)
  (def (_ xs yz)
    (if (nilp yz) xs
      (_ [g xs (car yz)] (cdr yz))        
  ) )
  (_ xs yz)
)
