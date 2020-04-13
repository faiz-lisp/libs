
(def map*
  (case-lam
    ([g xs]   (map g xs))
    ([g . xz] (redu~ (curry map g) xz)) ;(_ + '() '(1)) => '(1)
    (else     nil)
) )
(defn conz (xs . ys)
  (if (nilp ys) xs
    (append xs ys) ;! a a -> cycle
) )
;(def conj conz)

(def (compose-n . xs) ;f m g n ...
  (redu compose
    (xn-mk-list% xs)
) )

;





(def (last* xs)
  (if (nilp xs) Err
    (last xs)
) )

(def (last% xs)
  (def (_ xs)
    (if (nilp (cdr xs))
      (car xs)
      [_ (cdr xs)]
  ) )
  (if (nilp xs) Err ;
    (_ xs)
) )



(defn num-of [x db] ;
  (let ([g (eq/eql x)])
    (def (_ db n)
      (if (nilp db) n      
        (_
          (cdr db)
          (if [g (car db) x]
            (1+ n)
            n )
    ) ) )
    (_ db 0)
) )
 
(defn nth-of (x db)
  (let ([g (eq/eql x)])
    (def (_ db n)
      (if (nilp db) Fal
        (if [g (car db) x] n
          (_ (cdr db) (1+ n))
    ) ) )
    (_ db 1)
) )


;(def/defa (assoc-g x ys [g id])
(def (assoc-g x ys g)
  (let ([= (eq/eql x)])
    (def (_ ys)
      (if (nilp ys) nil ;
        (if [= (caar ys) x] 
          (g (car ys))
          [_ (cdr ys)]
    ) ) )
    (_ ys)
) )



(def (list-and xs ys) ;common
  (def (_ xs ys ret)
    (if*
      (nilp ys) ret
      (letn ([y(car ys)] [dy(cdr ys)] [rmp(remov-1?/g y xs eql)]) ;
        (if rmp
          [_ rmp dy (cons y ret)]
          [_ xs dy ret]
  ) ) ) )
  (_ xs ys nil)
)

(def (list-tail xs m) ;*
  (def (_ xs  m)
    (if* (nilp xs) xs
      (<= m 0) xs
      [_ (cdr xs) (1- m)]
  ) ) 
  (_ xs m)
)
(def (list-head xs m) ;%
  (def (_ xs ret m)
    (if* (nilp xs) ret
      (<= m 0) ret
      [_ (cdr xs) (cons[car xs]ret) (1- m)]
  ) ) 
  (rev(_ xs nil m))
)

(def (zip . xz) ;(_ '(1 2) '(2 3) '(3 4 5)) ~> '((1 2 3) (2 3 4))
  (def (_ xz ret)
    (if [nilp(car xz)] ret
      [_ (map cdr xz) (cons (map car xz) ret)]
  ) )
  (if (nilp xz) nil     
    [rev(_ xz nil)]
) )

(defn list/nth (xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li n (car xs))
        [_ (cdr xs) (1+ n)]
  ) ) )
  (_ xs 1)
)
(defn list/-nth (xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li (car xs) n)
        [_ (cdr xs) (1+ n)]
  ) ) )
  (_ xs 1)
)

(def (list- xs ys) ;@
  (def (_ xs ys)
    (if* (nilp xs) nil
      (nilp ys) xs
      [_ (remov-1(car ys)xs) (cdr ys)]
  ) )
  (_ xs ys)
)


(def (xn-mk-list% xns)
  (def (_ x n ys)
    (if [> n 0]
      (cons x [_ x (1- n) ys])
      (if (nilp ys) nil
        (if [nilp(cdr ys)] (li (car ys))
          [_ (car ys) (cadr ys) (cddr ys)]
  ) ) ) )
  (_ nil 0 xns)
)
(def (xn-mk-list . xns) (xn-mk-list% xns))

(defn nx->list (n x) ;a bit faster than make-list
  (defn _ [n rest]
    (cond [(<= n 0) rest]
      [else
        (_ (1- n) [cons x rest]) ] ; cons is fast
  ) )
  (_ n nil)
)
;(def/defa (xn2lis x [n 1]) (nx->list n x))
(def (xn2lis x n) (nx->list n x))

(defn nlist% (xs n) ;xs need append is slow
  (def [_ n ret]
    (if (< n 1) ret
      (_ (1- n) [append xs ret]) ;
  ) )
  (if (nilp xs) nil
    (_ n nil)  
    ; (append% (xn2lis xs n))
) )

;ex

(def (ncdr xs n)
  (if*
    [< n 0]
     (list-head xs (+ (len xs) n)) ;@
    [> n 0]
     (list-tail xs n) ;if outofrange?    
    xs    
) )



;lisp use quo and defsyn, instead of get-addr in c
(defsyn swap
  ( [_ a b]
    (if (eql a b)
      nil
      (let ([t a])
        (setq a b  b t)
    ) )
    (li a b)
) )


(defn flat (xs)
  (def (rec x ret)
    (cond
      [(nilp  x) ret] ;
      [(atomp x) (cons x ret)] ;
      [else
        (rec (car x)
          (rec (cdr x) ret) ) ]
  ) )
  (rec xs nil)
)

(defn flat-and-remov (x xs)
  (let ([g (eq/eql x)])
    (def (_ xs ret)
      (cond
        [(nilp  xs) ret]
        [(g x xs)   ret] ;
        [(atomp xs) (cons xs ret)]
        [else
          (_ (car xs)
            (_ (cdr xs) ret) ) ]
    ) )
    (_ xs nil)
) )
  
(def (redu-map r m xs) (redu r (map m xs))) ;syn for such-as or




(def_ (infix-prefix% lst) ; need a 
  (if (list? lst)
    (if (null? (cdr lst))
      (car lst)
      (list (cadr lst)
            (_ (car lst))
            (_ (cddr lst)) ) )
    lst
) )

(def (list-do xs . fs) ;f g h f g h ...
  (let ([m (len fs)])
    (def (_ xs ret i)
      (if (nilp xs) ret
        [_ (cdr xs)
          (cons [(list-ref fs i)(car xs)] ret)
          (% (1+ i) m) ]
    ) )
    (rev (_ xs nil 0))
) )

(defn dmap (g xs) ;deep-map g . xz
  (def [_ xs]
    (if [nilp xs] nil
      (let ([a (car xs)][d (cdr xs)])
        (if (consp a) ;
          (cons [_ a] [_ d]) ;flat & bump/hunch ;@
          (cons (g a) [_ d])
  ) ) ) )
  [_ xs]
)

(def (lis-copy xs)
  (vec->lis (lis->vec xs))
)