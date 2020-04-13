
;;church-number: https://www.zhihu.com/question/39930042 https://www.jianshu.com/p/73f80c379860

(defn nex-prime (p)
  (prime p 2) ;
)
(alias inc 1+) ;for church's f, use 1+ is not rooty

;(def (zero f) (lam(x) x))
;(def (one f) (lam(x) (f x))) ;((one inc) 0)
; (def (add1 nf)
  ; (lam(f) (lam(x) [f ((nf f) x)] )) )
(defn-snest chur0 (f x)   x)
(defn-snest chur1 (f x)   (f x))
(defn-snest chur2 (f x)   ((compose f f) x))
(defn-snest chur3 (f x)   ((compose f f f) x))

(def (mk-chur num)
  (lam (f)
    [lam (x) ;lam-snest
      ((redu compose (xn2lis f num)) x)
  ] )
)
; (call-snest chur* (mk-chur 123) (mk-chur 3) inc 0)

;todo: chur-*%/n/<=/or
(defn-snest chur+ (m n f x) ;lam-nest
  [(m f) ((n f)x)]
)
(defn-snest chur* (m n f)
  (m (n f))
)
(defn-snest chur+1 (nf f x) [f ((nf f) x)])

;λn w z. ((n λl h. h (l w)) (λd.z)) (λx.x)
(defn chur-pred [n w z]
  ( ( (n
        (lam [l h]
          (h (l w)) ) )
      (lam [d] z) ) ;
    id
) )

(defn-snest chur-t (t f) t)
(defn-snest chur-f (t f) f)
(defn-snest chur-and (a b) ((a b) chur-f))
(defn-snest chur-or (a b) ((a chur-t) b))
(defn-snest chur-not (a) ((a chur-f) chur-t))
(defn-snest chur-xor (a b) ((a (chur-not b)) b))

; pair = \a.\b.\c.c a b
; first = \p.p true
; second = \p.p false
(defn-snest chur-pair (a b c) [(c a) b]) ;
(defn-snest chur-1st (p) (p chur-t))
(defn-snest chur-2nd (p) (p chur-f))
;let empty = pair false false
(defn-snest chur-nil () ((chur-pair chur-f) chur-f))
;list = \a.\b.pair true (pair a b) in
(defn-snest chur-li (a b) ([chur-pair chur-t] [(chur-pair a)b]))

; (def (chur-fib0 n) ;30=*23(+23) ;(((~ ((chur* [(chur* two)three]) [(chur+ two)three])) f) x)
  ; (if ((chur<= n) two) one
    ; ((chur+ [chur-fib0(chur-1 n)]) [chur-fib0((chur- n)2)])
; ) )