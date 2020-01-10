

;

(def (display* . xs)
  (def (_ xs)
    (if (nilp xs) *v
      (bgn
        (display (car xs))
        [_ (cdr xs)]
  ) ) )
  ;(if *will-disp* 
    (_ xs)
) ;)
(ali disp display*)

;

(def (return x) (if *will-ret* x 'done)) ;

;


;


(def (nstrs s n)
  ;(redu strcat (xn2lis s n))
  [list->string (nlist% (string->list s) n)]
)


(def bool (compose not not)) ;nil? 0? ;does it conflit with bool type in ffi ?

(def (bool->string b) (?: (fal? b) "#f" "#t"))



(def (call g . xs) (redu g xs)) ;
(def (rcall% g . xs) (redu g (rev xs)))


(def (explode-sym sym) ;[explode 'asd] ~> '[a s d]
  (map string->symbol [str->ss (sym->str sym)])
)

(setq *alphabet* (str->ss "abcdefghijklmnopqrstuvwxyz"))

;

(def (replace-in xs x y)
  (let ([g (eq/eql x)])
    (map
      (lam (a) (if [g a x] y a))
      xs
) ) )


(defn round% (x)
  (let ([f (floor x)])
    (if (>=(- x f)1/2) (1+ f)
      f
) ) )
(def/defa (myround@ fl (nFlt 0)) ;@
  (let ([fac (pow 10 nFlt)])
    (inexact (/ [round% (* fl fac)] fac)) ;
) )


(defn apply/reducing-num (f n)
  (def (_ ret n)
    (if (< n 1) ret
      [_ (f ret n) (1- n)]
  ) )
  (_ nil n)
)

(defn num->lbump-g (n g)
  (def (_ n ret)
    (if* (< n 0) nil
      (= n 0) ret
      [_ (1- n) (g ret n)]
  ) )
  (_ (1- n) (g n))
)
(defn num->rbump-g (n g)
  (def (_ n ret)
    (if* (< n 0) nil
      (= n 0) ret
      [_ (1- n) (g n ret)]
  ) )
  (_ (1- n) (g n))
)

(def num->lbump (rcurry num->lbump-g li))
(def num->rbump (rcurry num->rbump-g li))

(alias num->bump-g num->rbump-g)
(alias num->bump num->rbump)



(def (eq/eql x)
  (if (str/pair/vec? x) eql eq)
)



(defn mem?/g (x xs g) ;
  (def (_ xs)  
    (if (nilp xs) *f
      (if (g (car xs) x) *t ;
        [_ (cdr xs)]
  ) ) )
  (_ xs)
)
(alias mem? member)

(define (load-relatived* file)
  (load (str *script-path* file)) ;
)