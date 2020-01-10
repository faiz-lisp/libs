
;'((^)(* / %)(+ -))
(defn read-math-expr xs
  (let
    ([p (open-input-string
          (redu~ strcat
            `("'(" ,@xs ")") ) ) ])
    (read p)
) )


;math

(def =0? (curry = 0))
(def =1? (curry = 1))
(def >0  (curry < 0))
(def <0  (curry > 0))
(def >1  (curry < 1))
(def <1  (curry > 1))
(def >=0 (curry <= 0))
(def <=0 (curry >= 0))
(def >=1 (curry <= 1))
(def <=1 (curry >= 1))

(ali =0 =0?)
(ali =1 =1?)
(def not= (compose not =))
(ali != not=)
(def !=0 (compose not =0))


(def 2* (curry * 2))

(def ./ (compose exa->inexa /))
(def .* (compose exa->inexa *))
(def (avg . xs) (/ (redu~ + xs) (len xs)))
(def %
  (case-lam
    [(x) (./ x 100)]
    [(x . ys) (foldl mod x ys)]
) )

(def (pow . xs)
  (if [nilp (cdr xs)]
    (expt (car xs) 2) ;
    (fold-left expt (car xs) (cdr xs))
) )

(setq *max-deviation* (- [expt(sqrt 2)2] 2)) ;?
(setq *max-deviation-ratio* [1-(/ (expt(sqrt 2)2) 2)])
(def (~= a b)
  [<= (abs(1-(/ a b))) *max-deviation-ratio*] ;/
  ; (let ([cal (if(> a b) call rcall%)])
    ; [<= (1-(cal / a b)) *max-accuracy-error-ratio*]
  ; )
)

(defa-def (distance (p1) (p2 [])) ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1
  (let* ( [l1 (len p1)]
          [p2 (if(nilp p2) (nlist% '(0) l1) p2)]
        )
    (if [= (len p1)(len p2)]
      (sqrt
        [apply + (map [lam(y x) (pow(- y x))] p2 p1)] )
      nil
) ) )

(defn min-prime-factor (n) ;factorize prime-num?
  (def (_ n tmp max.)
    (if (<= tmp max.)
      (if (!= (% n tmp) 0)
        (_ n (+ 2 tmp) max.)
        tmp
      )
      nil ;
  ) )
  (let ([max. (pow n 1/2)])
    (if (!= (% n 2) 0)
      (_ n 3 max.) ;n
      (if (= n 2) nil ;
        2
) ) ) )
(def min-factor min-prime-factor)

;(cost(factors 40224510201988069377423))
(defn factors (n)
  (defn _ (n factors.)
    (letn ([factor (min-factor n)])
      (if (nilp factor)
        (cons n factors.)
        (_ (/ n factor) (cons factor factors.))
  ) ) )
  (_ n nil)
)


(def (evenp n)
  (fx= (mod n 2) 0)
)

(def (prim-num? n)
  (if* (< n 2) Fal
    (< n 4) Tru
    (even? n) Fal
    (< n 9) Tru
    (fx= 0 (mod n 3)) Fal
    (let ([r (sqrt n)]) ;floor?
      (let loop ([f 5]) ;22 25 26
        (if (<= f r) ;
          (if*
            [fx= 0 (mod n f)]       Fal
            (fx= 0 [mod n (fx+ f 2)]) Fal
            [loop (fx+ f 6)] )
          Tru ;
      ) )
) ) )

(def (prime s i) ;i
  (def (~ ret s i)
    (if (fx< i 1) ret ;
      (if (prim-num? s)
        (~ s (+ 2 s) (fx1- i)) ;
        (~ ret (+ 2 s) i)
  ) ) )
  (let( [b (even? s)]
        [b2 (< s 3)] ) ;
    (~
      2 ;
      (if b (1+ s)
        (if b2 3 s) )
      (fx- i (if b2 1 0))
) ) )
(def primes
  (lam [s n]
    (def (~ s n ret)
      (if (fx< n 1) ret
        (if (prim-num? s) ;?
          (~ (+ 2 s) (fx1- n) (cons s ret))
          (~ (+ 2 s) n ret)
    ) ) )
    (let( [b2  (< s 3)]
          [b (even? s)] ) ;
      (~
        (if b (1+ s)
          (if b2 3 s) )
        (- n (if b2 1 0))
        (if b2 '(2) '())
) ) ) )

;(cost (prime (1-[redu~ * (primes 2 13)]) 1))
;402245102020351 is the nth? prime-num start from 2 ?

(alias quot quotient)

(def/defa (nbits num [m 10]) ;@ not for float
  (def (_ num n)
    (let ([quo (quot num m)]) ;1 2 4 2 1
      (if [< quo 1] n
        [_ quo (1+ n)]
  ) ) )
  (_ num 1)
)

(def (leap-year? yr)
  (or (=0 [% yr 400])
    (and
      (=0 [% yr 4])
      (!=0[% yr 100])
) ) )

;math end


(def +.ori +) ;
(def (my+ . xs) ;(my+ '(1 2))
  (redu~ +.ori [flat xs]) ;
)
;(dmap [lam(x)(if[nilp x]0 x)] xs)
(def + my+) ;need to be restored bef reload this script


(def (fast-expt-algo x n g x0) ;g need to meet the Commutative Associative Law
  (def (_ n)
    (if*
      (= n 0) x0
      (= n 1) x ;(* x x0) ==> x
      (letn [(m[_ (>> n 1)]) (y[g m m])]
        (if (even? n) y
          [g y x]
  ) ) ) )
  (_ n)
) ; N mod z ?=> a^q*s^w*d^e mod z => ... ; encrypt: 椭圆曲线加密 ; 所有基于群幂的离散对数的加密算法

(def (rep-g g f y0) ;? f for this reason: (- a b c ...) => (rep-g - + 0) => (- a (+ 0 b c ...))
  (lam xs
    (def (once a b)
      (g a
        (fast-expt-algo a (1- b) f y0) ;
    ) )
    (def (_ a b dd)
      (if (nilp dd) (once a b)
        [_ (once a b) [car dd] [cdr dd]]
    ) )
    (_ (car xs) (cadr xs) (cddr xs)) ;
) )

(def (fib1 n) ;gmp: (fib 1E) just 1s
  ;(let ([st(clock)] [1st Fal])
    (def_ (fibo1 ret nex n)
      (if (< n 1) ret
        ; (bgn
          ; (if [=0 (%[- (clock) st]100)]
            ; (when 1st (setq 1st Fal) (echo ".") )
            ; (setq 1st Tru) )
          [_ nex (+ nex ret) (fx1- n)]
    ) ) ;)
    (fibo1 0 1 n)
) ;)

(def (fib n)
  (def (fibo pre pos n)
    (caar
      (mat-mul ;
        (if [>0 n]
          (mat-pow '([ 0  1]
                     [ 1  1]) n)
          (mat-pow '([-1  1]
                     [ 1  0]) (- n)) )
        `([,pre]
          [,pos])
  ) ) )
  (fibo 0 1 n)
)
;(elapse(fib 200000)) ;=> elapse = 0.082 s

(def (fac n) ;how to be faster, such as fast-expt
  (def (_ ret n)
    (if (< n 2) ret
      [_ (* ret n) (1- n)]
  ) )
  [_ 1 n]
)
;(elapse(fac 50000)) ;=> elapse = 1.559 s


(defn math:points->parabola (x1 y1 x2 y2 x3 y3) ;y=ax^2+bx+c
  (letn (
      [b
        (/[-[* (-[pow x2][pow x3]) (- y1 y2)]
            [* (-[pow x1][pow x2]) (- y2 y3)] ]
          [-[* (-[pow x2][pow x3]) (- x1 x2)]
            [* (-[pow x1][pow x2]) (- x2 x3)] ] ) ]
      [a 
        (/[- y1 y2 [* b(- x1 x2)]]
          [- [pow x1] [pow x2]] ) ]
      [c 
        [- y1 [* a [pow x1]] [* b x1]] ]
    )
    (li a b c)
) )
(defn y=ax2+bx+c (a b c x)
  (+ [* a (pow x)] [* b x] c)
)

;码
(setq
  mm/m  1000
  m/inch  0.0254
  mm/inch (* mm/m m/inch) ;25.4
)

(defn diagonal-length(x y) [sqrt(redu-map + pow (li x y))])
(alias diagonalength diagonal-length)

(defn mm->inch (mm) ;inch(/cun)
  ;(* mm 0.0393701) ;英寸Inch
  ;(/ mm 25.4)
  (/ mm mm/inch)
  ;(* mm 0.03)  ;寸?
)
(defn mm->cun (mm)
  (inexact(* mm 1/300))  ;cun
)
(defn inch->mm (inch) (* inch mm/inch))

(defn cm->ma (cm) (- [* 2 cm] 10))