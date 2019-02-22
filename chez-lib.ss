; chez-lib.ss v1.06f pub
#|
  if(#f) cond lambda map foldl reduce curry recursion repl foldr Y 
  str any->str 
  code:dsl->raw
  church yc algo AI math eval memo combinations zip eval. match min
  solve24 remov-what https usd/usdt|usdc/usdt pcre
|#

(alias imp   import)
(alias lam   lambda)
(alias fn    lam)
(alias letn  let*)
(alias progn begin)
(alias quo   quote)
(alias els   else)
(alias def-syn  define-syntax)
(alias syn-ruls syntax-rules)
(alias case-lam case-lambda)

(def-syn bgn (syn-ruls ()
    ((_) *v)
    ((_ . xs) (begin . xs))
) )

(def-syn def ;define*
  (syn-ruls()  
    ( [_ x]
      (def x (void)) )
    ( [_ (g . args) body ...]
      (define (g . args) (bgn body ...)) )
    ( [_ x e]
      (define x e) )
    ( [_ g (args ...) body ...] ;
      (define (g args ...) (bgn body ...))
) ) )

(def-syn defm ;define-macro <- define-syntax
  (syn-ruls()
    ( [_ (f . args) body ...]
      (def-syn f (syn-ruls ()      
          ( [_ . args]
            (bgn body ...)
    ) ) ) )
    ( [_ f (args ...) body ...]
      (defm (f args ...) (bgn body ...))
) ) )

;

(def (compose . gs)
  (def (~ ret gs)    
    (cond
      ([null? gs] ret)
      ([= (length gs) 1]
        (~ (lam xs [ret (redu [car gs] xs)] )
          '()
      ) )
      ( (~ (lam (x) [ret ([car gs] x)])
          (cdr gs)
  ) ) ) )
  (~ (lam (x) x) gs)
)

(def (curry g . args)
  (lam xs
    (redu g
      (append args xs)
) ) )
(def (rcurry g . args)
  (lam xs
    (redu g
      (append xs args)
) ) )

(def car.ori car)
(def cdr.ori cdr)
(def (mycar xs)
  (if (atomp xs) *v ;
    (car.ori xs) ;
) )
(def (mycdr xs)
  (if (atomp xs) *v
    (cdr.ori xs)
) )
(def car mycar)
(def cdr mycdr)

(def caar (compose car car))
(def cadr (compose car cdr))
(def cdar (compose cdr car))
(def cddr (compose cdr cdr))

;cddddr

;

(def *f #f)
(def *t #t)
(def *v (void))
(def *e '[(err)])
(def spc " ")
(def nil? null?)
(def first car)
(def rest cdr)

(def nil '())
(def Fal *f)
(def Tru *t)
(def No  *f)
(def Yes *t)
(def eq eq?)
(def equal equal?)
(def eql equal?)
(def == eql)
(def sym?   symbol?)
(def bool?  boolean?)
(def int?   integer?)
(def num?   number?)
(def str?   string?)
(def nilp   null?)
(def lisp   list?)
(def fn?    procedure?)
(def void? (curry eq *v))
(def voidp  void?)
(def atomp  atom?)
(def exa->inexa exact->inexact)
(def inexa->exa inexact->exact)
(def sym->str   symbol->string)
(def ev   eval)
(def reduce apply)
(def redu   reduce)
(def strcat string-append)
(def rev reverse)
(def li  list)
(def len length)
(def foldl fold-left)
(def foldr fold-right)
(def % mod)
(def ceil ceiling)
(def 1st first)
(def 2nd cadr)
(def 3rd caddr)
(def (id x) x)
(def identity id)
(def identities values)
(def disp display)
(def newln newline)
(def cls [lam() (for(42)(echol))])
(def repl new-cafe)
(def fmt format)
(def exec system)
(def q exit)

;

(def-syn defsyn
  (syn-ruls ()            
    ( [_ f (expr body ...)] ;;;one ;must be bef (_ f g), or will make wrong meanings
      (def-syn f
        (syn-ruls ()      
          (expr
            (bgn body ...) ) ) ) ) ;            
    ( [_ f g]
      (def-syn f
        (syn-ruls ()
          ( [_ . args]
            (g . args) ) ) ) )    
    ( [_ f (expr ...) ...]   ;multiple
      (def-syn f
        (syn-ruls ()      
          ( expr
            ...
          )
          ...
) ) ) ) )

(defsyn defun
  ( [_ f args ...]
    (define f (lam args ...))
) )
(alias defn defun)

(defsyn defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( (_ f args body ...)
    (define f
      (eval
        (foldr
          [lam(a b)(append a (list b))]
          `(lam() body ...)
          [map (lam(x)`(lam(,x))) 'args] ;
) ) ) ) )
(defsyn defn-snest ;s for short ;(lam(a)(lam(b) body...))
  ( (_ f args body ...)
    (define f
      (eval
        (foldr
          [lam(a b) (append a (list b))]
          `(bgn body ...)
          (map [lam(x) `(lam (,x) )] 'args) ;
) ) ) ) )

(def-syn def_
  (lam (stx)
    (syntax-case stx()
      ([_ (g . xs) bd ...]
      #`(define (g . xs)
          (let ([#,(datum->syntax #'g '_) g]) ;with-syntax
              bd ...
      ) ) )
      ([_ xs ...]
      #'(define xs ...)
) ) ) )
(defsyn defn_
  ( (_$% f args bd...)
    (def_ (f . args) bd...)
) )

(defsyn setq
  [(_ a) (set! a (void))]
  ((_ a b)
    (bgn (set! a b) (if *setq-wil-ret* a))
  )
  ((_ a b c ...)
    (bgn          
      (set! a b)
      (setq c ...) ;
) ) )

;

(def-syn defa-def ; g x . ys
  (syntax-rules() 
    [(_ (g . args) body ...)
      (define (g . xs)
        (let*(
              [max-ln (if (list? (car 'args)) (length 'args) 100 )] ;?
              [raw-ln (length xs)]
              [ln (min raw-ln max-ln)]
              [need 0] ;num-non-defa
             )
          (def_ (need-how-many ys n)
            (if (null? ys)
              n
              (if (null? (cdar ys)) ;
                (_ (cdr ys) (+ 1 n))
                (_ (cdr ys) n)
          ) ) )
          (if (list? (car 'args)) ;
            (bgn
              (ev `(define (f_ . ,(map car 'args)) (bgn body ...)))              
              (setq need (need-how-many 'args 0)) ;
              (if (>= ln need)
                (redu f_
                  (append xs
                    (map [lam(x)(ev(cadr x))] (ncdr 'args ln)) ;ev
                ) )
                nil ;#f
            ) )
            (bgn
              (ev `(define (f_ . args) (bgn body ...))) ;
              (redu f_ xs) ;
          ) )
    ) ) ]
) )

;common

(def-syn for          ;break?
  (syn-ruls (in : as)   ;syntax-keywords
    ; ((_ i in list body ...)
     ; (map (lambda (i) ;map makes action-sequence mess, could use (for-each do list)
                  ; body ...)
          ; list ))
    ( [_ i in xs body ...]
      (let loop ([l xs])
        (unless (nilp l)
          (let ([i (car l)])
            body ...
            (loop (cdr l)) ))))
    ((_ list as i body ...)
     (map (lambda (i) ;map has ret values
            body ...)
          list))
    ((_ (i : list) body ...)
     (map (lambda (i)
            body ...)
          list))
    
    ( [_ (n) b1 ...] ;;(for ((+ 2 3)) ..) ;i?
      (let loop ([i 0])
        (when (< i n)
          b1 ...
          (loop (1+ i)) )))      
    ( [_ (i n) b1 ...]
      (for (i 0 (1- n)) b1 ...) )
    ( [_ (i from to) b1 ...]
      (for (i from to 1) b1 ...) )
    ( [_ (i from to step) b1 ...]
      (let loop ([i from])
        (cond
          ( (> step 0)
            (when (<= i to)
              b1 ...
              (loop (+ i step))))
          ( (= step 0)
            nil)              
          ( (< step 0)
            (when (>= i to)
              b1 ...
              (loop (+ i step)))) )))
    ;call/cc
    ((_ k (n) b1 ...) ;;(for ((+ 2 3)) ..) ;i?
     (let loop [(i 0)]
      (call/cc (lam(k)
          (when (< i n)
            b1 ...
            (loop (+ 1 i)))
      )        )
    ))
    ((_ k (i from to) b1 ...)
     (let loop [(i from)] ;let when
      (call/cc (lam(k)
          (when (<= i to)
            b1 ...
            (loop (1+ i))
          )
      )        )
    ))
    ((_ k (i from to step) b1 ...)
        (let loop [(i from)]
         (call/cc (lam(k)
             (cond
               ((> step 0)
                 (when (<= i to)
                   b1 ...
                   (loop (+ i step))))
               ((= step 0)
                 nil)              
               ((< step 0)
                 (when (>= i to)
                   b1 ...
                   (loop (+ i step)))))
         )        )
    )   )
))

;

(def *setq-wil-ret* #f)

;

(defsyn set-xth!
  ( [_ xs i y]
    (letn ( (n (1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln)))
            (pos (ncdr xs n)) )
      (set! xs (append pre (cons y pos)))
) ) )
(defsyn set-nth!
  [(_ xs n y) (set-xth! xs (1- n) y)]
)
(defsyn swap-xths!
  ((_ xs i j)
    (let( (t(nth xs i)) )
      (set-xth! xs i (nth xs j))
      (set-xth! xs j t)
  ) )
  ((_ xs i ys j)
    (let( (t(nth xs i)) )
      (set-xth! xs i (nth ys j))
      (set-xth! ys j t)
) ) )
(defsyn swap-nths!
  ((_ xs m n)
    (swap-xths! xs (1- m) (1- n)) )
  ((_ xs m ys n)
    (swap-xths! xs (1- m) ys (1- n)) )
)

(defsyn push ;(_ ys xs) (_ ys xs -1)
  [(_ a ll)
    (let ([ts (cons a ll)])
      (if (sym? 'll) (set! ll ts) )
      ts
) ] )
(defsyn rpush
  [(_ a ll)
    (let ([ts (conz ll a)])
      (if (sym? 'll) (set! ll ts) )
      ts
) ] )
(def-syn pop
  (syn-ruls ()
    ((_ ls)
      (let ([ret (car ls)])
        (if (symbol? `ls)
          (eval
            `(set! ls (cdr ls))
        ) )
        ret
) ) ) )


(defsyn type-main
  ( [_ x]
    (cond
      ;((ffi-s? (any->str 'x))  "ffi") ;?if not sym
      ((sym?  x)      "symbol") ;
      ((bool? x)      "boolean")
      ((num?  x)      "number") ;
      ((char? x)      "char") ;
      ((str?  x)      "string") ;      
      ((nil?  x)      "null")
      ((list?  x)     "list") 
      ((pair? x)      "pair")
      ;((ffi?  x)      "ffi2") ;
      ((fn?   x)      "fn") ;procedure
      ((vector? x)    "vector") ;
      ((void? x)      "void")
      ((atom? x)      "other-atom") ;(eof-object) ;x (void)
      (else           "other")  ;other-atoms      
) ) )
(alias ty type-main)

;

(defn nlist (xs n)
  (defn _(xs n rest)
    (if (<= n 0)
      rest
      (_ xs (1- n) (append rest xs))
  ) )
  (_ xs n '())
)
(def nli nlist)

;ex

(def ncdr
  (case-lam
    ( [ll s]
      (if (< s 0)
        (let ([res (rev ll)])
          (for ((- -1 s)) [setq res (cdr res)])
          (rev res) )
        (let ([res ll]);
          (for (s) [setq res (cdr res)]) ;
          res
    ) ) )
) )
    
(def (call . xs)
    (apply (car xs) (cdr xs))
)

(defn member? (x xs)
  (cond
    ( (nil? xs) *f)
      (else
        (or (eq? x (car xs))
          (member? x (cdr xs))
) ) ) )

(def (disp2 x y)
  (disp x)
  (disp y)
)
(def (echo% sep . xs)
  (case (len xs)
    (0 *v)
    (1 (disp(car xs)))
    (else
      (disp2 (car xs) sep)
      (redu echo% (cons sep (cdr xs)))
) ) )
(def (echo . xs) (redu echo% (cons " " xs)))

(def mk-range%
  (lam (s e p)
    (let _ ((cnt e) (res nil))
      (if ((if(> p 0)> <) s cnt)
        res
        (_ (- cnt p) (cons cnt res))
) ) ) )
(def range
  (case-lambda
    ((a)     (mk-range% 0 (1- a) 1))
    ((a b)   (mk-range% a b 1))
    ((a b c) (mk-range% a b c))
) )

(defa-def (range* [n\s][e](f +)(p 1)) ;'+
  (defn _ (n\s e f p res)
    (cond
      ((nilp e) (_ 0 (- n\s 1) f p res))
      (else
        (let([m (f n\s p)])
          (if ([if(> m n\s)< >] e n\s) ;
            res
            (_ m e f p (rpush n\s res)) ;
  ) ) ) ) )  
  (_ n\s e f p '()) ;
)

(def echol
  (lam xs
    (redu echo xs)(newln)
) )

(defn readexpr xs ;
  (let
    ( [p(open-input-string
          (redu strcat
            `("(begin " ,@xs ")")
    ) ) ] ) ;ign spc between
    (read p)
) )
(def readexp readexpr)
(def (evs . xs) [ev (redu readexp xs)]) ;

;cl 

(defsyn getf
  ((_ xs xtag)
    (if (<(len xs)2) nil
      (if (eq (1st xs) 'xtag)
        (2nd xs)
        (ev`(getf (cddr xs) xtag)) ;
) ) ) )

(defsyn getf-xth-iter
  ((_ x f1 i)
    (if (<(len x)2) nil ;
      (if (eq (1st x) 'f1)
        (1+ i)
        (ev`(getf-xth-iter (cddr x) f1 (+ 2 i)))
) ) ) )
(defsyn getf-xth
  ((_ x f1)
    (getf-xth-iter x f1 0)
) )
(defsyn setf* ;(_ mapA tagX a)
  ((_ x f1 a)
    (letn [ (i (getf-xth x f1)) ]
      (if (nilp i) (if *setq-wil-ret* x nil)
        (set-xth! x i a)
) ) ) )

(defn_ getf* (xs xtag) ;`(:n ,n :x ,x)
  (if (<(len xs)2) nil
    (if (eq (1st xs) xtag)
      (2nd xs)
      (_ (cddr xs) xtag)
) ) )

(def_ (get-as-arr xs . iz)
  (if (nilp iz)
    xs
    (if (lisp xs) ;
      (redu [curry _ (nth xs (car iz))]
            (cdr iz) )
      nil
) ) )
(def aref get-as-arr)

;oth
(def op-inp-str open-input-string)

(defn char->string(x) (list->string(li x)))
(def (str-explode s) (map char->string(string->list s)))

; (defa-def (str->ss [str][i nil]) ;x str-explode-by
  ; (letn([i (if(nilp i) (open-input-string str) i)]
        ; [s (sym->str(read i))])
    ; (if (eof-object? s) nil
      ; (cons s (str->ss "" i))
; ) ) )

(defn conz (xs y)
  (append xs (li y))
)
(def conj conz)
;

;C

(defn ?: (a b c) (or (and a b) c))

(def-syn +=
  (syntax-rules()
    ((_ x . xs)
      (bgn
        (set! x (+ x . xs))
        x
) ) ) )
(def-syn -=
  (syntax-rules()
    ((_ x . xs)
      (bgn
        (set! x (- x (+ . xs)))
        x
) ) ) )

(def (xth xs ix) ;<len< nil ;mvto: nth line
  (let()
    (if(eql 0 ix)
      (car xs)
      (xth (cdr xs) (1- ix))
) ) )
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

(defn nth (xs n) (xth xs (1- n)))

(defun flat (x)
  (defun rec (x ret)
    (cond
      ((nilp  x) ret)
      ((atomp x) (cons x ret))
      ( (rec (car x)
          (rec (cdr x) ret)
  ) ) ) )
  (rec x nil)
)

(def (redu-map r m xs) (redu r (map m xs))) ;syn for such-as or

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

(def_ (stru-cmp xs ys)
  (if (nilp xs) '=
    (if (atomp xs)
      (atom-cmp xs ys)
      (letn ([x(car xs)] [y(car ys)])
        (if (atomp x)
          (if (ty-neq x y) nil
            (let ([resl (atom-cmp x y)])
              (case resl
                (= [_ (cdr xs) (cdr ys)])
                (else resl)
          ) ) )
          (let ([resl (_ x y)])
            (case resl
              (= [_ (cdr xs) (cdr ys)])
              (else resl)
) ) ) ) ) ) )
(defn stru>(x y) (mk<>= stru-cmp (li x y) '>))
(defn stru<(x y) (mk<>= stru-cmp (li x y) '<))

(def (assert resl test)
  (echol
    (if (tru?(eql resl test)) *t
      "Wrong!!"
) ) )

;math

(def =0? (curry = 0))
(def =1? (curry = 1))
(def >0 (curry < 0))
(def <0 (curry > 0))
(def >1 (curry < 1))
(def <1 (curry > 1))
(def >=0 (curry <= 0))
(def <=0 (curry >= 0))
(def >=1 (curry <= 1))
(def <=1 (curry >= 1))

(def =0 =0?)
(def =1 =1?)
(def not= (compose not =))
(def != not=)

(defn len0?(x) (=(len x)0))
(def len0 len0?)
(def len>0 (compose >0 len))
(def len<0 (compose <0 len))
(def len>=0 (compose >=0 len))
(def len<=0 (compose <=0 len))
(def len1 (compose =1 len))
(def len>1 (compose >1 len))
(def len<1 (compose <1 len))
(def len>=1 (compose >=1 len))
(def len<=1 (compose <=1 len))

(def (avg . xs) (/ (redu + xs) (len xs)))

(def (pow . xs)
  (if(>(len xs)1)
    (fold-left expt (car xs) (cdr xs))
    (expt (car xs) 2) ;
) )

;todo: calc th min length of a line of multiple points
;todo: calc th length of th line of multiple points
(defa-def (distance (p1) (p2 ())) ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1
  (let* ( [l1 (len p1)]
          [p2 (if(nilp p2) (nlist '(0) l1) p2)]
        )
    (if [= (len p1)(len p2)]
      (sqrt
        [apply + (map [lam(y x) (pow(- y x))] p2 p1)] )
      nil
) ) )

(defn min-prime-factor (n) ;factorize prime-num?
  (defn _ (n tmp max.)
    (if (<= tmp max.)
      (if (!= (% n tmp) 0)
        (_ n (+ 2 tmp) max.)
        tmp
      )
      nil ;
  ) )
  (letn ([max. (pow n 1/2)])
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

(def prime-num? (compose nilp min-factor))
(def (prime s i)
  (defn ~ (s i ret)
    (if (<= i 0) ret
      (if (prime-num? s)
        (~ (+ 2 s) (1- i) s)
        (~ (+ 2 s) i ret)
  ) ) )
  (let( [b (even? s)]
        [b2 (<= s 2)] ) ;
    (~
      (if b (1+ s)
        (if b2 3 s) )
      (- i (if b2  1 0))
      2 ;nil
) ) )
(def primes
  (case-lam
    ([s n]
      (defn ~ (s n ret)
        (if (<= n 0) ret
          (if (prime-num? s) ;
            (~ (+ 2 s) (1- n) (cons s ret))
            (~ (+ 2 s) n ret)
      ) ) )
      (let( [b2  (<= s 2)]
            [b (even? s)] )
        (~        
          (if b (1+ s)
            (if b2 3 s) )
          (- n (if b2  1 0))
          (if b2 '(2) '())
) ) ) ) )

(def len-1 (compose 1- len))
(def (find-ref xs x st ed)
  (let([ed (if(nilp ed)(len-1 xs)ed)])
    (def (_ xs x i)
      (if(eql x (car xs))
        i
        (if(>= i ed)
          nil
          (_ (cdr xs) x (1+ i))
    ) ) )
    (_ xs x st)
) )
(def_ (remov-n x xs n )
  (if(<= n 0) xs
    (let*[(i (find-ref xs x 0 nil))]
      (if(nilp i) xs
        (let*[(n2 (1+ i))
              (m (1- i))
              (ln (len xs))
              (pre (ncdr xs (- m ln)))
              (pos (ncdr xs n2))]
          (append pre (_ x pos (1- n)))
) ) ) ) )
(defa-def (remov (x)(xs)(n 1))
  (remov-n x xs n)
)

(defn permutation (xs)
  (defn _ (xs ys r)
    (if (nil? xs) r
      (let*[(a (car xs))
            (d (cdr xs))
            (ts (remov a ys)) ;
            (zss(permutation ts))
           ]
        (if (nil? zss) (li(li a)) ;
          (_ d ys (append r [map(curry cons a)zss]))
  ) ) ) )
  (_ xs xs nil)
)

(def_ (combinations items k)
  (cond
    ((<= (len items) k) (list items))
    ((= k 1) (map list items))
    (else
      (append
        (_ (rest items) k)
        (map (curry cons (first items))
             (_ (rest items) (1- k)) ;
) ) ) ) )

(def +.ori +)
(def (my+ . xs)
  (def (~ ret . xs)
    (if (nilp xs) ret
      (letn ( [a (car xs)]
              [x (if(num? a)a 0)] )
        (foldl ~
          (+.ori ret x)
          (cdr xs)
  ) ) ) )
  (foldl ~ 0 xs)
)
;(def + my+) ;10x slower than bef

(def (fib0 n)
  (if (<= n 2) 1
    (+ (fib0(- n 1)) (fib0(- n 2)))
) )
(def (fib n)
  (def (~ ret nex n) ;fib-tail 5 1/2 2/3
    (if (<= n 0) ret
      (~ nex (+ ret nex) (1- n))
  ) )
  (~ 0 1 n)
)

(def_ (fac-tail n x) (if (> n 1) ;tail is with an ex-storage
   (_ (1- n) (* n x))        ;commutative law of multiplication
   x
)  )
(def (fac n) (fac-tail n 1))

(defn my-round xs
  (let* ( (flt.   (nth xs 0))
          (numFlt (nth xs 1))
          (numFlt (if(voidp numFlt) 0 numFlt))
          (lv (pow 10 numFlt))
        )
    (/ (round (* flt. lv)) lv)
) )

;matrix:
;'(1 2 3 4 5 6) --m*3->
;a mat: '((1 2 3)(4 5 6))
;((mat m 3) 1 2 3 4 5 6)
;(_ numForOneRow aFlattenList): (_ 3 (range 6)) -> '((0 1 2)(3 4 5))
; (defn_ lis2mat (lst per)
  ; (if (<= (len lst) per)
    ; (li lst)
    ; (cons (carn per lst) (_ (cdrn per lst) per));;
; ) )
(defn_ mat2lis (mat) ;matrix->list: matrix1
  (flat mat)
)
;?matlen submat
(def (dotmul da db) ;(1,2,3)*(4,5,6) ;dot-multiply: point1 point2
  (redu + (map * da db)) ;
)
(defn_ convolution1 (m1 m2) ;convolution: matrix1 matrix2
  (redu dotmul (map mat2lis (li m1 m2)))
)

;middle-function
(def_ (mat-1Muln m1 mn) ;'(1 2 3) '((4 7)(5 8)(6 9))
  (if (nilp(car mn)) nil
    (cons (dotmul m1 (map car mn)) (_ m1 (map cdr mn)))
) )

(def_ (mat-nMuln ma mb) ;mul-2-matrixes
  (if (nilp ma) nil
    (cons (mat-1Muln (car ma) mb) (_ (cdr ma) mb))
) )

(def_ (mat-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-nMuln (car mts) (cdr mts))
)

(defn sigmoid (x)
  (/ 1 (+ 1 [exp(- x)]))
)

;码
(setq
  mm/m  1000
  m/inch  0.0254
  mm/inch (* mm/m m/inch) ;25.4
)

(defn diagonal-length(x y) [sqrt(redu-map + pow (li x y))])
(def diagonalength diagonal-length)

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

;AI: math-e

; (defn sigmoid(x) (/ 1 (1+ (pow math-e (- x))))) ;s-shape-it: make +/-/0 -> probability
; (def  ReLU (curry max 0))

;theory

(def (mk-cps g)
  (lam args
    (let ([r (rev args)])
      ( (car r)
        (redu g
          (rev (cdr r))
) ) ) ) )

;;church-number: https://www.zhihu.com/question/39930042 https://www.jianshu.com/p/73f80c379860

(defn nex-prime (p)
  (prime p 2)
)
(def (inc x) (1+ x)) ;for church's f

;(def (zero f) (lam(x) x))
;(def (one f) (lam(x) (f x))) ;((one inc) 0)
; (def (add1 nf)
  ; (lam(f) (lam(x) [f ((nf f) x)] )) )
(defn-snest chur0 (f x)   x)
(defn-snest chur1 (f x)   (f x))
(defn-snest chur2 (f x)   ((compose f f) x))
(defn-snest chur3 (f x)   ((compose f f f) x))

;todo: chur-*%/n/<=/or
(defn-snest chur+ (m n f x) ;lam-nest
  [(m f) ((n f)x)]
)
(defn-snest chur* (m n f)
  (m (n f)) 
)
(defn-snest chur+1 (nf f x) (f ((nf f) x)))

;λn w z. ((n λl h. h (l w)) (λd.z)) (λx.x)
(def chur-pred ;?
  (lam(n w z)
    ( ( (n
          (lam(l h)
            (h (l w))
        ) )
        (lam (d) z) ;
      )
      id
) ) )

(defn-snest chur-t (t f) t)
(defn-snest chur-f (a b) b)
(defn-snest chur-and (a b) ((a b) chur-f))
(defn-snest chur-or (a b) ((a chur-t) b))
(defn-snest chur-not (a) ((a chur-f) chur-t))
(defn-snest chur-xor (a b) ((a (chur-not b)) b))

; pair = \a.\b.\c.c a b
; first = \p.p true
; second = \p.p false
(defn-snest chur-pair (a b c) ((c a)b)) ;
(defn-snest chur-1st (p) (p chur-t))
(defn-snest chur-2nd (p) (p chur-f))
;let empty = pair false false
(defn-snest chur-nil () ((chur-pair chur-f) chur-f))
;list = \a.\b.pair true (pair a b) in
(defn-snest chur-li (a b) ((chur-pair chur-t) ((chur-pair a)b)))

; (def (chur-fib0 n) ;30=*23(+23) ;(((~ ((chur* [(chur* two)three]) [(chur+ two)three])) f) x)
  ; (if ((chur<= n) two) one
    ; ((chur+ [chur-fib0(chur-1 n)]) [chur-fib0((chur- n)2)])
; ) )

(def (Yc yF%)
  ( (lam (f)
      [f f] )
    (lam (g)
      [yF%
        (lam (x)
          ( [g g] x
) ) ] ) ) )
(def y-getln (lam (~)
    (lam (xs)
      (if (nilp xs) 0
        (1+ (~ (cdr xs)))
) ) ) )

;algo

(def (most-match g? xs) ;_-left
  (def (~ ret xs)
    (if (nilp xs) ret
      (let([a (car xs)])
        (~(if (g? a ret) a ret)
          (cdr xs)
  ) ) ) )
  (~ (car xs) (cdr xs))
)

(def (qsort xs f) (sort f xs))

(def_ (mysort lst cmp) ;much slower than sort ;sort lists
  (cond
    ((nilp lst) '())
    (else
      (let*([a (car lst)]
            [d (cdr lst)]
            [pre (filter (lam(x) (cmp x a)) d)]
            [pos (filter (lam(x) (not (cmp x a))) d)])
        (append (_ pre cmp)
          (cons a (_ pos cmp))
) ) ) ) ) ;-> tail format

; (defn sort2 (xs g?)
  ; (defn ~ (xs ret)
    ; (if (nilp xs) ret
      ; (letn([a (car xs)]
            ; [d (cdr xs)]
            ; [pre (filter [lam(x)(g? x a)] d)]
            ; [pos (filter [lam(x)(not(g? x a))] d)])
        ; (~ pos (~ pre ret))
  ; ) ) )    
  ; (~ xs nil)
; )

;exercise

(defn_ exist-cond? (g x xs) 
  (if (nilp xs) *f ;<-nil
    (let ([a (car xs)])
      (if (g x a) *t
        (_ g x (cdr xs))
) ) ) )
(defn_ exist-relate? (g xs)
  (if (nilp xs) *f
    (let ([b (exist-cond? g (car xs) (cdr xs))])
      (if b *t
        (_ g (cdr xs))
) ) ) )

;(alias defnest defn-nest)

;!!
;(_ gnest nvars data resl)
(defn exist-match? (g cnt  xs) ;nested-g cnt-of-vars testing-data
  (defn _ (g cnt  xs i  ret)    
    (if (>= i (len xs))
      *f
      (if (<= cnt 0)
        (if (g) ret *f)
        (letn ( [x (xth xs i)]
                [b (_ (g x) (1- cnt) xs 0 ret)] ) ;inner
          (if b
            (cons x b)
            (_ g cnt xs (1+ i) ret) ;outer
  ) ) ) ) )  
  (_ g cnt  xs 0  nil)
)

;ffi

(defsyn defc
  ( [_ ret f args]
    (def f (foreign-procedure (sym->str 'f) args ret)) ;outer-proc
) )

(load-shared-object "kernel32.dll")
(defc string GetCommandLineA () )

(load-shared-object "msvcrt.dll")
(defc void* clock ())

;
;(def (main-args) (str-split (GetCommandLineA) spc))

(def CLOCKS_PER_SEC 1000)
(def (clock*)
  (inexact (/ (clock) CLOCKS_PER_SEC))
)

(defsyn cost
  ( [_ g]
    (let ([t 0] [res nil])
      (echo ":" 'g)(newln)
      (setq t (clock*))      
      (setq res g)
      (setq t (-(clock*)t))
      (echo ":elapse= " t "s")(newln)
      (list res t)
) ) )
(defsyn elapse ;just elapse but result
  ((_ g)
    (let[(t 0)(res nil)]
      (echo ":" 'g)(newln)
      (setq t (clock*))      
      (setq res g)
      (setq t (-(clock*)t))
      (echo ":elapse= " t "s")(newln)
      t
) ) )

(defn mem?* (x xs)
  (if(nilp xs) *f
    (if (eql x (car xs))
      *t
      (mem?* x (cdr xs))
) ) )

(defn remov-same (xs)
  (defn _ (ws xs)
    (if(nilp xs) ws
      (let[(a (car xs))]
        (if (mem?* a ws)
          (_ ws (cdr xs))
          (_ (conz ws a) (cdr xs))
  ) ) ) )
  (_ nil xs)
)

; ;yin's code
; (define cps
  ; (lambda (exp)
    ; (letrec
        ; ([trivial? (lambda (x) (memq x '(zero? add1 sub1)))]
         ; [id (lambda (v) v)]
         ; [ctx0 (lambda (v) `(k ,v))]      ; tail context
         ; [fv (let ([n -1])
               ; (lambda ()
                 ; (set! n (+ 1 n))
                 ; (string->symbol (string-append "v" (number->string n)))))]
         ; [cps1
          ; (lambda (exp ctx)
            ; (pmatch exp ;
              ; [,x (guard (not (pair? x))) (ctx x)]
              ; [(if ,test ,conseq ,alt)
               ; (cps1 test
                     ; (lambda (t)
                       ; (cond
                        ; [(memq ctx (list ctx0 id))
                         ; `(if ,t ,(cps1 conseq ctx) ,(cps1 alt ctx))]
                        ; [else
                         ; (let ([u (fv)])
                           ; `(let ([k (lambda (,u) ,(ctx u))])
                              ; (if ,t ,(cps1 conseq ctx0) ,(cps1 alt ctx0))))])))]
              ; [(lambda (,x) ,body)
               ; (ctx `(lambda (,x k) ,(cps1 body ctx0)))]
              ; [(,op ,a ,b)
               ; (cps1 a (lambda (v1)
                         ; (cps1 b (lambda (v2)
                                   ; (ctx `(,op ,v1 ,v2))))))]
              ; [(,rator ,rand)
               ; (cps1 rator
                     ; (lambda (r)
                       ; (cps1 rand
                             ; (lambda (d)
                               ; (cond
                                ; [(trivial? r) (ctx `(,r ,d))]
                                ; [(eq? ctx ctx0) `(,r ,d k)]  ; tail call
                                ; [else
                                 ; (let ([u (fv)])
                                   ; `(,r ,d (lambda (,u) ,(ctx u))))])))))]))])
      ; (cps1 exp id))))

      
(def (restore)  
  (setq
    car car.ori
    cdr cdr.ori
    ;+   +.ori ;?
) )
(def (clean) (restore))
(def (reload-it)
  (clean)
  ;(load (symbol->string 'g:/tool/chez-lib.ss))
  (load (symbol->string 'g:/tool/mylib/chez-lib.ss))
   ;当在foo.scm文件中出现load-relative(MzScm)调用时，它的参数的路径将根据文件foo.scm所在目录的路径来计算
  ;(load-relative (symbol->string 'chez-lib.ss)) ;getcmdline read
)
(def refr reload-it)



;
#||#