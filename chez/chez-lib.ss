; chez-lib.ss v1.18 pub

#|
  @ bad
  % theoretic / internal;
  ~ optimized;
  * extensional;
  ! with side-effect
    
  Which ops are slow?:
    append->conz->rpush ... slowest
    ? eval->reduce->compose/curry
    remove
  fast>:
    sort, .., cond if, .., append,
  solution:
    vector

  clean reload? load compile udp/tcp get/post v3 juce ui
  if(! #f/nil)
  cond case, for map lambda foldl reduce curry recursion repl foldr
  lam-snest
  range (range% sum f p n)
  ? (str/sep sep . xs)
    -> echo
    => any->int
  (_ xs . x) (-> -> x)
  code:dsl->raw
  church yc algo
  有些函数实现的层数/维数太高,想破头皮想不透, 估计后面需要搞个降维的函数. for?, cps是搞这块的?
  AI:
    unification
      which book
  math memo combinations, zip eval. match
  solve24 https usd/usdt pcre
  def/setq-glob
  car! (cons 1 2 '()) cons! conz! 
  
  cant/hard: get-addr

  tolearn:
    hygienic assq memq define-structure
    >: [syntax-case see to ;push] defsyn def
    (let ([ret ..]) (ev `(setq x ',ret))
    un/trace

  flow:
    bakup -> .ori
    def myxx xx* xx%
    alias
    restore whn refr
    play
    test
    
  common:
    (_ x y) (_ x . xs) (_ x xs)
|#

(alias imp      import)
(alias lam      lambda)
(alias fn       lam)
(alias letn     let*)
(alias progn    begin)
(alias quo      quote)
(alias els      else)
(alias def-syn  define-syntax)
(alias syn-ruls syntax-rules)
(alias case-lam case-lambda)

(def-syn bgn (syn-ruls ()
    ( (_) *v)
    ( (_ . xs) (begin . xs) )
) )

(def-syn def ;define*
  (syn-ruls ()
    ( [_ x]
      (def x (void) ))
    ( [_ (g . args) body ...]
      (define (g . args) (bgn body ...) ))
    ( [_ x e]
      (define x e))
    ( [_ g (args ...) body ...] ;
      (define (g args ...) (bgn body ...) ))
) )

(def-syn defm ;define-macro <- define-syntax
  (syn-ruls ()
    ( [_ (f . args) body ...]
      (def-syn f (syn-ruls ()
          ( [_ . args]
            (bgn body ...)
    ) ) ) )
    ( [_ f (args ...) body ...]
      (defm (f args ...) (bgn body ...) )
) ) )

;

(def (compose . gs)
  (def (~ ret gs)
    (cond
      ( [null? gs] ret)
      ( [= (length gs) 1]
        (~ (lam xs [ret (redu [car gs] xs)])
          '() ) )
      ( [~ (lam (x) [ret ([car gs] x)]) ;
          (cdr gs) ]
  ) ) )
  (~ (lam (x) x) gs)
)

(def (compose-n g n) ;todo: (_ 1+ 0 *)
  (redu compose (xn2lis g n) )
)

(def map.ori map)
(def map*
  (case-lam
    ([g]      (g))
    ([g xs]   (map.ori g xs))
    ([g . ws] (redu (curry map.ori g) ws)) ;(_ + '() '(1)) => '(1)
    (else     nil)
) )
;(def map map*)

(def (append~ . xz)  
  (redu append (remov-nil xz)) ;remov ;when nil behind, is much faster then system append
)

(def (append% xs . yz)
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        [_ (car yz) (cdr yz)]
        (cons (car xs) [_ (cdr xs) yz]) ;
  ) ) )
  (_ xs (remov-nil yz))
)

(def (curry g . args) ;curry(0~)2
  (lam xs
    (redu g ;
      (append~ args xs)
) ) )

(def (rcurry g . args) ;curry(0~)2
  (lam xs
    (redu g
      (append~ xs args)
) ) )

(def car.ori car)
(def cdr.ori cdr)

(def (car% xs)
  (if (atomp xs) *v ;
    (car.ori xs) ;
) )
(def (cdr% xs)
  (if (atomp xs) *v
    (cdr.ori xs)
) )

;

(def *f #f)
(def *t #t)
(def *v (void) )
(def *e '[(err)] )
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
(def (?: a b c) (or (and a b) c))
(def ? ?:)
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
(def ev     eval)
(def reduce apply)
(def redu   reduce)
(def strcat string-append)
(def rev reverse)
(def li  list)
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
(def repl new-cafe)
(def fmt format)
(def exec system)
(def q exit)
(def str-append string-append)
(def len length)
;(def (len xs) [?(atomp xs) 0 (length xs)])

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

(def-syn (if* stx) ;if* ? ?: if(cond) 
  (syntax-case stx () ;nil?
    ([_ k d]
    #' (if k d) )
    ([_ k d e]
    #'(if k d e) )
    ([_ k d bd ...]
    #'(if k d
        (if* bd ...) )
) ) )

(defsyn defun
  ( [_ f args ...]
    (define f (lam args ...))
) )
(alias defn defun)

(defsyn defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( [_ f args body ...]
    (define f
      (eval
        (foldr
          [lam(a b)(append a (list b))]
          `(lam() body ...)
          [map (lam(x)`(lam(,x))) 'args] ;
) ) ) ) )
(defsyn defn-snest ;(lam(a)(lam(b) body...))
  ( [_ f args body ...]
    (define f
      (eval
        (foldr
          [lam(a b) (append a (list b))]
          `(bgn body ...)
          (map [lam(x) `(lam (,x) )] 'args) ;
) ) ) ) )
;lam-snest (x y z) (+ x y z)
;

(def-syn def_ ;how ab (def_ asd [lam[][_]]) ?
  (lam (stx)
    (syntax-case stx ()
      ([_ (g . xs) bd ...]
      #`(define (g . xs)
          (let ([#,(datum->syntax #'g '_) g]) ;with-syntax
              bd ...
      ) ) )
      ([_ xs ...]
      #'(define xs ...)
) ) ) )
(defsyn defn_
  ( [_$% f args bd...] ;
    (def_ (f . args) bd...)
) )

(def (return x) (if *ret-resl-p* x 'done))

(defsyn setq
  [(_ a) (set! a (void))]
  ((_ a b)
    (bgn (set! a b) (if *ret-resl-p* a))
  )
  ((_ a b c ...)
    (bgn
      (set! a b)
      (setq c ...) ;
) ) )

;

(def-syn defa-def ; g x . ys
  (syn-ruls()
    ( [_ (g . args) body ...]
      (define (g . xs)
        (let*([max-ln (if (list?(car 'args)) (length 'args) 10)] ;?
              [raw-ln (length xs)]
              [ln (min raw-ln max-ln)]
              [need 0] ;numof-NotDefas
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
              (ev `[define (f_ . ,(map car 'args)) (bgn body ...)])
              (setq need (need-how-many 'args 0)) ;
              (if (>= ln need)
                (redu f_
                  (append xs
                    (map [lam (x) (ev(cadr x))] (ncdr 'args ln)) ;ev
                ) )
                nil ;#f
            ) )
            (bgn
              (ev `[define (f_ . args) (bgn body ...)]) ;
              (redu f_ xs) ;
) ) ) ) ) ) )

(defsyn def/defa ;(_ (g a b (c 3) (d 4)) (+ a b c d))
  ( [_ (g . args) body ...]
    [def (_ ret xs)
      (if (nilp xs) ret
        (let ([a (car xs)])
          (if (lisp a)
            (append ret xs)
            [_ (conj ret (li a)) (cdr xs)]
    ) ) ) ]
    (if (lisp (car 'args))
      (ev`(defa-def (g . args) body ...))
      (ev`(defa-def (g . ,(_ nil 'args)) body ...))
) ) )

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
    ( (_ list as i body ...)
      (map (lambda (i) ;map has ret values
            body ... )
          list ))
    ( (_ (i : list) body ...)
      (map (lam (i)
            body ... )
          list ))

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
              (loop (+ i step)) ))
          ( (= step 0)
            nil )
          ( (< step 0)
            (when (>= i to)
              b1 ...
              (loop (+ i step))
    ) ) ) ) )
    ;call/cc
    ( (_ k (n) b1 ...) ;;(for ((+ 2 3)) ..) ;i?
      (let loop [(i 0)]
        (call/cc (lam(k)
          (when (< i n)
            b1 ...
            (loop (+ 1 i)) )
    ) ) ) )
    ( [_ k (i from to) b1 ...]
      (let loop [(i from)] ;let when
        (call/cc (lam (k)
            (when (<= i to)
              b1 ...
              (loop (1+ i))
    ) ) ) ) )
    ( [_ k (i from to step) b1 ...]
      (let loop [(i from)]
        (call/cc (lam (k)
            (cond
              ((> step 0)
                (when (<= i to)
                  b1 ...
                  (loop (+ i step)) ))
              ((= step 0)
                nil)
              ((< step 0)
                (when (>= i to)
                  b1 ...
                  (loop (+ i step))
    ) ) ) ) ) ) )
) )

(def cls [lam() (for(42)(echol))])

;

(def *ret-resl-p* #f)

;

(defn_ last (xs) ;
  (if [nilp (cdr xs)] (car xs)
    (_ (cdr xs))
) )

(defn quiet (x) ;
  (bgn x *v)
)

(defn str-mapcase (mf s)
  (list->string (map mf (string->list s)))
)
(def str-upcase   (curry str-mapcase char-upcase))
(def str-downcase (curry str-mapcase char-downcase))

(defn swap-para (g) ;rev?
  (lam xs
    (redu g (rev xs)) ;
) )

(defn num-of (db x)
  (def (_ db n)
    (if (nilp db) n      
      (_
        (cdr db)
        (if [eql (car db) x]
          (1+ n)
          n )
  ) ) )
  (_ db 0)
)
 
(defn nth-of (db x)
  (def (_ db n)
    (if (nilp db) Fal
      (if (eql (car db) x) n
        (_ (cdr db) (1+ n))
  ) ) )
  (_ db 1)
)

(defn list/nth (xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li n (car xs))
        [_ (cdr xs) (1+ n)]
  ) ) )
  (_ xs 1)
)

(def (len-g f . xs) [redu f (map len xs)])

(def_ (most% g xs . yz) ;(most (lam(l r)(?(> l r)l r)) 1 2 3)
  (def (_ xs yz)
    (if (nilp yz) xs
      (_ [g xs (car yz)] (cdr yz))        
  ) )
  (_ xs yz)
)
(def_ (most g xz) ;(most (lam(l r)(?(> l r)l r)) '(1 2 3))
  (def (_ xs yz)
    (cond [(nilp yz) xs]
      [else
        (_ [g xs (car yz)] (cdr yz)) ]
  ) )
  (_ (car xz) (cdr xz))
)

(defn longest xz
  (most
    [lam (l r)
      (?[len-g > l r] l r) ]
    xz
) )

(defn r-merge (xs ys) ;.
  (let ([m (len xs)] [n (len ys)])
    (if [>= m n] (ncdr xs [- n m])
      (append xs (ncdr ys m))
) ) )
(def l-merge (swap-para r-merge))

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

(defsyn set-xth! ;chg-nth
  ( [_ xs i y]
    (letn ( (n (1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) )
      (set! xs (append pre (cons y pos))) ;
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


(def-syn (pop stx)
  (syntax-case stx ()
    ([_ xs]
      [identifier? #'xs]
      #'[setq xs (cdr xs)] )
    ([_ xs]
      #'(car xs) )
) )
(defsyn rpush
  ([_ a xs]
    (append! xs (li a))
) )
(def-syn (push stx)
  (syntax-case stx () ;
    ([_ a xs]
      [identifier? #'xs] ;
      #'[setq xs (cons a xs)] ) ;
    ([_ a xs]
      #'(cons a xs) )
) )
; (defsyn push ;push!
  ; ([_ a xs]
    ; (let ([ret (cons a xs)]) ;
      ; (if (sym? 'xs) ; (push 1 nil) make nil become '(1) !
        ; (ev `(setq xs ',ret)) ;box?
        ; ret
; ) ) ) )



(defsyn type-main
  ( [_ x]
    (cond
      ;((ffi-s? (any->str 'x))  "ffi") ;x if not sym
      ((sym?  x)      "symbol") ;
      ((bool? x)      "boolean")
      ((num?  x)      "number") ;
      ((char? x)      "char") ;
      ((str?  x)      "string") ;
      ((nil?  x)      "null")
      ((list?  x)     "list")
      ((pair? x)      "pair")
      ;((ffi?  x)      "ffi") ;
      ((fn?   x)      "fn") ;procedure
      ((vector? x)    "vector") ;
      ((void? x)      "void")
      ((atom? x)      "other-atom") ;(eof-object) ;x (void) #err
      (else           "other")  ;other-atoms
) ) )
(alias ty type-main)

(def bool (compose not not)) ;nil? 0? ;does it conflit with bool type in ffi ?

(def (bool->string b) (?:(fal? b) "#f" "#t"))

(def (any->str x)
  (cond
    ((symbol? x) (sym->str            x)) ;
    ((bool?   x)  "") ;               x
    ((number? x) (number->string      x))
    ((char?   x) (list->string (list  x)))
    ((string? x)                      x)
    ((list?   x) (lis->str            x))
    ((pair?   x) (lis->str (pair->list% x)))
    ;((ffi?   x) (sym->str           'x)) ;name?
    ((fn?     x)  "") ;ty?
    ((atom?   x) (sym->str           'x)) ;
    (els          "")
) )
(defn lis->str (xs)
  (redu strcat (map any->str xs))
) ;lis2str

(def (str . xs) (lis->str xs))

(def (pair->list% pr) ;'(1 . ()) ~> '(1 ())
  (li (car pr) (cdr pr))
)

(defn nx->list (n x)
  (defn _ [n rest]
    (cond [(<= n 0) rest]
      [else
        (_ (1- n) [cons x rest]) ] ; cons is fast
  ) )
  (_ n nil)
)
(def (xn2lis x n) (nx->list n x))

(defn nlist@ (xs n) ;xs need append is slow
  (defn _ [xs n rest]
    (if (<= n 0) rest
      (_ xs (1- n) [append rest xs]) ;
  ) )
  (_ xs n nil)
)

;ex

(defn_ ncdr [xs n]
  (cond
    ([= n 0] xs)
    ([< n 0]
      (let ([res (rev xs)])
          (for ((- 0 n)) [setq res (cdr res)]) ;
          (rev res) ) )
    (els
      (_ (cdr xs) (1- n))
) ) )

(def (call . xs)
  (redu (car xs) (cdr xs))
)

(defn member?@ (x xs)
  (cond
    ( (nil? xs) *f)
      (else
        (or (eql x (car xs)) ;
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
    (let _ [(cnt e) (res nil)]
      (if ([if (> p 0) > <] s cnt) ;
        res
        (_ (- cnt p) (cons cnt res))
) ) ) )
(def range
  (case-lambda
    ((a)     (mk-range% 0 (1- a) 1))
    ((a b)   (mk-range% a b 1))
    ((a b c) (mk-range% a b c))
) )

(defa-def (range* (n\s)(e nil) (f +)(p 1))
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

;(range2 sum f p n)

(def echol
  (lam xs
    (redu echo xs)(newln)
) )

(defn read-expr xs ;
  (let
    ( [p(open-input-string
          (redu strcat
            `("(begin " ,@xs ")") ;
    ) ) ] ) ;ign spc between
    (read p)
) )
;'((^)(* / %)(+ -))
(defn read-math-expr xs
  (let
    ([p (open-input-string
          (redu strcat
            `("'(" ,@xs ")") ) ) ])
    (read p)
) )
(def readexp read-expr)
(def (evs . xs) [ev (redu readexp xs)])

(def chars-replace-x (cs x xx)
  (def _ (cs x xx ret)
    (if (nilp cs) ret
      (letn (
          [a (car cs)]
          [b (eq a x)] )
        (_ (cdr cs) x xx ([if b append conz] ret [if b xx a]))
  ) ) )
  (_ cs x xx nil)
)

(def string-replace (s a b) ;
  (list->string (chars-replace-x (string->list s) a (string->list b)))
)

;test
(def (evsx s) ;diy
  (letn (
      [tmp (string-replace s #\[ "(def ")]
      [ss (string-replace tmp #\] ")")] )
    (evs ss)
) )

;'((1 * 2 + 3 * 4) - 5) => 
;(_ '((1 * 2 + 3 * 4) - 5)) => '(((1 * 2) + (3 * 4)) - 5)
;(defn f () nil)

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
      (if (nilp i) (if *ret-resl-p* x nil)
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

(defn str->ss (s) ;(_ "asd") -> '("a" "s" "d")
  (map str (string->list s))
)

(defn conz (xs . ys)
  (if (nilp ys) xs
    (append xs ys) ;! a a -> cycle
) )
(def conj conz)

;C

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
  (if (eql 0 ix)
    (car xs)
    (xth (cdr xs) (1- ix))
) )
(defn nth (xs n) (xth xs (1- n)))

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
  (let ([g (?(str/pair? x) eql eq)])
    (def (_ xs ret)
      (cond
        [(nilp  xs) ret]
        [(g x xs)   ret]
        [(atomp xs) (cons xs ret)]
        [else
          (_ (car xs)
            (_ (cdr xs) ret) ) ]
    ) )
    (_ xs nil)
) )
  
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

(def ./ (compose exa->inexa /))
(def (avg . xs) (/ (redu + xs) (len xs)))

(def (pow . xs)
  (if(>(len xs)1)
    (fold-left expt (car xs) (cdr xs))
    (expt (car xs) 2) ;
) )

(defa-def (distance (p1) (p2 [])) ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1
  (let* ( [l1 (len p1)]
          [p2 (if(nilp p2) (nlist@ '(0) l1) p2)]
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

(def_ (infix-prefix% lst) ; need a 
  (if (list? lst)
    (if (null? (cdr lst))
      (car lst)
      (list (cadr lst)
            (_ (car lst))
            (_ (cddr lst)) ) )
    lst
) )

(def prime-num? (compose nilp min-factor))
(def (prime s i) ;i
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

;402245102020351 is the nth? prime-num start from 2 ?

(def (str/pair? x) [or(str? x)(pair? x)]) ;for eql/eq

(def len-1 (compose 1- len))
(def (find-ref xs x st ed)
  (let ([ed (if(nilp ed)(len-1 xs)ed)][= (?(str/pair? x) eql eq)])
    (def (_ xs x i)
      (if [= x (car xs)] ;
        i
        (if [>= i ed]
          nil
          (_ (cdr xs) x (1+ i))
    ) ) )
    (_ xs x st)
) )

(def (remov~ x xs)
  (let ([g (?(str/pair? x) eql eq)])
    (def (_ xs)
      (if (nilp xs) nil
        (let ([a (car xs)] [d (cdr xs)])
          (if (g a x) ;
            [_ d]
            (cons a [_ d])
      ) ) )
    )
    (_ xs)
) )

(def_ (remov-nil xs)
  ;(remov~ nil xs)
  (if (nilp xs) nil
    (let ([a (car xs)] [d (cdr xs)])
      (if (eq a nil) ;
        [_ d]
        (cons a [_ d])
  ) ) )
)

(def_ (remov-n x xs n)
  (cond
    [(< n 0) (remov~ x xs)] ;
    [(= n 0) xs]
    [else
      (let ([i (find-ref xs x 0 nil)]) ;
        (if (nilp i) xs
          (let*[(n2 (1+ i))
                (m  (1- i))
                (ln (len xs))
                (pre (ncdr xs (- m ln -1))) ;
                (pos (ncdr xs n2))]
            (append~ pre (_ x pos (1- n))) ;
    ) ) ) ]
) )
(defa-def (remov (x)(xs) (n -1)) ;all? -1?
  (remov-n x xs n)
)

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

(defn permutation (xs)
  (defn _ (xs ys r)
    (if (nil? xs) r
      (let*[(a (car xs))
            (d (cdr xs))
            (ts (remov a ys 1)) ;
            (zss(permutation ts))
           ]
        (if (nil? zss) (li(li a)) ;
          (_ d ys (append r [map(curry cons a)zss]))
  ) ) ) )
  (_ xs xs nil)
)

(def_ (combinations items k)
  (cond
    ((= k 0) (list '())) ;
    ((= k 1) (map list items))
    ((>= k (len items)) (list items))
    (else
      (append
        (_ (rest items) k)
        (map (curry cons (car items))
             (_ (rest items) (1- k))
) ) ) ) )

(def_ (subsets xs) ;_ '(1 2) ~> '(() (1)(2)(3) (1 2)(2 3)(1 3))
  (if (nilp xs) (list nil)
    (let ([rest (_ (cdr xs))])
      (append rest
        (map [curry cons (car xs)] rest)
) ) ) )

(defn group (xs n)
  (def [_ xs m ps g]
    (if (nilp xs)
      (li (g ps)) ;
      (let ([a (car xs)][dd (cdr xs)])
        (if (<= m 1) ;
          [_ dd n [g (li a)] id] ;
          ( (?(nilp ps) id (curry cons ps))
            [_ dd (1- m) nil (compose g (curry cons a))]
  ) ) ) ) )
  (cond [(< n 1) nil]
    [(= n 1) (map li xs)]
    [else (_ xs n nil id)]
) )

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
    (+ [fib0(- n 1)] [fib0(- n 2)])
) )
(def (fib n)
  (def (~ ret nex n)
    (if (<= n 0) ret
      [~ nex (+ ret nex) (1- n)]
  ) )
  (~ 0 1 n)
)

(def_ (fac-tail n x) (if (> n 1) ;tail is with an ex-storage
   (_ (1- n) (* n x))        ;commutative law of multiplication
   x
)  ) ;~=7ms
(def (fac n) (fac-tail n 1)) ;(< n 1021L)

(defn round% (x)
  (let ([f (floor x)])
    (if (>=(- x f)1/2) (1+ f)
      f
) ) )

(def/defa (myround@ fl (nFlt 0))
  (let ([fac (pow 10 nFlt)])
    (inexact (/ [round% (* fl fac)] fac)) ;
) )


(defn math:points->parabola (x1 y1 x2 y2 x3 y3)
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
    (cons (dotmul m1 (map car mn)) (_ m1 (map cdr mn))) ;todo
) )

(def_ (mat-nMuln ma mb) ;mul-2-matrixes
  (if (nilp ma) nil
    (cons (mat-1Muln (car ma) mb) (_ (cdr ma) mb))
) )

(def_ (mat-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-nMuln (car mts) (cdr mts))
)

;AI

(def ReLU (curry max 0))
(def relu ReLU)

(defn sigmoid (x)
  (/ (1+ [exp(- x)]))
)
(defn swish (x)
  (* x (sigmoid x))
)

(def/defa (nonlin x (deriv Fal))
  (if (eql deriv Tru)
    (* x [- 1 x])
    (sigmoid x)
) )

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

;theory

(def (mk-cps g)
  (lam args
    (let ([r (rev args)])
      ( (car r)
        (redu g
          (rev (cdr r))
) ) ) ) )

(defn quine (g) `(,g ',g))

; (defsyn lam-snest
  ; ([x] nil)
; )

;;church-number: https://www.zhihu.com/question/39930042 https://www.jianshu.com/p/73f80c379860

(defn nex-prime (p)
  (prime p 2) ;
)
(def inc 1+) ;for church's f, use 1+ is not rooty

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
      (li ll rr)
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

(def float inexact)

(def (qsort xs f) (sort f xs))

(defn mysort@ (xs g)
  (def (~ xs ret)
    (if*(nilp xs) ret
      (let ([mo (most [lam(l r)(?(g l r)r l)] xs)]) ;! if repeat ;maxs longest
        [~ (remove! mo xs) (cons mo ret)] ;
      )
  ) )
  (~ xs nil)
)
(defn mysort (xs g) ;?(lam(l r)[odd?(+ l r)]) ;800~~1500X slower than sort
  (def (~ xs ret)
    (cond
      [(nilp xs) ret]
      [else
        (letn ( [a  (car xs)]
                [lr  (filter2 (lam(~)(g ~ a)) [cdr xs])] ;
                [pre (car lr)]
                [pos (cadr lr)] )
          [~ pre (cons a [~ pos ret])] ;
  ) ] ) )
  (~ xs nil)
) ;-> tail?

;exercise
(def cond? condition?)
(defsyn try
  ([_ exp]
    (guard (x(els x)) exp) ;(condiction? #condition) -> *t
) )

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

(defn call-nest (g . xs)
  (defn ~ (g xs)
    (if (nilp xs) (g)
      (~ (g (car xs)) (cdr xs))
  ) )
  (~ g xs)
)
(def callnest call-nest)

(defn call-snest (g . ys)
  (defn ~ (g ys)
    (if (nilp ys) g
      [~ (g (car ys)) (cdr ys)]
  ) )
  (~ g ys)
)
(def callsnest call-snest)

;ffi

(defsyn defc
  ( [_ ret f args]
    (def f (foreign-procedure (sym->str 'f) args ret)) ;outer-proc
) )

;
(def load-lib load-shared-object)
(def ffi? foreign-entry?) ;
(alias ffi foreign-procedure)


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
      (echol ":" 'g)
      (setq t (clock*))
      (setq res g)
      (setq t (-(clock*)t))
      (echol ": elapse =" t "s")
      (li res t)
) ) )
(defsyn elapse ;just elapse but result
  ( [_ g]
    (let ([t 0])
      (echol ":" 'g)
      (setq t (clock*))
      g
      (setq t (-(clock*)t))
      (echol ": elapse =" t "s")
      t
) ) )

(defn_ mem?@ (x xs)
  (if (nilp xs) *f
    (if (eql x (car xs)) *t
      (_ x (cdr xs))
) ) )
(def mem? member)

(defn remov-same (xs)
  (defn _ (ts xs)
    (if (nilp xs) ts
      (let ([a (car xs)])
        (if (mem? a ts)
          (_ ts (cdr xs))
          (_ (conz ts a) (cdr xs))
  ) ) ) )
  (_ nil xs)
)


;Code written by Oleg Kiselyov

(def-syn ppat ;ppattern for ?
  (syn-ruls (? comma unquote quote) ;comma for unquo?
    ([_ v ? kt kf] kt)
    ([_ v () kt kf] (if (nilp v) kt kf))
    ((_ v (quote lit) kt kf) (if (equal? v (quote lit)) kt kf)) ;x?
    ([_ v (unquote var) kt kf] (let ([var v]) kt))
    ([_ v (x . y) kt kf]
      (if (pair? v)
        (let ([vx(car v)] [vy(cdr v)])
          (ppat vx x (ppat vy y kt kf) kf) )
        kf
    ) )
    ([_ v lit kt kf] (if [equal?(quote lit)v] kt kf))
) )
;(ppat '(1 b) (,a b) *t *f)
;(ppat '(2 3) (,a ,b) b *f)

(def-syn pmatch-aux
  (syn-ruls (else guard)
    ([_ name (rator rand ...) cs ...] ;rator rand
      (let ([v (rator rand ...)])
        (pmatch-aux name v cs ...) )) ;cs?
    ([_ name v] ;err-case
      (bgn
        (if 'name
          (printf "pmatch ~s failed\n~s\n" 'name v)
          (printf "pmatch failed\n ~s\n" v))
        (error 'pmatch "match failed")
    ) )
    ((_ name v [else e0 e ...]) (bgn e0 e ...))
    ((_ name v [pat (guard g ...) e0 e ...] cs ...) ;pat for pattern
      (let ([fk (lam() (pmatch-aux name v cs ...))])
        (ppat v pat
          (if(and g ...) (bgn e0 e ...) (fk))
          (fk)
    ) ) )
    ((_ name v [pat e0 e ...] cs ...)
      (let ([fk (lam() (pmatch-aux name v cs ...))])
        (ppat v pat (bgn e0 e ...) (fk))
) ) ) )

(def-syn pmatch ;~= aux ;p for pat
  (syn-ruls (else guard)    ;guard for ?
    ([_ v      (e ...) ...]
      (pmatch-aux  *f  v (e ...) ...) )
    ([_ v name (e ...) ...] ;v for xsValue, name for aux-info
      (pmatch-aux name v (e ...) ...)
) ) )

;yin's code

(def cps
  (lam (exp)
    (letrec
      ( [trivial? (lam (x)
            (memq x '(zero? add1 sub1)) )] ;
        ;[id   (lambda (v) v)]
        [ctx0 (lambda (v) `(k ,v))]      ; tail context
        [fv (let ([n -1])
              (lam ()
                (set! n (+ 1 n))
                (string->symbol (string-append "v" (number->string n)))))]
        [cps1 (lam (exp ctx)
            (pmatch exp ;
              ( ,x [guard (not(pair? x))] (ctx x) )
              ( (if ,test ,conseq ,alt)
                [cps1 test (lam (t)
                    (cond
                      [(memq ctx (list ctx0 id))
                       `(if ,t ,(cps1 conseq ctx) ,(cps1 alt ctx))]
                      [else
                        (let ([u (fv)])
                         `(let ([k (lambda (,u) ,(ctx u))])
                            (if ,t ,(cps1 conseq ctx0) ,(cps1 alt ctx0))
              ) ) ] ) ) ] )
              ( (lam (,x) ,body)
                (ctx `(lambda (,x k) ,(cps1 body ctx0))) )
              [ (,op ,a ,b)
                [cps1 a (lam (v1)
                    [cps1 b (lam (v2)
                        (ctx `(,op ,v1 ,v2))
              ) ] ) ] ]
              [ (,rator ,rand)
                [cps1 rator (lam (r)
                    [cps1 rand (lam (d)
                        (cond
                          [(trivial? r) (ctx `(,r ,d))]
                          [(eq? ctx ctx0) `(,r ,d k)]  ; tail call
                          [else
                            (let ([u (fv)])
                             `(,r ,d (lam (,u) ,(ctx u)))
      ) ] ) ) ] ) ] ] ) ) ] )
      (cps1 exp id)
) ) )


;to-test: (cps ...)
 
(def (stop? p) ;p for process() ;tarball of p can be read by stop?.
  (if (loop? p)
    (if (repeat? p) ;-> myif: nil ~= #f
      '!stop
      (judge-!repeat-case p) )
    (judge-!loop-case p)
) )

;@
(def (time- . ts)
  (letn
    [ (resl
        [redu
          (curry map
            [lam xs
              (if (num?(car xs)) (redu - xs)
                (car xs) ) ] )
          ts ] )
      (hr (car resl))
      (2nd.is.min (num?(2nd resl)))
      (mn [(if 2nd.is.min 2nd 3rd) resl])
      (bmn (<0 mn)) ]
    (setq
      mn (if bmn (+ mn 60) mn)
      hr (if bmn (- hr 1) hr)
      hr (if (< hr 0) (+ hr 24) hr) )
    (cons hr ([if 2nd.is.min id (curry cons (2nd resl))] (li mn)))
) )

;complex-syntax

(define-syntax define-c-function
  (lambda (x)
    (define gen-id
      (lambda (k value)
        (datum->syntax k ;
          (string->symbol
            (id
              (let ([v (syntax->datum value)]) ;datum
                [if (string? v) v (symbol->string v)]
    ) ) ) ) ) )
    (syntax-case x () ;
      ( [k cfnam (In ...) Ret]
        (with-syntax ([name (gen-id #'k #'cfnam)]) ;
         #'(define name ;
            (foreign-procedure [if (string? 'cfnam) 'cfnam (symbol->string 'cfnam)]
              (In ...) Ret
      ) ) ) )
) ) )

;(def (calc-ratio-array s nMid e fac) ) ;3 1 6 2 -> '(3 4 6)


; (def car car%) ;
; (def cdr cdr%)
; (def caar (compose car car) )
; (def cadr (compose car cdr) )
; (def cdar (compose cdr car) )
; (def cddr (compose cdr cdr) )
;cddddr



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def (clean) (restore))
(def (restore)
  (setq nil nil
    ; car car.ori
    ; cdr cdr.ori
    ;append append.ori
    ;map map.ori
    ;+   +.ori
) )


(def (reload-it)
  (clean)
  (load (symbol->string 'c:/mylib/chez/chez-lib.ss))
   ;当在foo.scm文件中出现load-relative(MzScm)调用时，它的参数的路径将根据文件foo.scm所在目录的路径来计算
  ;(load-relative (symbol->string 'chez-lib.ss)) ;getcmdline read
)
(def refr reload-it)