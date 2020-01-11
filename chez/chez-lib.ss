; Chez-lib.ss v1.4e - Written by Faiz

#|
  logging: -- about: 22.85 chars/line
    v1.4e: Fixed bug of +.ori
    x v1.4a: def/defa supports disordered-default-paras    
    
  suffixes:
    @ bad / slow
    % theoretic / internal / paras->list
    ;~ optimized
    * extensional
    ! with side-effect
  
  prefixes:
    sy/ syntax
    ~ return a reverse result
  
  vars:
    ~var temp variety
    *global_var*

  versions: fast; Grace; safe; experimental; 
  
  Which ops are slow?:    
    last-pair last list?
    length
    append->conz->rpush ... slowest
    ? eval->reduce->compose/curry
    strcat
    remove
    lis->vec vec->lis
  fast>:
    sort, .., cond if, .., map, .., append;
    syntax, func    
    def_ set!~def alias
    cons vector list
  not the fastest achievement:
    reverse append! list-copy 
  ?
    apply let 
    eq, =, eql

  todo:
    see to: verb.adj.a./act, prep./judge,
    lam/defa lam_ 
    [random-seed (floor->fix(w* (elapse(fib 500000))))] ;too closed ;~> parallel universe id bytes, not work well
      time.ms->md5->cost.ns?
      . time activities info net:salt io? file:psw/md5
    (nthof-g-resl rand '(3 1 4) [max-n 10000000])
    (nthof-g rand nth [len 1])
    d-rev
    grep grep-rn 
    reload? load compile udp/tcp get/post v3 juce ui test trace
    if(!#f/nil): cadr caddr cadddr eval, repl
    cond case, for map lambda foldl reduce curry recursion repl foldr
    (range% sum f p n)
    ? (str/sep sep . xs)
      -> echo
      => any->int
    (_ xs . x) (-> -> x)
    code:dsl->raw
    api-search 可以 下载个网页, 然后用正则搜索; 每次defn时,记录信息到hashtable
    有些函数实现的层数/维数太高, 后面需要搞个降维函数. for?, cps?
    church yc algo
    structure:
      skip-list/max-skip-step/for-spec-type/with-logic, path
        ?`[(4) ([(1 a) 2 3] [4 5 6])]
      b+tree
    AI:
    math memo combinations, eval. match
    solve24 https usd/usdt pcre
    def/setq-glob
    car! (cons 1 2 '()) cons! conz! 
    rev!
    seems that newlisp call scheme and c will be more free.
  
  cant/hard: get-addr  
  cant implete the same thing:
    apply call/cc? 
    
  seq of implements:
    (g x y)~> apply~= reduce-> curry

  tolearn:
    三体是否碰撞的检测, 说是平面会 空间不会? 宇宙遇到三体问题,怎么计算?
    my: let + redu sort! rand eval
    hygienic assq memq define-structure
    >: [syntax-case see to ;push] defsyn def
    ;define-syntax syntax-rules syntax->datum=datum 
    datum->syntax=syntax=#' with-syntax with-implicit syntax-case #, fluid-let-syntax ...
    (let ([ret ..]) (ev `(setq x ',ret))
    un/trace debug
    list: -tail/head/ref
    apis: #%$xxx
    (trace funxxx) (funxxx ...) can show is it a tail form rec
    hash when def/setq/defsyn ~> api-search
    vec: cons lam/vec def/vec, map for redu, add! del/rm! flat strcat
    b-plus-tree: '[(8? 15) () () ([1 2][4 5][6 8][9 11][12 15])]
    sy: rev, vec? flat append? group
    sort: qsort heap merge
    abs(fxnum) <= 2^29-1 (> 5E)    
    (eval-when (compile) (optimize-level 3))
  learned
    body... != body ...
    let-values(<->)
    def-syn doesnt supp recursion directly, but case
    def-syn cant be in ano def-syn
    
  beauties:
    reverse flat deep-count bump
  to-be-beauty:
    curry compose
    
  to-try
    walker 
    
  to-optimize:
    ;def_: fluid-let-syntax
    def-syn
    def f g -> alias f g
    ;def_/def -> def (def (_ ..) ..) ..
    nilp (cdr xs)
    [] -> ()
    (small .. big) -> (big .. small)
    ?: setq
    
  to-debug:
    (trace fib)?, assert&print, debug?, call/cc+assert+return.false ...

  flow: work->fast->safe->complete
    ;must-inits
    ; main-apis
    ;apis-for-main
    ; apps-api
    ;endups
    ; test
    
  common:
    (_ X x)
    ? syt -> '
    common/special... common-special...
|#

(alias ali      alias)
(alias imp      import)
(alias lam      lambda)
(alias letn     let*)
(alias bgn      begin)
(alias quo      quote)
(alias def-syn  define-syntax)
(alias syn-ruls syntax-rules)
(alias syn-case syntax-case)
(alias case-lam case-lambda)
(alias els      else)
(alias fn       lambda)
(alias progn    begin)
(ali vec      vector)
(ali vecp     vector?)
(ali vec-ref  vector-ref)
(ali vec->lis vector->list)
(ali lis->vec list->vector)
(ali veclen   vector-length)

(def-syn define* ;
  (syn-ruls () ;
    ( [_ x]
      (define* x *v) )
    ( [_ (g . args) body ...]
      (define (g . args) body ...) )
    ; ( [_ g (args ...)] ;x _ ' ... ;(def a '(...))
      ; (define (g args ...) *v) )      
    ( [_ x e]
      (define x e) ) ;symp? e: e *v
      
    ;Plz use defn instead of the followings, and they make def slow:
    ; ( [_ g (args ...) body ...]
      ; (define (g args ...) body ...) ) ;
    ; ( [_ g args body ...] ;
      ; (define (g . args) body ...) )
) )
(ali def define*)

(def-syn defm ;define-macro <- define-syntax ;to-add (void)
  (syn-ruls ()
    ( [_ (f . args) body ...]
      (defsyn f
        ( [_ . args]
          (bgn body ...)
    ) ) )
    ( [_ f (args ...) body ...]
      (defm (f args ...) body ...)
) ) )

(ali nilp  null?)
(ali first car)
(ali rest  cdr)
(ali eq    eq?)
(ali equal equal?)
(ali eql   equal?)
(ali ==    equal?)
(ali ?: if)
(ali ?  if)
(ali !  not)
(ali sym?   symbol?)
(ali bool?  boolean?)
(ali int?   integer?)
(ali num?   number?)
(ali str?   string?)
(ali lisp   list?)
(ali consp  pair?)
(ali pairp  pair?)
(ali fn?    procedure?)
(ali voidp  void?) ;voip
(ali atomp  atom?) ;atop
(ali nump   number?)
(ali exa->inexa exact->inexact)
(ali inexa->exa inexact->exact)
(ali sym->str symbol->string)
(ali ev     eval)
(ali reduce apply) ;
(ali redu   apply) ;
(ali strcat string-append)
(ali foldl  fold-left)
(ali foldr  fold-right)
(ali mod remainder) ;
(ali %   mod) ;
(ali ceil ceiling)
(ali 1st  first)
(ali 2nd  cadr)
(ali 3rd  caddr)
(ali identities values)
(ali repl new-cafe)
(ali fmt format)
(ali exec command-result) ;
(ali sys system)
(ali q exit)
(ali str-append string-append)
(ali len length)
(ali newln newline)
(ali nil?  null?)

(ali redu~ redu~/fold)
(ali strhead! string-truncate!)

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
          ( [_ . args] ;
            (g . args) ) ) ) )
    ( [_ f (expr ...) ...]   ;multiple
      (def-syn f
        (syn-ruls ()
          ( expr
            ...
          )
          ...
) ) ) ) )
(ali def-syt def-syn)
(ali defsyt defsyn)

(def-syn (if% stx)
  (syn-case stx (else)
    ([_ () (bd ...)]
    #'(cond bd ...) )
    ([_ (last-expr) (bd ...)]
    #'(if% () (bd ... [else last-expr])) )
    ([_ (k e more ...) (bd ...)]
    #'(if% (more ...) (bd ... [k e])) )
) )
(def-syn (if* stx)
  (syn-case stx ()
    ([_ bd ...]
      #'(if% [bd ...] []) ;
      ;#'[sy-redu cond (group (bd ...) 2)] ;sy-group
) ) )
(ali if~ if*)

; (def-syn (if* stx) ;? ?: cond->if
  ; (syn-case stx (else) ;nil?
    ; ([_ k d]
    ; #'(if k d) )
    ; ([_ k d e]
    ; #'(if k d e) )
    ; ([_ k d else e]
    ; #'(if k d e) )
    ; ([_ k d bd ...] ;#'(cond (k d) bd ...)
    ; #'(if k d
        ; (if* bd ...) )
; ) ) )

(defsyn defun
  ( [_ f (args ...) ]
    (define (f args ...) *v) )
  ( [_ f args ]
    (define (f . args) *v) ) ;
    
  ( [_ f args ...]
    (define f (lam args ...)) )
)
(ali defn defun)

(defsyn defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( [_ f args body ...]
    (define f
      (eval ;
        (foldr
          [lam(a b)(append~ a (list b))]
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

;(define-syntax _ (syntax-rules () )) ;for export
(define-syntax def_ ;i think it s good
  (syntax-rules ()
    [(_ (id . args) body ...)
      (def_ id (lambda args body ...))] ;for lambda format
    [(_ id expr)
      (define id
        (fluid-let-syntax ([_ (identifier-syntax id)]) ;
          expr
) ) ] ) )
;(def_ (asd n) [if(< n 1) nil (cons n [_ (1- n)])])
;(ali def_ def/_)

(defsyn defn_
  ( [_$% f args bd...] ;
    (def_ (f . args) bd...)
) )

(defsyn setq
  [(_ a) (set! a (void))]
  ((_ a b)
    (bgn (set! a b) (if *will-ret* a))
  )
  ((_ a b c ...)
    (bgn
      (set! a b)
      (setq c ...) ;
) ) )

(def-syn lam* ;% @?
  (syn-ruls()
    ([_ x1 bd ...]
      (lam x2
        (redu [ev `(lam ,(flat 'x1) bd ...)] ;redu ev
          (flat x2) )
    ) )
) )

;

(def-syn (append!% stx) ;
  (syn-case stx ()
    ( [_ xs . yz]
      [identifier? #'xs]
      #'(bgn
          [set! xs (append xs . yz)] ;
          xs ) )
    ( [_ . xz]
      #'(append . xz)
) ) )
(def append!.ori append!) ;
(def (append! xs . yz) ;?
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        (append!% xs [_ (car yz) (cdr yz)]) ;
        (bgn
          (set-cdr! (last-pair xs) [_ (car yz) (cdr yz)])
          xs
  ) ) ) )
  (_ xs [remov-nil yz]) ;when to ys/cons/append!/set-cdr!
)

(def (curry g . args) ;curry(0~)2
  (lam xs
    (redu g ;
      (append~ args xs)
) ) )
(def (rcurry g . args)
  (lam xs
    (redu g
      (append~ xs args)
) ) )
(def (curry~ g . args)
  (lam xs
    (redu~ g ;
      (append~ args xs)
) ) )
(def (rcurry~ g . args)
  (lam xs
    (redu~ g
      (append~ xs args)
) ) )

(ali call/k call/cc)

(defsyn cacc ;
  ([_ (k) bd ...]
    (call/cc [lam (k) bd ...])
) )
(defm (let/cc k bd ...) ;
  (call/cc (lam (k) bd ...))
)

;

(def *f #f)
(def *t #t)
(def *v (void))
(def *e '[(err)]) ;
(def nil '()) ;
(def spc " ")
(def Fal  *f) ;
(def Tru  *t)
(def No   *f)
(def Yes  *t)
(def Void *v)
(def Err  *v) ;

(def void? (curry eq *v))
(def (str/pair? x) [or(string? x)(pair? x)]) ;x
(def (str/pair/vec? x) [or(string? x)(pair? x)(vector? x)]) ;for eql/eq

(def (id x) x)
(ali identity id)
(def (li . xs) xs) ;~

(def car.ori car)
(def cdr.ori cdr)
(def (car% xs)
  (if (atomp xs) Err
    (car xs) ;.ori
) )
(def (cdr% xs)
  (if (atomp xs) Err
    (cdr xs)
) )

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


(def (return x) (if *will-ret* x 'done)) ;

(def (set-alp! pr x)
  (set-car! (last-pair pr) x)
)
(def (set-dlp! pr x)
  (set-cdr! (last-pair pr) x)
)

;

(defn conz (xs . ys)
  (if (nilp ys) xs
    (append xs ys) ;! a a -> cycle
) )
;(ali conj conz)

(defsyn sy/num-not-defa-vals%
  ([_ () n] n)
  ([_ ((x vx)) n]       (sy/num-not-defa-vals% () n))
  ([_ (x) n]            (sy/num-not-defa-vals% () (fx1+ n)))
  ([_ ((x vx) y ...) n] (sy/num-not-defa-vals% (y ...) n))
  ([_ (x y ...) n]      (sy/num-not-defa-vals% (y ...) (fx1+ n))) ;
)
(defsyn sy/num-not-defa-vals ;good for: (_ a [b 1] c)
  ([_ . xs] (sy/num-not-defa-vals% xs 0))
)

;(_ '(a [b 2] [c]))
(defn num-not-defa-vals (paras)
  (def (_ paras n)
    (if (nilp paras) n
      (let ([a (car paras)][d (cdr paras)])
        (if (consp a)
          (if (atomp (cdr a))
            [_ d (1+ n)]
            [_ d n] )
          [_ d (1+ n)]
  ) ) ) )
  (_ paras 0)
)

(def (list-elements xs) ;(_ '(a (b) (c 1) d)) ~> '((a) (b) (c 1) (d))
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)])
        (if (sym? a) ;consp lisp sym?
          (cons (li a) [_ (cdr xs)])
          (cons a [_ (cdr xs)]) ;
  ) ) ) )
  (_ xs)
)
(def (list-the-front xs) ;partly ;(_ '(a (b) (c 1) d)) ~> '((a) (b) (c 1) (d)) ~> '((a) (b) (c 1) (d nil))
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)])
        (if (sym? a) ;consp lisp sym? ?
          (cons (li a) [_ (cdr xs)]) ;
          xs ;
  ) ) ) )
  (_ xs)
)
(defsyn sy/list-the-front ;
  ( [_ ()] '())
  ( [_ ((x ...) . xs)] '((x ...) . xs))
  ( [_ (x)] (cons '(x) [sy/list-the-front ()])) ;
  ( [_ (x . xs)]
    (cons '(x) [sy/list-the-front xs]) ;
) )

(def (defa->vals/aux paras vals nths-defa-part nths-not-defa nths-defa-rest) ;
  (def (_ paras vals n-head n-ndefa n-tail ret)
    (if (nilp paras) ret ;
      (if (nilp vals)
        [_ nil nil 0 0 0 [append~ (map [compose ev cadr] paras) ret]]
        (letn ([a (car paras)] [d (cdr paras)]) 
          (if (cdr-nilp a)
            [_ d (cdr vals) n-head (1- n-ndefa) n-tail (cons[car vals]ret)]
            (if (<1 n-head)
              [_ d vals 0 n-ndefa (1- n-tail) (cons(ev[cadr a])ret)] ;
              [_ d (cdr vals) (1- n-head) n-ndefa n-tail (cons[car vals]ret)]
  ) ) ) ) ) )
  [rev (_ paras vals nths-defa-part nths-not-defa nths-defa-rest nil)]
)

(defsyn def/defa ;(_ (g [a] [b 2] [c ]) (+ a b c))
  ( [_ (g . paras) body ...] (def/defa g paras body ...)) 
  ( [_ g paras% body ...]
    (define (g . args) ;
      (let ([paras (list-elements 'paras%)]) ;
        (define f% [ev `(lam ,(map car paras) body ...)]) ;
        (letn ( [paras-ln (len paras)]
                [num-not-defa (num-not-defa-vals paras)] ;
                [vals-ln (len args)]
                [n-head (- vals-ln num-not-defa)]
                [n-tail (- paras-ln vals-ln)] )
          ;(echol n-head num-not-defa n-tail)
          (redu f%
            (defa->vals/aux paras [list-head args paras-ln] ;
              n-head num-not-defa n-tail
) ) ) ) ) ) )
;We may def func again with some defa paras, and test the func with just one variable para.
;(def/defa asd ([a 2] b [c *]) (c a b)) (asd 3) (asd 4 3) (asd 4 3 +)
;(ali defa-def defa-def2)

; (defsyn def/defa ;(_ (g [a] b (c 3) (d 4) e) (+ a b c d)) ;lam/defa ;todo: test@, (d 4) e
  ; ( [_ (g . paras) body ...] (def/defa g paras body ...))
  ; ( [_ g paras body ...]
    ; (defa-def g paras body ...)
; ) )
(ali def/values def/defa)

;common

(def (redu~/fold g xs) ;-> curry/compose~ ;elements of xs must be simular
  (if (nilp xs) (g)
    (foldl g (car xs) (cdr xs)) ;wrong sometimes: values map echo ;echo ~> '(*v) ;evs ;i/o
) ) ;curry?

(def-syn vec-for
  (syn-ruls (in)
    ( [_ i in ve body ...]
      (quiet
        (vector-map ;
          (lambda (i)
            body ... )
          ve )
) ) ) )
          
(def-syn for
  (syn-ruls (in : as)
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
          
    ( [_ () b1 ...] ;;(for ((+ 2 3)) ..) ;i?
      (let loop ()
        (when Tru
          b1 ...
          (loop) ) ) )
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
          ((> step 0)
            (when (<= i to)
              b1 ...
              [loop (+ i step)]
          ) )
          ((< step 0)
            (when (>= i to)
              b1 ...
              [loop (+ i step)]
          ) )
          (else nil)
    ) ) )
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

(defsyn while
  ([_ k bd ...]
    (call/cc
      (lam (break)
        (let loop ()
          (if k
            [bgn bd ... (loop)]
            (break) ;
) ) ) ) ) )

(defm (sy-redu g (x ...))
  (g x ...)
)

;

(def (compose . gs) ;
  (def (_ ret gs)
    (if* ;[nilp gs] id ;nop x.id x.li
      [nilp (cdr gs)]
      (lam xs (ret [redu(car gs) xs]))
      (_ 
        (lam (x) (ret [(car gs) x]))
        (cdr gs)
  ) ) )
  (_ id gs)
)

(define floor->fix (compose flonum->fixnum inexact))

; todo: (_ + 2 * 3) (_ f a g b ...)
; (def (compose-fx . fxs) ;see to compose and xn-mk-list
  ; (_ (curry [car fxs] [cadr fxs]) [cddr fxs])
; )

(def (compose-n . xs) ;f m g n ...
  (redu compose
    (xn-mk-list% xs)
) )

; (def (map2 g xs yz)
  ; (def (_ xs ys zz)
    ; (if (nilp zz) (map g xs ys)
      ; [_ ]
  ; ) )
  ; (let ([yz2 (remov-nil yz)]
    ; (if (nilp yz2) nil
      ; (if (nilp xs) 
        ; (_ xs (car yz2) (cdr yz2))
; ) ) ) )

(def map*
  (case-lam
    ([g xs]   (map g xs))
    ([g . xz] (redu~ (curry map g) xz)) ;(_ + '() '(1)) => '(1)
    (else     nil)
) )


(def (len* x)
  ( (if* [str? x] string-length
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

;strcat
; (def (strcat% ss)
  ; (def (_ ss ret)
    ; (if (nilp ss) ret
      ; [_ (cdr ss) [append~ (string->list (car ss)) ret]]
  ; ) )
  ; (list->string (_ ss nil)) ;(list->string [append% (map string->list ss)])
; )

(def (nstrs s n)
  ;(redu strcat (xn2lis s n))
  [list->string (nlist% (string->list s) n)]
)

(def/defa (string-divide s [sep " "])
  (if (eql "" sep) [str->ss s]
    (let ([chs(string->list s)] [csep(car(string->list sep))]) ;
      (def (rev->str chs)
        (list->string(rev chs)) )
      (def (_ chs tmp ret)
        (if [nilp chs] (cons[rev->str tmp]ret)
          (let ([a(car chs)]) ;
            (if [eq a csep] ;
              [_ (cdr chs) nil (cons[rev->str tmp]ret)] ;
              [_ (cdr chs) (cons a tmp) ret]
      ) ) ) )
      [rev(_ chs nil nil)]
) ) )

(define (list->revstr chs) ;lis->revstr
  (list->string (rev chs))
)
(define (string-divide-rhs-1 s sep) ;todo: str-sep
  (if (eq? "" sep) [str->ss s]
    (if (eq? "" s) "" ;
      (let ([chs(string->list s)] [csep(car(string->list sep))]) ;
        (define (_ chs ret)
          (if (null? chs) (list "" [list->string ret]) ;
            (let ([a (car chs)]) ;
              (if [eq? a csep] ;
                (list [list->revstr chs] [list->string ret]) ;
                [_ (cdr chs) (cons a ret)]
        ) ) ) )
        [_ (rev chs) '()]
) ) ) )
(def (string->path-file s)
  (string-divide-rhs-1 s "/")
)

(def (str/sep sep . ss)
  (def (_ chz ret)
    (if (nilp chz) ret
      (let ([a (car chz)])
        (if [nilp a]
          [_ (cdr chz) ret]
          [_ (cdr chz) (append a (cons sep ret))] ;
  ) ) ) )
  (let ([chz [rev(map string->list ss)]])
    (str(_ [cdr chz] [car chz]))
) )

(def (num2nth n)
  (str n
    (case (% n 10)
      (1 "st")
      (2 "nd")
      (3 "rd")
      (else "th")
) ) )

(def (num2mon n) ;int
  (let ([mons '(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec)])
    (if* (> n 12) nil
      (< n 1) nil
      (str (list-ref mons [1- n]))
) ) )

;

(def (append% xz)
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        [_ (car yz) (cdr yz)]
        (cons (car xs) [_ (cdr xs) yz])
  ) ) )
  (let ([xz2 (remov-nil xz)])
    (_ (car xz2) (cdr xz2)) ;
) )

(def (append~ . xz)
  (apply append (remov-nil xz))
)


; (defn conz! (xs . ys) ;->syn
  ; (set-cdr! (last-pair xs) ys)
  ; xs
; )


(def (cls) [for(42)(newln)])

;

(def *will-ret* #f)
(def *will-disp*  #t)
(def (show-asm-code b) (#%$assembly-output b))

;

(def (last pr)
  (car (last-pair pr))
)
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


;sy-

(defsyn sy-rev% ;
  ([_ () (ret ...)] '(ret ...)) ;
  ([_ (x) (ret ...)]
    '(x ret ...) )
  ([_ (x ys ...) (ret ...)]
    (sy-rev% [ys ...] [x ret ...]) )
)
(defsyn sy-rev
  ([_ (xs ...)]
    [sy-rev% (xs ...) ()] )
  ([_ xs ...]
    [sy-rev% (xs ...) ()] )
)

(defsyn lam-nest% ;(_ (a b) bd...) -> [lam(a)[lam(b) bd...]]
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    [lam(x) (lam-nest% (ys ...) [ret ...])] ) ;
)
(defsyn lam-rnest%
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    (lam-rnest% (ys ...) [lam(x) [ret ...]]) )
)

(defsyn lam-rnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) [lam() bd ...]] )
)
(defsyn lam-srnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) (bgn bd ...)] )
)
(defsyn lam-nest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [lam() bd ...]] )
)
(defsyn lam-snest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [bgn bd ...]] )
)

;quo/sym-

(def (sym-redu sym-f xs) ;(quo-redu 'setq '(a 1))
  (ev (cons sym-f xs)) ;
  ;(ev `(sym-f ,@xs)) ;map-q 1st-q
)

;

(def (quiet . xs) )
(ali todo quiet)
(ali tofix id)
(ali ?~ if*)

(defn str-mapcase% (mf s)
  (list->string (map mf (string->list s))) ;
)
(ali str-upcase   string-upcase)
(ali str-downcase string-downcase)

(defn swap-para (g)
  (lam xs
    (redu g (rev xs)) ;!?
) )


; (defsyn cons~
  ; ([_ xs ...] ;[_ 1 2 3 '(4)] ~> [~ '(4) 3 2 1]
    ; (redu cons* (sy-rev xs ...))
; ) )

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

; list

(def cdr-nilp (compose nilp cdr))

(def/defa (assoc-g x ys [g id])
;(def (assoc-g x ys g)
  (let ([= (eq/eql x)])
    (def (_ ys)
      (if (nilp ys) nil ;
        (if [= (caar ys) x] 
          (g (car ys))
          [_ (cdr ys)]
    ) ) )
    (_ ys)
) )

(def (w* num) (* num 10000))

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

(def/defa (remov-1?/g x xs [g eql])
;(def (remov-1?/g x xs g) ;result / #f
  (call/cc (lam [k]
      (def (_ xs)
        (if (nilp xs) [k Fal]
          (let ([a(car xs)] [d(cdr xs)])
            (if (g a x) d
              (cons a [_ d])
      ) ) ) )
      (_ xs)
) ) )

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
  (def (_ xs m)
    (if* (nilp xs) nil
      (< m 1) xs
      [_ (cdr xs) (1- m)]
  ) ) 
  (_ xs m)
)
(def (list-head xs m) ;%
  (def (_ xs ret m)
    (if* (nilp xs) ret
      (< m 1) ret
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

(defn list/nth- (xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li n (car xs))
        [_ (cdr xs) (1+ n)]
  ) ) )
  (_ xs 1)
)
(ali list/nth list/nth-)
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

(def (len-cmp f . xs) [redu f (map len xs)]) ;redu? len*?

(def (most% g xs . yz) ;(most (lam(l r)(?(> l r)l r)) 1 2 3)
  (def (_ xs yz)
    (if (nilp yz) xs
      (_ [g xs (car yz)] (cdr yz))        
  ) )
  (_ xs yz)
)
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
            (pos (ncdr xs n)) ] ;
      (set! xs (append! pre (cons y pos)) ) ;!
) ) )
(defsyn set-nth!
  ([_ xs n y] (set-xth! xs (1- n) y))
)
(defsyt insert-xth!
  ([_ xs i y]
    (letn([pre (list-head xs i)]
          [pos (list-tail xs i)])
      (setq xs (append! pre (cons y pos)))
) ) )
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


(def-syn (pop stx)
  (syn-case stx ()
    ( [_ xs]
      [identifier? #'xs]
      #'[setq xs (cdr xs)] )
    ( [_ xs]
      #'(car xs) )
) )

(defn rpush~ [a xs]
  (set-cdr! (last-pair xs) (li a)) ;loop
  (return xs)
)
(ali rpush rpush~) ;

(def-syn (push stx)
  (syn-case stx () ;
    ([_ args ... x]
      (identifier? #'x) ;
      #'[setq x (cons* args ... x)] ) ;
    ([_ . args]
      #'(cons* . args)
) ) )


(def (command-result cmd)
  (let-values
    ( [ (in ou er id)
        (open-process-ports cmd
          (buffer-mode block)
          (make-transcoder (utf-8-codec)) ) ] ;
    )
    (let loop ([ret ""])
      (if (eof-object? (peek-char ou)) ret ;\r\n?
        [loop (str ret (read-char ou))] ;% strcat
) ) ) )


(defsyn type-main ;todo detail for printf
  ( [_ x]
    (cond
      ;((ffi-s? (any->str 'x))  "ffi") ;x if not sym
      ((sym?  x)      "symbol") ;
      ((bool? x)      "boolean")
      ((num?  x)      "number") ;
      ((char? x)      "char") ;
      ((str?  x)      "string") ;
      ((nil?  x)      "null")
      ((list? x)     "list") ;
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

(def (bool->string b) (?: (fal? b) "#f" "#t"))

; (def (any->str/raw x)
  ; (cond
    ; ((symbol? x) (sym->str            x)) ;
    ; ((bool?   x) [if x "#t" "#f"]) ;               x
    ; ((number? x) (number->string      x))
    ; ((char?   x) (list->string (list  x)))
    ; ((string? x)                      x)
    ; ((list?   x) (lis->str            x))
    ; ((pair?   x) (lis->str(pair->list% x)))
    ; ((fn?     x)  "") ;ty?
    ; ((atom?   x) (sym->str           'x)) ;
    ; (els          "")
; ) )
(defm (raw . xs) ;
  (if~ (nilp 'xs) nil
    (cdr-nilp 'xs) (car 'xs)
    'xs
) )

(def (any->str x)
  (cond
    ((symbol? x) (sym->str            x)) ;
    ((bool?   x)  "") ;               x
    ((number? x) (number->string      x))
    ((char?   x) (list->string (list  x)))
    ((string? x)                      x)
    ((list?   x) (lis->str            x))
    ((pair?   x) (lis->str(pair->list% x)))
    ;((ffi?   x) (sym->str           'x)) ;name?
    ((fn?     x)  "") ;ty?
    ((atom?   x) (sym->str           'x)) ;
    (els          "")
) )
(defn lis->str (xs)
  (redu~ strcat (map any->str xs))
) ;lis2str

(def (list->num xs) ;10 based
  (def (_ xs ret)
    (if (nilp xs) ret
      [_ (cdr xs) (+ (* ret 10) [car xs])]
  ) )
  (_ xs 0)
)
(ali lis2num list->num)

(def (str . xs) (lis->str xs))

(def (pair->list% pr) ;'(1 . ()) ~> '(1 ())
  (li (car pr) (cdr pr))
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

(def (call g . xs) (redu g xs)) ;
(def (rcall% g . xs) (redu g (rev xs)))

(defn member?@ (x xs)
  (cond
    ( [nil? xs] *f)
    ( (or [eql x (car xs)] ;
        (member? x (cdr xs))
) ) ) )

(def (echo% sep . xs) ;(_ xs [sep " "]) ;voidp
  (def (_ sep xs)
    (case [len xs] ;
      (0 *v)
      (1 (disp (car xs))) ;
      (else
        (disp (car xs) sep)
        [_ sep (cdr xs)] ;
  ) ) )
  (if *will-disp*
    (_ sep xs)
) )
(def (echo . xs) (apply echo% (cons " " xs))) ;

(defn mk-range% (s e p)
  (let ([g (if(> p 0) > <)])
    (def (_ ret cnt)
      (if (g s cnt) ret
        [_ (cons cnt ret) (- cnt p)]
    ) )
    [_ nil e]
) )
(def range
  (case-lambda
    ((a)     (mk-range% 0 (1- a) 1))
    ((a b)   (mk-range% a b 1))
    ((a b c) (mk-range% a b c))
) )

(def (vec-range n)
  [def (_ n ret)
    (for (i n)
      (vector-set-fixnum! ret i i) )
    ret ]
  [_ n (make-vector n)]
)

(def/defa (range* n\s (e nil)(f +)(p 1)) ;@
  (def (_ n\s e f p res)
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

(def (echol . xs)
  (apply echo xs) (newln) ;
)

(defn read-expr xs ;
  (let
    ( [p(open-input-string
          (redu~ strcat
            `("(begin " ,@xs ")") ;
    ) ) ] ) ;ign spc between
    (read p)
) )
;'((^)(* / %)(+ -))
(defn read-math-expr xs
  (let
    ([p (open-input-string
          (redu~ strcat
            `("'(" ,@xs ")") ) ) ])
    (read p)
) )
(alias readexp read-expr)
(def (evs . xs) [ev (redu readexp xs)])

(defn chars-replace-x (cs x xx)
  (defn _ (cs x xx ret)
    (if (nilp cs) ret
      (letn (
          [a (car cs)]
          [b (eq a x)] )
        (_ (cdr cs) x xx ([if b append conz] ret [if b xx a]))
  ) ) )
  (_ cs x xx nil)
)

(defn string-replace (s a b) ;
  (list->string (chars-replace-x (string->list s) a (string->list b)))
)

;'((1 * 2 + 3 * 4) - 5) => 
;(_ '((1 * 2 + 3 * 4) - 5)) => '(((1 * 2) + (3 * 4)) - 5)
;(defn f () nil)

;cl

(ali atom atom?)
(ali null null?)
(ali second cadr)

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
      (if (nilp i) (if *will-ret* x nil)
        (set-xth! x i a)
) ) ) )

(defn getf* (xs xtag) ;`(:n ,n :x ,x)
  (if (<(len xs)2) nil
    (if (eq (1st xs) xtag)
      (2nd xs)
      [getf* (cddr xs) xtag]
) ) )

(def (get-as-arr xs . iz) ;[_ '((1 2)(3 4)) 0 0]
  (def (_ xs iz)
    (if (nilp iz) xs
      (if (atomp xs) nil ;<-consp
        [_ (xth xs (car iz)) (cdr iz)] ;
  ) ) )
  (_ xs iz)
)
(alias aref list-ref) ;

;oth
(alias op-inp-str open-input-string)

(defn char->string(x) (list->string(li x)))

(def (str-explode s)
  (map char->string(string->list s))
)
(ali str->ss str-explode)


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

(ali ref list-ref)
(def (xth xs i) ;%
  (if (nilp xs) nil ;
    (if (< i 0) nil
      (list-ref xs i) ;use len wil be slow
) ) )
(def (nth xs n) (xth xs (1- n)))

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

(def car-atomp (compose atomp car))

;pieces of the most beautiful code

(defn rev (xs)
  (def (_ xs ret)
    (if (nilp xs) ret
      (_ (cdr xs) [cons (car xs) ret])
  ) )
  (_ xs nil)
)
(ali rev! reverse!)

(defn flat (xs)
  (def (rec x ret)
    (if*
      (nilp  x) ret
      (atomp x) (cons x ret)
      (rec (car x)
        (rec (cdr x) ret)
  ) ) )
  (rec xs nil)
)

(defn deep-length (xs) ;deep-count
  (def (_ x n)
    (if* (nilp x) n
      (atomp x) (1+ n) ;
      (_ (car x)
        [_ (cdr x) n]
  ) ) )
  (_ xs 0)
)
(ali d-len deep-length) ;d-cnt
;(d-len '[((a b)c)(d e)]) ;-> 5

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

(def (bump xs fmt) ;bumpl/bumpup-lhs
  (def (_ x fmt ret)
    (if~
      (nilp fmt) ret
      (atomp fmt) (cons x ret)
      (letn ([fa(car fmt)] [ln(d-len fa)] [fd(cdr fmt)] [head(list-head x ln)] [tail(list-tail x ln)]) ;d-len
        (if (car-atomp fmt) ;car-atomp
          [_ (car x) fa [_ tail fd ret]] ;car
          (cons [_ head fa ret] [_ tail fd ret]) ;cons _ _
  ) ) ) )
  (_ xs fmt nil)
)

;
  
(def (redu-map r m xs) (redu r (map m xs))) ;syn for such-as or

(defn tru? (b)
  (if (eq *t b) *t *f)
)
(defn fal? (b)
  (if (eq *f b) *t *f)
)
(defn  neq (x y) [not(eq  x y)])
(defn !eql (x y) [not(eql x y)])

(defn tyeq (x y) ;
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

(defm (assert resl test)
  (letn ([tmp resl] [b(eql tmp test)]
      [ret(if b 'Ok 'Wrong!!)] [ss`(resl " expect " test " ---> " ,ret)] )
    (redu echo ss) ;
    (newln)
) )
(def (assert0 resl test)
  (echol
    (if (eql resl test) 'Ok
      'Wrong!!
) ) )

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
(ali >> bitwise-arithmetic-shift-right)
(ali << bitwise-arithmetic-shift-left)

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

(def/defa (distance p1 (p2 nil)) ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1
  (let* ( [l1 (len p1)]
          [p2 (if(nilp p2) (nlist% '(0) l1) p2)] )
    (if [=(len p1)(len p2)] ;
      (sqrt
        [apply + (map [lam(x y)(pow(- x y))] p2 p1)] )
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

(def_ (infix-prefix% lst) ; need a 
  (if (list? lst)
    (if (null? (cdr lst))
      (car lst)
      (list (cadr lst)
            (_ (car lst))
            (_ (cddr lst)) ) )
    lst
) )

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

(def len-1 (compose 1- len))
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
(ali permu permutation)

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

;onlisp

(def-syn [nreverse! stx]
  (syntax-case stx ()
    ([_ xs]
      [identifier? #'xs]
      #'(let ([tmp (rev xs)])
        (set! xs (li(car xs)))
        tmp
    ) )
    ([_ xs]
      #'(rev xs) )
) )

(def (group xs m)
  (let ([m (if [= 0 m]1 m)]) ;
    (def (_ ret xs)
      (if (nilp xs) ret
        (let ([a(list-head xs m)] [d(list-tail xs m)]) ;
          [_ (cons a ret) d]
    ) ) )
    (rev (_ nil xs))
) )

(def (arb-group xs . ns) ;arbitrarily
  (def (_ xs n ms tmp ret)
    (if (nilp xs) (cons [rev tmp] ret)
      (if (nilp ms)
        (if (=0 n)
          (cons [rev tmp] ret)
          [_ (cdr xs) (1- n) nil (cons(car xs)tmp) ret] )
        (if (=0 n)
          [_ xs (car ms) (cdr ms) nil (cons tmp ret)]
          [_ (cdr xs) (1- n) ms (cons(car xs)tmp) ret]
  ) ) ) )
  [rev(_ xs (car ns) (cdr ns) nil nil)]
)

(defn prune (g xs) ;rec remov-if satisfy g ;!keep
  (def (_ xs ret)
    (if [nilp xs] (rev ret)
      (let ([a (car xs)][d (cdr xs)])
        (if [consp a] ;
          (_ d (cons [_ a nil] ret))
          (_ d [? (g a) ret (cons a ret)]) ;
  ) ) ) )
  (_ xs nil)
)

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

(def +.ori +) ;+.0
(def (my+ . xs) ;(my+ '(1 () 2))
  (redu~ +.ori [flat xs]) ;todo: try / sum-of-list
)
;(dmap [lam(x)(if[nilp x]0 x)] xs)
;(def + my+) ;to test (fib0 38) ;need to be restored bef reload this script ;10x slow

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

(def (mat-unitlen m) [len(car m)])

(def (mat-unit n)
  (def (once ret m i)
    (def (_ ret m)
      (if (< m 1) ret        
        [_ (cons 0 ret) (1- m)]
    ) )
    [_ [cons 1 (xn2lis 0 i)] m]
  )
  (def (_ ret i m)
    (if [< m 0] ret
      [_ (cons(once nil m i)ret) (1+ i) (1- m)]
  ) )
  (_ nil 0 (1- n))
)

(def (mat-unitof m) [mat-unit(mat-unitlen m)])

(def (mat-pow m n)
  (fast-expt-algo m n mat-mul (mat-unitof m)) ;(fast-expt-algo m n mat-mul '[(1 0)(0 1)])
)

(define (fib0 n)
  (define (_ n) ;
    (if (< n 3) 1
      (+ [_ (fx- n 2)] [_ (fx- n 1)])
  ) )
  (if (< n 0) 0
    (_ n)
) )
;(time (fib0 38)) ;realtime = 0.170~1.403 s ;adm tool ;i don't why chez-lib is slow

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
;(elapse(fac 50000)) ;=> elapse = 1.559~1.563 s

(defn round% (x)
  (let ([f (floor x)])
    (if (>=(- x f)1/2) (1+ f)
      f
) ) )
(def/defa (myround@ fl (nFlt 0)) ;@
  (let ([fac (pow 10 nFlt)])
    (inexact (/ [round% (* fl fac)] fac)) ;
) )

;txt->excel->chart
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
;(setq abc (math:points->parabola 1 127  153 10  253 1)) ;-> '[a b c]
(defn y=ax2+bx+c (a b c x)
  (+ [* a (pow x)] [* b x] c)
)

;(for (x 128) (echol [floor->fix(redu y=ax2+bx+c [conz abc x])]))
;(for (x 128) (print-to-file "1.txt" [floor->fix(redu y=ax2+bx+c [conz abc x])]))
#|
(setq abc (math:points->parabola 1 127  127 11  253 1)) ;其实可以检查abc给用户提示
(clean-file "1.txt")
(setq resl (map [lam[x](str(floor->fix(redu y=ax2+bx+c [conz abc x])))] (range 256)))
(setq ss (redu (curry str/sep " ") resl))
[print-to-file "1.txt" ss]
[sys "npp 1.txt"]
|#
;(map [lam[x](floor->fix(redu y=ax2+bx+c [conz abc x]))] (range 12))
;(sys (str "cd.>" "1.txt")) ;cre-new-file 1.txt
;(sys (str "echo " "a" ">>1.txt")) ;print-to-file


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
(defn mat2lis (mat) ;matrix->list: matrix1
  (flat mat)
)
;?matlen submat
(def (dotmul da db) ;(1,2,3)*(4,5,6) ;dot-multiply: point1 point2
  (redu~ + (map * da db)) ;
)
(defn convolution1 (m1 m2) ;convolution: matrix1 matrix2
  (redu~ dotmul (map mat2lis (li m1 m2)))
)

;middle-function
(def (mat-1Muln m1 mn) ;'(1 2 3) '((4 7)(5 8)(6 9))
  (def (_ mn)
    (if [nilp (car mn)] nil
      (cons [dotmul m1 (map car mn)] [_ (map cdr mn)]) ;todo
  ) )
  [_ mn]
)

(def (mat-nMuln ma mb) ;mul-2-matrixes
  (def (_ ma)
    (if (nilp ma) nil
      (cons [mat-1Muln (car ma) mb] [_ (cdr ma)]) ;
  ) )
  [_ ma]
)

(def (mat-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-nMuln (car mts) (cdr mts))
)

;AI

(def ReLU (curry max 0))
(alias relu ReLU)

(defn sigmoid (x)
  (/ (1+ [exp(- x)]))
)
(defn swish (x)
  (* x (sigmoid x))
)

(def/defa (nonlin x (deriv Fal)) ;
  (if (eql deriv Tru)
    (* x [- 1 x])
    (sigmoid x)
) )

; file: load-file-cont-as-str

(def (save-file cont file)
  (if (file-exists? file) (delete-file file)) ;
  (let ([of (open-output-file file)])    
    (write cont of)
    (close-port of)
) )

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

;theory

; (def (rev~ xs) ;rev!% syn 
  ; (reverse! xs)
; )

(def (mk-cps g) ;cps相当于做了堆栈交换?
  (lam args
    (let ([r (rev args)])
      ( (car r)
        (redu g
          (rev (cdr r))
) ) ) ) )

; ((lambda (x) (list x (list 'quote x)))
  ; '(lambda (x) (list x (list 'quote x)))))
; ((lam (g) (li g (li 'quo g)))
  ; '(lam (g) (li g (li 'quo g)))))
; ((lam (g) (li g `(',g))) '(lam (g) (li g `(',g)))))
; ((lam (g) `(,g (',g))) '(lam (g) `(,g (',g)))))
; ((lam (g) `(,g '(,g))) '(lam (g) `(,g '(,g)))))

; ((lam (g) `(,g ',g)) '(lam (g) `(,g ',g))))
     
(def (quine-f g) `(,g ',g)) ;[_ '_] `,_ ' ;(quine 'quine) (ev(quine 'quine)) (eql (quine 'quine) (ev(quine 'quine)))
(defm (quine g) `(,'g ,'g))

(def/defa (ev-n x [m 1])
  (def (_ x n)
    (if~ (> n m) x
      ; (let ([ret (ev x)])
        ; (if~ (eql x ret) x ;?
      [_ (ev x) (1+ n)]
  ) ) ;) )
  (_ x 1)
)

(ali bad-cond? condition?)
(def (full-eval x) ;
  (def (_ x)
    (let ([ret (try(ev x))])
      (if~ (bad-cond? ret) x
        (eql x ret) x
        [_ ret]
  ) ) )
  (_ x)
)
(ali ev-full full-eval)

; (defsyn lam-snest
  ; ([x] nil)
; )

;;church-number: https://www.zhihu.com/question/39930042 https://www.jianshu.com/p/73f80c379860

(defn nex-prime (p)
  (prime p 2) ;
)
(ali inc 1+) ;for church's f, use 1+ is not rooty

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

(alias float inexact)

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

; (defn dmap% (g xs)
  ; (def (_ xs ret)
    ; (if (nilp xs) [rev ret]
      ; (let ([a (car xs)][d (cdr xs)])
        ; (if (consp a)
          ; (_ d (cons (_ a nil) ret))
          ; (_ d [cons (g a) ret])
  ; ) ) ) )
  ; (_ xs nil)
; )

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

;vec: mk-vec n; vec-fill!; vec-set! v i x; 

(def-syn (ve-push* stx)
  (syn-case stx () ;
    ([_ args ... x]
      (identifier? #'x) ;
      #'[setq x (ve-cons* args ... x)] ) ;mk-vec will slower than list's
    ([_ . args]
      #'(ve-cons* . args)
) ) )

(def (vec-nilp x) ;
  (if [vecp x]
    (=0 (veclen x))
    Fal
) )
(alias vnilp vec-nilp)

(def num->lis (curry apply/reducing-num cons))

(def vnil (vec))
(def (vec-car v) (vec-ref v 0))
(def (vecadr v) (vec-ref v 1))

(def (vec-consp v) (and (vecp v) [>0(veclen v)]))

(defn num->vec (n)   ;vec-flat ;@(lis->vec (range n))
  (let ([ve (mk-vec n)])
    (for (i n)
      (vec-set! ve i i) )
    ve
) )

(def (ve-last ve)
  (vec-ref ve [1- (veclen ve)])
)

(defn vec-cons (x vy) ;* . xxv
  (if (vecp vy)
    (let ([ve (mk-vec [1+ (veclen vy)])])
      (vec-set! ve 0 x)
      (vec-copy! ve 1 vy)
      ve
    )
    nil ;
) )
(def [ve-cons* . xxv]
  (letn ([vy (last xxv)][n (len xxv)][m (1- n)])
    (if (vecp vy)
      (let ([ve (mk-vec [+ m (veclen vy)])])
        (vec-copy! ve 0 (lis->vec [ncdr xxv -1])) ;->lis flat
        (vec-copy! ve m vy)
        ve )
      nil
) ) )
(alias vecons vec-cons)

(defn vec-conz (vx y)
  (if (vecp vx)
    (letn ([n (veclen vx)][ve (mk-vec [1+ n])])
      (vec-copy! ve 0 vx)
      (vec-set! ve n y)
      ve
    )
    nil ;
) )
(alias veconz vec-conz)

(alias vec-copy vector-copy)
(alias mk-vec make-vector)
(alias vec-len vector-length)
(alias vec-set-fnum! vector-set-fixnum!)
(alias vec-set! vector-set-fixnum!)
(alias vecar vec-car)

(def (vec-head ve n) ;
  (letn ([ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve i]) )
    ret
) )

(def (vec-tail ve m)
  (letn ([n [-(vec-len ve)m]][ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve [+ m i]]) )
    ret
) )
(def vec-cdr (rcurry vec-tail  1))
(alias vecdr vec-cdr)

(defn vec-dmap (g xs) ;
  (def [_ xs]
    (if [vec-nilp xs] vnil
      (let ([a (vecar xs)][d (vecdr xs)]) ;
        (if (vec-consp a) ;
          [vecons [_ a] [_ d]] ;flat & bump/hunch
          [vecons (g a) [_ d]]
  ) ) ) )
  [_ xs]
)

(def (vec-foldl g x ve)
  (vec-for y in ve
    [set! x (g x y)] ) ;
  x
)

(def (vec-redu g ve)
  (vec-foldl g (vec-car ve) (vecdr ve)) ;
)

(def (vec-swap! ve i j) ;!
  (let ([t 0])
    (set! t (vec-ref ve i))
    (vec-set-fnum! ve i (vec-ref ve j))
    (vec-set-fnum! ve j t)
) )

(def (vec-rev! ve)
  (letn ([n (veclen ve)] [m (1- n)] [h (quot n 2)])
    (for (i h)
      (vec-swap! ve i [- m i])
) ) )

(def vec-copy! ;
  (case-lam
    [(ve) (vec-copy ve)]
    [(des i) (vec-tail des i)]    
    [(des i src)
      [vec-copy! des i src (veclen src)] ] ;
    [(des i src n)
      (letn ([dn (veclen des)][m (min n [- dn i])])
        (for (j m)
          (vec-set! des (+ i j) (vec-ref src j)) ) ) ]
) )

(def (vec-append . vz)
  (letn ([n (len vz)][ns (map veclen vz)][ret (mk-vec [redu + ns])])
    (for (i n)
      (vec-copy! ret (redu + [list-head ns i]) (xth vz i)) )
    ret
) )



;algo for vec-sort

;sort

(def (car->end xs)
  (set-cdr! (last-pair xs) (li(car xs))) ;
  (set-car! xs (cadr xs)) ;
  (set-cdr! xs (cddr xs))
  xs
)

(def/defa (qsort xs [f >]) (sort f xs))

(define (merge-sort ls lt?) ;2x slower than sort
  (define merge~
    (lambda (ls1 ls2)
      (if (null? ls1)
          ls2
          (if (null? ls2)
              ls1
              (if [lt? (car ls1) (car ls2)]
                  (cons (car ls1) [merge~ (cdr ls1) ls2]) ;
                  (cons (car ls2) [merge~ ls1 (cdr ls2)]) ) ) ) ) )
  (define (_ ls n)
    (if (fx< n 2)
      ls
      (let ([mid (quotient n 2)])
        (merge~
          [_ (list-head ls mid) mid]
          [_ (list-tail ls mid) (fx- n mid)]
  ) ) ) )
  (_ ls (length ls))
)

(defn isort% (xs g) ;(2~)266x slower than sort ;onlisp Page.201 chapter.22 非确定性排序(?)非常快
  (def (_ pre x ys pos) ;ys pre pos x
    (if (nilp ys)        
      (if (nilp pos)
        (cons x pre)
        [_ pre x pos nil] ) ;
      (if (g x (car ys))
        (if (nilp pre)
          [_ nil (car ys) (cdr ys) (cons x pos)]
          [_ (cdr pre) (car pre) ys (cons x pos)] ;list-ref/head/tail car->end?
        )
        [_ (cons x pre) (car ys) (cdr ys) pos]
  ) ) )
  (if (nilp xs) nil
    (_ nil (car xs) (cdr xs) nil)
) )
(defn isort (xs g) ;(1.5~)350X slower than sort ;try to use vec ;?(lam(l r)[odd?(+ l r)])
  (def (_ xs ret)
    (cond
      [(nilp xs) ret]
      [else
        (letn ( [a  (car xs)]
                [lr  (filter2 (lam(~)(g ~ a)) [cdr xs])] ;[_ (range n) >] is slow ;(rcurry g a)
                [pre (car lr)]
                [pos (cadr lr)] )
          [_ pre (cons a [_ pos ret])] ;
  ) ] ) )
  (_ xs nil)
)

;
(def (randnums n) ;(random-seed elapse)
  (def (_ m)
    (if (< m 1) nil
      (cons (random n) [_ (1- m)]) ;
  ) )
  (_ n)
)

;exercise
(defsyn try
  ([_ exp]
    (guard (x (els x)) exp) ;(condition? #condition) -> *t
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

(defn call-nest (g . xs)
  (defn ~ (g xs)
    (if (nilp xs) (g)
      (~ (g (car xs)) (cdr xs))
  ) )
  (~ g xs)
)
(alias callnest call-nest)

(defn call-snest (g . ys)
  (defn ~ (g ys)
    (if (nilp ys) g
      [~ (g (car ys)) (cdr ys)]
  ) )
  (~ g ys)
)
(alias callsnest call-snest)

;ffi

(alias load-lib load-shared-object)
(alias ffi? foreign-entry?) ;
(alias ffi foreign-procedure)

;CFName nArgs tyRet fname? ;(defc Beep (void* void*) bool [beep]) ;(api: Beep 2 bool [])? ;(fname-sym CFName)
;(_ fname (var1 var2) ret FName (void* void*))
;(_ bool Beep (freq=1047 dura))

(defsyn defc*
  ( [_ f]
    (defc* f (void)) ) ;
  ( [_ f args]
    (defc* f args void*) ) ;
  ( [_ f args ret] ;defa
    (defc* f args ret f) ) ;
  ( [_ api args ret f] ;f is case-sensitive ;how many args ;void* is ok too ;no ret is ok too ;
    (def f (ffi (sym->str 'api) args ret)) ) ;outer-proc ;todo f?
  ( [_ api args ret f rems]
    (defc* api args ret f) )
)

(defsyn defc
  ( [_ ret f args]
    (def f (ffi (sym->str 'f) args ret)) )
  ( [_ fnam ret api args] ;
    (def fnam (ffi (sym->str 'api) args ret)) )
  ( [_ fnam rems ret api args]
    (defc fnam ret api args) )
)

;
(load-lib "kernel32.dll") ;Beep
(defc* GetCommandLineA () string get-command-line)
(defc beep (freq dura) void* Beep (void* void*))
(defc c-sleep (ms) void* Sleep (void*)) ;(defc c-sleep Sleep 1) ;(ms)
(alias sleep c-sleep)

(load-lib "msvcrt.dll")
(defc void* clock ())

(load-lib "winmm.dll")
(defc midi-out-get-num-devs() int midiOutGetNumDevs()) ;
(ali numofMidiOut midi-out-get-num-devs)

;(def (main-args) (str-split (GetCommandLineA) spc))

(def CLOCKS_PER_SEC 1000)
(def (clock*)
  (inexact (/ (clock) CLOCKS_PER_SEC)) ;
)

(defsyn cost
  ( [_ g]
    (let ([t 0] [res nil])
      (echol ":" 'g)
      (set! t (clock))
      (set! res g)
      (setq t [./ (-(clock)t) CLOCKS_PER_SEC])
      (echol ": elapse =" t "s")
      (li res t)
) ) )
(defsyn elapse ;just elapse but result
  ( [_ g]
    (let ([t 0])
      (echol ":" 'g)
      (set! t (clock))
      g
      (setq t [./ (-(clock)t) CLOCKS_PER_SEC])
      (echol ": elapse =" t "s")
      t
) ) )

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

(def cps ;cont-pass-style
  (lam (exp)
    (letrec ;recurse
      ( [trivial? (lam (x) ;
            (memq x '(zero? add1 sub1)) )] ;member-quo?
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

;

;num2lis num2abc abc2num

(def (repeats xs n) ;ng
  (redu (curry map li) (xn2lis xs n))
) ;仍然漏了部分重复的情况



;unify -- onlisp?

(def_ (contain. e m)
  (if*
    (nilp e) *f
    (atom e) (if(eql e m)*t *f)
    (if*
      [_(car e)m] *t		
      [_(cdr e)m] *t
      else   *f
) ) )
(def_ (sb. e s1) ;exp syms?
  (if* [nilp e] nil
    [atom e] (if[eql e (2nd s1)] (1st s1) e) ;
    (let [(head[_ (car e) s1]) (tail[_ (cdr e) s1])]
      (cons head tail)
) ) )
(def_ (substitution. e m)	;置换 exp marks?
  (if* (nilp m) e
    (bgn
      (set! e [sb. e (car m)]) ;
      [_ e (cdr m)]
) ) )
(defun compose. (s1 s2)
  (def (_cp1 s1 s2)
    (if* (nilp s1) nil        
      (letn ([ti(caar s1)] [vi(cdar s1)] [new_ti(substitution. ti s2)])
        (cons (cons new_ti vi) [_cp1 (cdr s1) s2])
  ) ) )
  (append (_cp1 s1 s2) s2)
)
(def (unify e1 e2 syms) ;(unify '(a b) '(x y) '[x y])
  (def (_ e1 e2)
    (let ([bf 0][f1 0][f2 0][t1 0][t2 0][s1 0][s2 0][g1 0][g2 0]) ;
      (cond
        ( [or(atom e1)(atom e2)]
          (when [not(atom e1)] (setq  bf e1  e1 e2  e2 bf)) ;
          (cond
            ((equal e1 e2)                         '()) ;
            ([and (mem? e1 syms) (contain. e2 e1)] 'fail) ;
            ((mem? e1 syms)                        `[,(li e2 e1)])
            ((mem? e2 syms)                        `[,(li e1 e2)])
            (else                                  'fail)
        ) )
        (else
          (setq
            f1 (car e1)   t1 (cdr e1)
            f2 (car e2)   t2 (cdr e2)
            s1 [_ f1 f2] )
          (cond ([eq s1 'fail] 'fail)
            (else
              (setq g1 (substitution. t1 s1))
              (setq g2 (substitution. t2 s1))
              (setq s2 [_ g1 g2])
              (if [eq s2 'fail] 'fail (compose. s1 s2))
  ) ) ) ) ) )
  (_ e1 e2)
) ;type infer

;(unify '(p a b) '(p x y) '[x y]) ;~> ((A X) (B Y))
;(unify '[x(f x)(g z)] '[y (f(g b)) y] '(x y z))
;(unify `(a b) `(b X) '(X)) ;?-> fail


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

; (def car car%) ;
; (def cdr cdr%)
; (def cadr (compose car cdr))
; (def cddr (compose cdr cdr))
;cddddr


(set! *script-path* ;%
  (car(string->path-file ;
      (car(remove ""
          (string-divide
            (cadr(remove ""
                (string-divide (get-command-line) " ") ) )
            "\""
  ) ) ) ) ) ;bug if just use load
)

(define (load-relatived file)
  (load (string-append *script-path* [(if (sym? file) symbol->string id) file]))
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ali clean restore)
(def (restore)
  (setq nil nil
    ; car car.ori
    ; cdr cdr.ori
    ; map map.ori
    ;+   +.ori
) )