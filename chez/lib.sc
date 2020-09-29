(define (version) "Chez-lib V1.92a")

#|
# Chez-lib.sc - Written by Faiz

  - Update notes:
    - 1.92a change format of notes
    - 1.92: update api-with: symbol -> macro
    - 1.91: add logic for dividing vowels in japanese; add T, F;
    - 1.90: Add data of jp, doremi
    - 1.89: syn -> syt
    - 1.88: divide-at

  - Suffixes:
    - @ slow / bad
    - % theoretic / internal / paras->list
    - ~ just faster
    - * optimized
    - ! with side-effect

  - prefixes:
    - sy/ syt/ for syntax
    - ~ returns a reverse result

  - vars:
    - ~var: temp variety
    - *global-var*

  - versions:
    - idea; ideal; refined; stable;
    - ; fast; Grace; safe; trial; refined; stable;

  - Which ops are slow?:
    - last-pair last list?
    - length
    - append->conz->rpush ... slowest
    - ? eval->reduce->compose/curry
    - strcat
    - remove
    - lis->vec vec->lis
  - fast>:
    - consp -> atomp, nilp, lisp, eq
    - sort, .., cond if, .., redu, map, .., append;
    - syntax, func
    - def_ set!~def alias
    - cons vector list
  - not the fastest achievement:
    - reverse append! list-copy
  - ?
    - apply let
    - eq =, eql

  - tofix:
    - (range 0 31270 529) is opposite
  - todo:
    - ls
    - api?
    - (deep-action/map/apply g xs [seq]): d-remov
    - to compatibale with linux
    - include
    - end->car
    - control[include convert]: strings, files, ...
    - ~(!= 1 2 1), (> 3 2 1), (coprime? 2 15 4)
    - (part-of-num 123456 -3 2)~> 45
    - see to: verb.adj.a./act, prep./judge,
    - lam/defa lam_ lam/ret
    - [random-seed (floor->fix(w* (elapse(fib 500000))))] ;too closed ;~> parallel universe id bytes, not work well
      - time.ms->md5->cost.ns?
      - . time activities info net:salt io? file:psw/md5
    - (nthof-g-resl rand '(3 1 4) [max-n 10000000])
    - (nthof-g rand nth [len 1])
    - d-rev
    - grep grep-rn
    - reload? load compile udp/tcp get/post v3 juce ui test trace
    - if(!#f/nil): cadr caddr cadddr eval, repl
    - cond case, for map lambda foldl reduce curry recursion repl foldr
    - (range% sum f p n)
    - ? (str/sep sep . xs)
      - -> echo
      - => any->int
    - (_ xs . x) (-> -> x)
    - code:dsl->raw
    - api-search 可以下载个网页,然后用正则搜索; 每次defn时,记录信息到hashtable
      - 用法直接searching in lib-files就可以了
    - church yc algo
    - structure:
      - skip-list/max-skip-step/for-spec-type/with-logic, path
        - ?`[(4) ([(1 a) 2 3] [4 5 6])]
      - b+tree
    - AI:
    - math memo combinations, eval. match
    - solve24 https usd/usdt pcre
    - def/setq-glob
    - car! (cons 1 2 '()) cons! conz!
    - rev!
    - seems that newlisp call scheme and c will be more free.

  - cant/hard: get-addr
  - cant implete the same thing:
    - apply call/cc?

  - seq of implements:
    - (g x y)~> apply~= reduce-> curry

  - tolearn:
    - duck-compiler:match
    - import
    - fork-thread
    - profile
    - eg: chez/examples/matrix.ss
    - my: let + redu sort! rand eval
    - hygienic assq memq define-structure
    - >: [syntax-case see to ;push] defsyt def
    - ;define-syntax syntax-rules syntax->datum=datum
    - datum->syntax=syntax=#' with-syntax with-implicit syntax-case #, fluid-let-syntax ...
    - (let ([ret ..]) (ev `(setq x ',ret))
    - un/trace debug
    - list: -tail/head/ref
    - apis: #%$xxx
    - (trace funxxx) (funxxx ...) can show is it a tail form rec
    - hash when def/setq/defsyt ~> api-search
    - vec: cons lam/vec def/vec, map for redu, add! del/rm! flat strcat
    - sy: rev, vec? flat append? group
    - sort: qsort heap merge
    - abs(fxnum) <= 2^29-1 (> 5E)
    - (eval-when (compile) (optimize-level 3))
  - learned
    - body... != body ...
    - let-values(<->)
    - def-syt doesnt supp recursion directly, but case
    - def-syt cant be in ano def-syn

  - beauties:
    - reverse flat deep-count bump

  - to-be-beauty:
    - curry compose

  - to-try
    - walker

  - to-optimize:
    - . xs -> xs
    - 1/2 -> 0.5
    - def-syn
    - def f g -> alias f g
    - nilp (cdr xs)
    - [] -> ()
    - (small .. big) -> (big .. small)
    - ?: setq
    - 听说cond要按发生概率高低来排序
    - def/va: case-lambda needs 1~2X time more than original lambda

  - to-debug:
    - (trace fib)?, assert&print, debug?, call/cc+assert+return.false ...

  - flow: work->fast->safe->complete
    - ;must-inits
    - ; main-apis
    - ;apis-for-main
    - ; apps-api
    - ;endups
    - ; test

  - common:
    - (_ X x)
    - syt -> '
    - common/special... - :
```
|#

(import (chezscheme)) ;for --program parameter
;(collect-request-handler void) ;~ for some optimizing

;(load (str *lib-path* "/match.ss"))

;#%car = ($primitive car) = ($primitive 1 car) = car
;#%car = ($primitive car) = ($primitive 1 car) = car

(alias ali      alias)
(alias imp      import)
(alias lam      lambda)
(alias letn     let*)
(alias bgn      begin)
(alias quo      quote)
(alias def-syt  define-syntax)
(ali   def-syn  define-syntax)
(alias syt-ruls syntax-rules)
(ali   syn-ruls syntax-rules)
(alias syt-case syntax-case)
(ali   syn-case syntax-case)
(alias case-lam case-lambda)
(alias els      else)
(alias fn       lambda)
(alias progn    begin)
(alias vec      vector)
(alias vecp     vector?)
(alias vec-ref  vector-ref)
(alias vec->lis vector->list)
(alias lis->vec list->vector)
(alias vec-len  vector-length)

(def-syt def ;ine*
  (syt-ruls ()
    ([_ x] (def x *v))
    ([_ (g . args) body ...]
      (define (g . args) body ...) )
    ([_ x e] (define x e)) ;sym? e: e *v
    ; ;The followings make def slow:
    ; ([_ g (args ...) body ...]
      ; (define (g args ...) body ...) ) ;
    ; ([_ g args body ...] ;
      ; (define (g . args) body ...) )
) )

(def-syt defm ;define-macro <- define-syntax ;to-add (void)
  (syt-ruls ()
    ( [_ (f . args) body ...]
      (defsyt f
        ( [_ . args]
          (bgn body ...)
    ) ) )
    ( [_ f (args ...) body ...]
      (defm (f args ...) body ...)
) ) )

(alias nilp  null?)
(alias first car)
(alias rest  cdr)
(alias eq    eq?)
(alias equal equal?)
(alias eql   equal?)
(alias ==    equal?)
(alias ?: if)
(alias ?  if)
(alias !  not)
(alias sym?   symbol?)
(alias bool?  boolean?)
(alias int?   integer?)
(alias num?   number?)
(alias str?   string?)
(alias lisp   list?)
(alias consp  pair?)
(alias pairp  pair?)
(alias fn?    procedure?)
(alias voidp  void?) ;voip
(alias atomp  atom?) ;atop
(alias nump   number?)
(alias exa->inexa exact->inexact)
(alias inexa->exa inexact->exact)
(alias sym->str symbol->string)
(alias ev     eval)
(alias reduce apply) ;
(alias redu   apply) ;
(alias strcat string-append)
(alias foldl  fold-left) ;
(alias foldr  fold-right)
(alias mod remainder) ;
(alias %   mod) ;
(alias ceil ceiling)
(alias identities values)
(alias repl new-cafe)
(alias fmt format)
(alias exec command-result) ;
(alias sys system)
;(def (sys cmd) (zero? (system cmd)))
(alias q exit)
(alias str-append string-append)
(alias len length)
(alias newln newline)
(alias nil?  null?)

(ali 1st car)
(ali 2nd cadr)
(ali 3rd caddr)
(ali elap elapse)
(ali origin $primitive)

(alias head list-head) ;.
(alias redu~ redu~/fold) ;. (redu~ list '(1 2 3))
(alias strhead! string-truncate!) ;
; To put aliases here

;

(def-syt defsyt
  (syt-ruls ()
    ( [_ f (expr body ...)] ;;;one ;must be bef (_ f g), or will make wrong meanings
      (def-syt f
        (syt-ruls ()
          (expr
            (bgn body ...) ) ) ) ) ;
    ( [_ f g]
      (def-syt f
        (syt-ruls ()
          ( [_ . args] ;
            (g . args) ) ) ) )
    ( [_ f (expr ...) ...]   ;multiple
      (def-syt f
        (syt-ruls ()
          ( expr
            ...
          )
          ...
) ) ) ) )
(ali def-syn def-syt)
(ali defsyn defsyt)

(def-syt (if% stx)
  (syt-case stx (else)
    ([_ () (bd ...)]
    #'(cond bd ...) )
    ([_ (last-expr) (bd ...)]
    #'(if% () (bd ... [else last-expr])) )
    ([_ (k e more ...) (bd ...)]
    #'(if% (more ...) (bd ... [k e])) )
) )
(def-syt (if* stx)
  (syt-case stx ()
    ([_ bd ...]
      #'(if% [bd ...] []) ;
      ;#'[sy-redu cond (group (bd ...) 2)] ;sy-group
) ) )
(alias if~ if*)

; (def-syt (if* stx) ;? ?: cond->if
  ; (syt-case stx (else) ;nil?
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

(defsyt defun
  ( [_ f (args ...) ]
    (define (f args ...) *v) )
  ( [_ f args ]
    (define (f . args) *v) ) ;

  ( [_ f args ...]
    (define f (lam args ...)) )
)
(ali defn defun)
(alias call/k call/cc)
(ali mem? member)

(defsyt defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( [_ f args body ...]
    (define f
      (eval ;
        (foldr
          (lam (a b) [append~ a (li b)])
          `(lam () body ...)
          (map [lam (x) `(lam (,x))] 'args) ;
) ) ) ) )
(defsyt defn-snest ;(lam(a)(lam(b) body...))
  ( [_ f args body ...]
    (define f
      (eval
        (foldr
          [lam (a b) (append a (list b))]
          `(bgn body ...)
          (map [lam (x) `(lam (,x) )] 'args) ;
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
;(alias def_ def/_)

(defsyt defn_
  ( [_$% f args bd...] ;
    (def_ (f . args) bd...)
) )

(defsyt setq
  [(_ a) (set! a (void))]
  ((_ a b)
    (bgn (set! a b) (if *will-ret* a))
  )
  ((_ a b c ...)
    (bgn
      (set! a b)
      (setq c ...) ;
) ) )

;

(def-syt (append!% stx) ;
  (syt-case stx ()
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


(defsyt cacc ;
  ([_ (k) bd ...]
    (call/cc [lam (k) bd ...])
) )
(defm (let/cc k bd ...) ;
  (call/cc (lam (k) bd ...))
)

;

(def    *f   #f)
(def    *t   #t)
(def    *v   (void))
(def    *e   '[(err)]) ;
(def    nil  '()) ;
(def    T    #t)
(def    F    #f)
(def    No   *f)
(def    Yes  *t)
(def    spc  " ")
(def    Void *v)
(def    Err  *v) ;
(define Tru  *t)
(define Fal  *f)

(def void? (curry eq *v))
(def (str/pair? x) [or(string? x)(pair? x)]) ;x
(def (str/pair/vec? x) [or(string? x)(pair? x)(vector? x)]) ;for eql/eq

(def (id x) x)
(alias identity id)
(alias li list)
(ali str->list string->list)

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
        (display (car xs)) ;write/pretty-print/display/?
        [_ (cdr xs)]
  ) ) )
  ;(if *will-disp*
    (_ xs)
) ;)
(alias disp display*)

(def (ok? x)
  (if [or (nilp x) (fal? x)] Fal
    Tru
) )

(def [please-return!] (setq *will-ret* Tru))
(def [dont-return!]   (setq *will-ret* Fal))

(def (return x)
  (if *will-ret* x
    (if (ok? x) 'OK
      'FAIL
) ) ) ;DONE->OK FAIL

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
;(alias conj conz)

(defsyt sy/num-not-defa-vals%
  ([_ () n] n)
  ([_ ((x vx)) n]       (sy/num-not-defa-vals% () n))
  ([_ (x) n]            (sy/num-not-defa-vals% () (fx1+ n)))
  ([_ ((x vx) y ...) n] (sy/num-not-defa-vals% (y ...) n))
  ([_ (x y ...) n]      (sy/num-not-defa-vals% (y ...) (fx1+ n))) ;
)
(defsyt sy/num-not-defa-vals ;good for: (_ a [b 1] c)
  ([_ . xs] (sy/num-not-defa-vals% xs 0))
)

;(_ '(a [b 2] [c])) ;-> 2
(defn num-not-defa-vals (paras)
  (def (_ paras n)
    (if (nilp paras) n
      (let ([a (car paras)][d (cdr paras)])
        (if (consp a) ;
          (if (nilp (cdr a)) ;<-atomp
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
(defsyt sy/list-the-front ;
  ( [_ ()] '())
  ( [_ ((x ...) . xs)] '((x ...) . xs))
  ( [_ (x)] (cons '(x) [sy/list-the-front ()])) ;
  ( [_ (x . xs)]
    (cons '(x) [sy/list-the-front xs]) ;
) )

; (def (defa->vals/aux paras vals nths-defa-part nths-not-defa nths-defa-rest) ;
  ; (def (_ paras vals n-head n-ndefa n-tail ret)
    ; (if (nilp paras)  ret ;
      ; (let ([ev-cadr (lam (xs) [ev(cadr xs)])])
        ; (if (nilp vals)
          ; [_ nil nil 0 0 0 [append~ (rev ret) (map ev-cadr paras)]] ;
          ; (letn ([a (car paras)] [d (cdr paras)])
            ; (if (cdr-nilp a)
              ; (cons (car vals) [_ d (cdr vals) n-head (1- n-ndefa) n-tail ret]) ;
              ; (if (<1 n-head)
                ; [_ d vals 0 n-ndefa (1- n-tail) (cons(ev[cadr a])ret)] ;
                ; (cons (car vals) [_ d (cdr vals) (1- n-head) n-ndefa n-tail ret]) ;
  ; ) ) ) ) ) ) )
  ; [_ paras vals nths-defa-part nths-not-defa nths-defa-rest nil]
; )
(def (defa->vals/aux paras vals numof-defa-vals numof-not-defa numof-defa-rest) ;@
  (def (_ paras vals n-head n-ndefa n-tail ret)
    (if (nilp paras) (rev ret)
      (let ([ev-cadr (lam (xs) [ev(cadr xs)])])
        (if (nilp vals)
          [append~ (rev ret) (map ev-cadr paras)] ;ev for eg: nil->'()
          (let ([a (car paras)] [d (cdr paras)])
            (if (cdr-nilp a) ;not-defa
              [_ d (cdr vals) n-head (1- n-ndefa) n-tail (cons (car vals) ret)]
              (if (<1 n-head) 
                [_ d vals 0 n-ndefa (1- n-tail) (cons (ev-cadr a) ret) ] ;
                [_ d (cdr vals) (1- n-head) n-ndefa n-tail (cons (car vals) ret)]
  ) ) ) ) ) ) )
  [_ paras vals numof-defa-vals numof-not-defa numof-defa-rest nil]
)
;(defa->vals/aux% '((a)(b 3)(c)) '(2 4) 0 2 1) -> '(2 3 4)

;(call-with-values (lam()(values 'a 'b vc)) g) ;
(defsyt def/defa@ ;@ (_ (g [a] [b 2] [c ]) (+ a b c)) ;test on fib0 found some issue
  ( [_ (g . paras) body ...] (def/defa@ g paras body ...))
  ( [_ g paras% body ...]
    (define (g . args) ; case-lam is good
      (let ([paras (list-elements 'paras%)])
        (define f% [ev `(lam ,(map car paras) body ...)]) ; eval is not good
        (letn ( [paras-ln (len paras)]
                [num-not-defa (num-not-defa-vals paras)]
                [vals-ln (len args)] ;args for calling ; runtime args
                [n-head (- vals-ln num-not-defa)]
                [n-tail (- paras-ln vals-ln)] ) ;(echol n-head num-not-defa n-tail)
          (redu f%
            (defa->vals/aux paras [head% args paras-ln] ;
              n-head num-not-defa n-tail
) ) ) ) ) ) )
;We may def func again with some defa paras, and test the func with just one variable para.


(defsyt defn/values%
  ([_ f (p ... q) (V ... Q) ret ...]
    (defn/values% f (p ...) (V ...)
      ret ... ([p ...] (f p ... Q))
  ) )
  ([_ f (p ...) () ret ...]
    (case-lam ret ...) ;@
) )
(defsyt defn/values
  ([_ f (p ...) [V ...] body ...]
    (def f
      [defn/values% f (p ...) [V ...] ;
        ([p ...] body ...) ]
) ) )
(defsyt def/values
  ([_ (f p ...) [V ...] body ...]
    (def f
      [defn/values% f (p ...) [V ...] ;
        ([p ...] body ...) ]
) ) )
(alias defn/defa defn/values)

#|
(def asd
  (case-lam
    ((a b c) (li a b c))
    ((a c) (asd a 2 c))
    ((c) (asd 1 2 c)) ) )

(def/va%4
  asd
  ((a 1) (s s) (d 3) (f f))
  ((a 1) (s s) (d 3) (f f))
  (a d) ;
  ()
  (a d) ;
  (((a s d f) (li a s d f)))
  ()
  () )
to-test:
  (def/va (asd a b [li li]) (li a b)) ;(asd 1 2) ;--> ok
|#
(def-syt (def/va%4 stx)
  (syt-case stx ()  
    ;_ g, Ori-pairs para-pairs; main-cnt=(A D), Ori-tmp-cnt=() tmp-cnt=(?); Ret, lamPara=[] bodyPara=[]
    ([_           g ori-pairs ([a A] ... [z Z]) main-cnt ori-tmp-cnt [C1 C2 ...] ret [  lamPara ...] (  bodyPara ...)]
      (eq #'z #'Z)
      #'(def/va%4 g ori-pairs ([a A] ...      ) main-cnt ori-tmp-cnt [C1 C2 ...] ret [z lamPara ...] (z bodyPara ...))
    )    
    ([_           g ori-pairs ([a A] ... [z Z]) main-cnt ori-tmp-cnt [C1 C2 ...] ret [  lamPara ...] (  bodyPara ...)]
                                                                           
      #'(def/va%4 g ori-pairs ([a A] ...      ) main-cnt ori-tmp-cnt [   C2 ...] ret [  lamPara ...] (Z bodyPara ...))
    )
    ([_           g ori-pairs ([a A] ... [z Z]) (A0 ...) ori-tmp-cnt [         ] (ret ...) [  tmp ...] (  rest ...)] ;
      #'(def/va%4 g ori-pairs ([a A] ...      ) (A0 ...) ori-tmp-cnt [         ] (ret ...) [z tmp ...] (z rest ...))
    )    
    ([_           g ori-pairs (               ) (A0 B0 ...) (   ) [ ] (ret ...) [tmp ...] (rest ...)]
      #'(def/va%4 g ori-pairs ori-pairs  (   B0 ...) (A0) (A0) (ret ...) [] [])
    )
    ([_           g ori-pairs (               ) (A0 B0 ...) (   ori-tmp-cnt ...) []                   (ret ...)                         [tmp ...] (rest ...)] ;tmp
      #'(def/va%4 g ori-pairs ori-pairs         (   B0 ...) (A0 ori-tmp-cnt ...) (A0 ori-tmp-cnt ...) (ret ... ([tmp ...](g rest ...))) [] [])
    )
    ([_           g ori-pairs para-pairs        [         ] ori-tmp-cnt       []       (ret ...) [tmp ...] (rest ...)]
      #'(def     g (case-lam ret ...  ([tmp ...](g rest ...))  ))
) ) )
;_ g, Ori-pairs para-pairs; main-cnt=(A D), Ori-tmp-cnt tmp-cnt=(); Ret, lamPara=[] bodyPara=[]

#|
(try3
  asd
  ((a 1) s (d 3) f)
  ((a 1) (s s) (d 3) (f f))
  [a d] ;
  (li a s d f))
|#
(defsyt def/va%3
  ([_ g ori [(a b) ...] (defas ...) body ...]
    (def/va%4
      g
      [(a b) ...]
      [(a b) ...]
      (defas ...) ;
      []
      (defas ...) ;<- []
      [([a ...] body ...)]
      [] []
) ) )

#|
(try2 asd ((a 1) s (d 3) f) ((a 1) s (d 3) f)
  () ()
  (li a s d f))
|#
(def-syt (def/va%2 stx)
  (syt-case stx ()
    ([_ g ori (x y ...) (ret ...) [defas ...] body ...]
      [identifier? #'x]
      #'(def/va%2 g ori (y ...) (ret ... [x x]) [defas ...] body ...) ) ;
    ([_ g ori (x y ...) (ret ...) [defas ...] body ...]
      #'(def/va%2 g ori (y ...) (ret ... x) [x defas ...] body ...) )
    ([_ g ori () (ret ...) [defas ...] body ...]
      #'(def/va%3 g ori (ret ...) [defas ...] body ...)
) ) )

;(def/va (asd [a 1] s [d 3] f) (li a s d f)) ;=> (asd 'A 'S 'F)

#| To test:
 (defn/va asd ([a 1] [b 2] c) (li a b c)) ;(asd 3)
 (def/va (asd [a 1] [b 2] [c 3]) (li a b c)) ;(asd)
 (defn/va asd ([a 1] [b 2] [c 3]) (li a b c)) ;(asd)
|#
(defsyt def/va
  ([_ (g p ...) body ...]
    (def/va%2 g (p ...) (p ...) () () body ...)
) )
(defsyt defn/va
  ([_ g (p ...) body ...]
    (def/va%2 g (p ...) (p ...) () () body ...)
) )
(ali def/defa def/va)
;test: (def/va (sublis xs [s 0] n) [head(tail xs s)n]) (sublis '(1 2 3) 2)

;common

(def (redu~/fold g xs) ;-> curry/compose~ ;elements of xs must be simular
  (if (nilp xs) (g)
    (foldl g (car xs) (cdr xs)) ;wrong sometimes: values map echo ;echo ~> '(*v) ;evs ;i/o
) ) ;curry?

(def-syt vec-for ;
  (syt-ruls (in)
    ( [_ i in ve body ...]
      (quiet ;
        (vector-map ;
          (lambda (i)
            body ... )
          ve )
) ) ) )

(def-syt for ;(for-each g . xz)
  (syt-ruls (in : as)
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
          (loop (fx1+ i)) )))
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
            (loop (fx1+ i)) )
    ) ) ) )
    ( [_ k (i from to) b1 ...]
      (let loop [(i from)] ;let when
        (call/cc (lam (k)
            (when (<= i to)
              b1 ...
              (loop (fx1+ i))
    ) ) ) ) )
    ( [_ k (i from to step) b1 ...]
      (let loop [(i from)]
        (call/cc (lam (k)
            (cond
              ((> step 0)
                (when (<= i to)
                  b1 ...
                  (loop (+ i step)) ))
              ((eq step 0)
                nil)
              ((< step 0)
                (when (>= i to)
                  b1 ...
                  (loop (+ i step))
    ) ) ) ) ) ) )
) )

(defsyt while
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

(def (compose . gs) ;@
  (def (_ ret gs)
    (if* ;[nilp gs] id ;nop x.id x.li
      [nilp (cdr gs)]
      (lam xs (ret [redu(car gs) xs]))
      (_
        (lam (x) (ret [(car gs) x])) ;?
        (cdr gs)
  ) ) )
  (_ id gs) ;values?
)

(def floor->fix
  (lam (flo) (flonum->fixnum(inexact flo))) )

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

(def string-divide
  (case-lam
    ([s sep] ;to supp, such as: sep="; "
      (if (eql "" sep) [str->ss s]
        (let ([chs (string->list s)] [csep (car(string->list sep))]) ;car?
          (def (rev->str chs)
            (list->string (rev chs)) )
          (def (_ chs tmp ret) ;tmp is good
            (if [nilp chs] (cons [rev->str tmp] ret)
              (let ([a (car chs)]) ;a?
                (if [eq a csep] ;eq?
                  [_ (cdr chs) nil (cons [rev->str tmp] ret)] ;
                  [_ (cdr chs) (cons a tmp) ret]
          ) ) ) )
          [rev (_ chs nil nil)]
    ) ) )
    ([s] (string-divide s " "))
) )

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
    (case (mod n 10)
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
  (let ([xz-new (remov-nil xz)])
    (_ (car xz-new) (cdr xz-new)) ;
) )

(def (append~ . xz)
  (apply append (remov-nil xz))
)


(def (rev-append xs ys) ;rev xs then append
  (def (_ xs ys)
    (if (nilp xs) ys
      [_ (cdr xs) (cons(car xs)ys)]
  ) )
  (_ xs ys)
)

; (defn conz! (xs . ys) ;->syn
  ; (set-cdr! (last-pair xs) ys)
  ; xs
; )


(def (cls) [for(42)(newln)])

;

(def *will-ret* #t)
(def *will-disp*  #t)


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

(defsyt sy-rev% ;
  ([_ () (ret ...)] '(ret ...)) ;
  ([_ (x) (ret ...)]
    '(x ret ...) )
  ([_ (x ys ...) (ret ...)]
    (sy-rev% [ys ...] [x ret ...]) )
)
(defsyt sy-rev
  ([_ (xs ...)]
    [sy-rev% (xs ...) ()] )
  ([_ xs ...]
    [sy-rev% (xs ...) ()] )
)

(defsyt lam-nest% ;(_ (a b) bd...) -> [lam(a)[lam(b) bd...]]
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    [lam(x) (lam-nest% (ys ...) [ret ...])] ) ;
)
(defsyt lam-rnest%
  ([_ () (ret ...)]
    [ret ...] )
  ([_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ([_ (x ys ...) (ret ...)]
    (lam-rnest% (ys ...) [lam(x) [ret ...]]) )
)

(defsyt lam-rnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) [lam() bd ...]] )
)
(defsyt lam-srnest
  ([_ (xs ...) bd ...]
    [lam-rnest% (xs ...) (bgn bd ...)] )
)
(defsyt lam-nest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [lam() bd ...]] )
)
(defsyt lam-snest
  ([_ (xs ...) bd ...]
    [lam-nest% (xs ...) [bgn bd ...]] )
)


(define windows?
  (case (machine-type)
    ((a6nt i3nt ta6nt ti3nt) #t)
    (else #f)
) )

(ali && and)
(ali || or)

(ali & bitwise-and)


;quo/sym-

(def (sym-redu sym-f xs) ;(quo-redu 'setq '(a 1))
  (ev (cons sym-f xs)) ;
  ;(ev `(sym-f ,@xs)) ;map-q 1st-q
)

;

(def (quiet . xs) )
(alias todo quiet)
(alias tofix id)
(alias ?~ if*)

(defn str-mapcase% (mf s)
  (list->string (map mf (string->list s))) ;
)
(alias str-upcase   string-upcase)
(alias str-downcase string-downcase)

(defn swap-para (g)
  (lam xs
    (redu g (rev xs)) ;!?
) )


; (defsyt cons~
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
            (fx1+ n)
            n )
    ) ) )
    (_ db 0)
) )

(defn nth-of-x (x db)
  (let ([g (eq/eql x)])
    (def (_ db n)
      (if (nilp db) Fal
        (if [g (car db) x] n
          (_ (cdr db) (fx1+ n))
    ) ) )
    (_ db 1)
) )
(ali nth-of nth-of-x)

; list

(def cdr-nilp [lam (x) (nilp(cdr x))])

; [duplicates '(123 321 123 321 321 1 2 3)] -> '(123 321 321 ...) -> remov-same
(def (duplicates xs)
  (def (_ xs sml ret)
    (if (nilp xs) ret
      (let ([a (car xs)] [d (cdr xs)])
        (if (mem? a sml)
          [_ d sml (cons a ret)]
          [_ d (cons a sml) ret]
  ) ) ) )
  ;[remov-same
    (_ xs nil nil)
  ;]
)

(def find-x-match
  (case-lam
    ([maker test cnt n0 nT] ;[sec 2]
      (def (_ ret n c)
        (if (> c cnt) ret
          (if (> n nT) ret ;
            (let ([x (maker n)])
              (if (test x)
                [_ (cons x ret) (1+ n) (1+ c)] ;
                [_ ret (1+ n) c]
      ) ) ) ) )
      (_ nil n0 1))
    ([maker test cnt n0](find-x-match maker test cnt n0 10000)) ;
    ([maker test cnt]   (find-x-match maker test cnt 0))        ;
    ([maker test]       (find-x-match maker test 1   0  10000))
) )
(ali find-x-meet find-x-match)

(def (flat-list-include ys0 xs0)
  (def (_ ys xs)
    (if (nilp xs) Tru
      (if (nilp ys) Fal
        (let ([dy (cdr ys)])
          (if [eq (car xs) (car ys)]
            [_ dy (cdr xs)]
            [_ dy xs0]
  ) ) ) ) )
  (_ ys0 xs0)
)
;(flat-list-include '(1 2 3 4 5) '(2 3))
(ali list-include flat-list-include)

(defn/defa assoc-g (x ys g) [id]
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

(def remov-1?
  (case-lam
    ([x xs eql] ;
      ;(def (remov-1?/g x xs g) ;result / #f
      (call/cc (lam [k]
          (def (_ xs)
            (if (nilp xs) [k Fal]
              (let ([a(car xs)] [d(cdr xs)])
                (if (eql a x) d
                  (cons a [_ d])
          ) ) ) )
          (_ xs)
    ) ) )
    ([x xs] (remov-1? x xs eql))
) )
;(ali remov-1)

(def (list-and xs ys) ;common
  (def (_ xs ys ret)
    (if*
      (nilp ys) ret
      (letn ([y(car ys)] [dy(cdr ys)] [rmp(remov-1? y xs)]) ;
        (if rmp
          [_ rmp dy (cons y ret)]
          [_ xs dy ret]
  ) ) ) )
  (_ xs ys nil)
)

(def (tail xs m) ;*
  (def (_ xs m)
    (if* (nilp xs) nil
      (< m 1) xs
      [_ (cdr xs) (1- m)]
  ) )
  (_ xs m)
)

(def (head% xs m) ;
  (def (_ xs n)
    (if* [nilp xs] nil ;
      [> n m] nil
      (cons (car xs) [_ (cdr xs) (1+ n)]) ;
  ) )
  (_ xs 1)
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
        [_ (cdr xs) (fx1+ n)]
  ) ) )
  (_ xs 1)
)
(alias list/nth list/nth-)
(defn list/-nth (xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li (car xs) n)
        [_ (cdr xs) (fx1+ n)]
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
        [(< n 1) (_ xs (fx1+ n) (cdr ys))]
        [(eq n 1) (r-merge ys xs)]
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
            [_ (cdr xs) (cdr nths)  (fx1+ n)] )
          (cons (car xs)
            [_ (cdr xs) nths  (fx1+ n)] )
  ) ) ) )
  (_ xs nths 1)
)

(defsyt set-xth!% ;chg-nth
  ( [_ xs i y]
    (letn [ (n (fx1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ]
      (set! xs (append pre (cons y pos)) ) ;
) ) )
(defsyt set-xth! ;chg-nth
  ( [_ xs i y]
    (letn [ (n (fx1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ] ;
      (set! xs (append! pre (cons y pos)) ) ;!
) ) )
(defsyt set-nth!
  ([_ xs n y] (set-xth! xs (1- n) y))
)

(defsyt insert-xth!
  ([_ xs i y]
    (letn([pre (head xs i)]
          [pos (tail xs i)])
      (setq xs (append! pre (cons y pos)))
) ) )

(defsyt swap-xths!
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
(defsyt swap-nths!
  ( (_ xs m n)
    (swap-xths! xs (1- m) (1- n)) )
  ( (_ xs m ys n)
    (swap-xths! xs (1- m) ys (1- n)) )
)


(def-syt (pop stx)
  (syt-case stx ()
    ( [_ xs]
      [identifier? #'xs]
      #'(setq xs (cdr xs)) )
    ( [_ xs]
      #'(car xs) )
) )

(def-syt (push stx)
  (syt-case stx () ;
    ([_ args ... x]
      (identifier? #'x) ;
      #'(setq x (cons* args ... x)) ) ;
    ([_ . args]
      #'(cons* . args)
) ) )

; to make return similar to bgn/values, with multiple input values

(def-syt (rpush stx)
  (syt-case stx ()
    ([_ args ... xs]
      (identifier? #'xs)
      #'(bgn
        (if [nilp xs]
          (setq xs (li args ...))
          (set-cdr! (last-pair xs) (li args ...)) ) ;
        (return xs)
    ) ) ;
    ([_ args ... xs]
      #'(if [nilp xs]
        (setq xs (li args ...)) ;
        (bgn
          (set-cdr! (last-pair xs) (li args ...)) ;let ([xs xs]) ?
          (return xs)
) ) ) ) )

;(list-replace '(#\a #\~ #\d #\x) '(#\~ #\d) '(#\1 #\2 #\3) 1)
;(list-replace '(#\a #\~ #\d #\x #\~ #\d) '(#\~ #\d) '(#\1 #\2 #\3))
(def list-replace
  (case-lam
    ([xs ori new num ==] ;
      (def (_ xs xx num tmp)
        (if (nilp xx)
          (append new [_ xs ori (1- num) nil]) ;
          (if (nilp xs) nil
            (if (eq 0 num) xs
              (let ([a(car xs)] [d(cdr xs)])
                (if (== a (car xx))
                  [_ d (cdr xx) num (cons a tmp)]
                  (rev-append (cons a tmp) [_ d xx num nil])
      ) ) ) ) ) )
      (_ xs ori num nil))
    ([xs ori new] (list-replace xs ori new -1 eql))
) )

;elap cant print ""

(def string-replace*
  (case-lam
    ([ss ori new num] ;(_ "asd~ddsa" "~d" "123" [-1])
      (list->string
        [redu (rcurry list-replace num eq)
          [map string->list (li ss ori new)] ]
    ) )
    ([ss ori new] (string-replace* ss ori new -1))
) )
(ali str-replace string-replace*)


(def (command-result cmd)
  (let-values
    ( [ (in ou er id)
        (open-process-ports cmd ;
          (buffer-mode block)
          (make-transcoder (utf-8-codec)) ) ] ;
    )
    ; (let loop ([ret ""])
      ; (if (eof-object? (peek-char ou)) ret ;\r\n?
        ; [loop (str ret (read-char ou))] ;% strcat 
    ; ) )
    (let loop ([ret nil])
      (if (eof-object? (peek-char ou))
        (str (rev ret)) ;\r\n?
        [loop (cons (read-char ou) ret)] ;% strcat 
) ) ) )


(defsyt type-main ;todo detail for printf
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

(def [bool x] (if x Tru Fal)) ;nil? 0? ;does it conflit with bool type in ffi ?

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
(alias lis2num list->num)

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
(ali xn->list xn-mk-list)

(defn nx->list (n x) ;a bit faster than make-list
  (def (_ n rest)
    (cond [(< n 1) rest]
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
     (head xs (+ (len xs) n)) ;@
    [> n 0]
     (tail xs n) ;if outofrange?
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

;rpush 1 nil

(def range% ;@
  (case-lam
    ( [n/s e f p]
      (def (_ n/s e f p res)
        (cond
          ((nilp e) (_ 0 (1- n/s) f p res))
          (else
            (let ([m (f n/s p)])
              (if ([if(> m n/s) < >] e n/s) ;
                res
                (_ m e f p (rpush n/s res)) ;
      ) ) ) ) )
      (_ n/s e f p '()) ) ;
    ([n/s e f] (range% n/s nil + 1))
    ([n/s e  ] (range% n/s nil +))
    ([n/s    ] (range% n/s nil))
) )

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

(alias atom atom?)
(alias null null?)
(alias second cadr)

(define (union x y)
  (if (pair? x)
    (if (memv (car x) y) ;
      (union (cdr x) y)
      (cons (car x) (union (cdr x) y)))
    y
) )

(define (every pred lst)
  (if (pair? lst)
    (if (pred (car lst))
      (every pred (cdr lst))
      #f)
    #t
) )

(define (some pred lst)
  (if (pair? lst)
    (or (pred (car lst))
      (some pred (cdr lst)))
    #f
) )

(defsyt getf
  ((_ xs xtag)
    (if (<(len xs)2) nil
      (if (eq (car xs) 'xtag)
        (cadr xs)
        (ev `(getf (cddr xs) xtag)) ;
) ) ) )

(defsyt getf-xth-iter
  ((_ x f1 i)
    (if (<(len x)2) nil ;
      (if (eq (car x) 'f1)
        (fx1+ i)
        (ev `(getf-xth-iter (cddr x) f1 (+ 2 i)))
) ) ) )
(defsyt getf-xth
  ((_ x f1)
    (getf-xth-iter x f1 0)
) )
(defsyt setf* ;(_ mapA tagX a)
  ((_ x f1 a)
    (letn [ (i (getf-xth x f1)) ]
      (if (nilp i) (if *will-ret* x nil)
        (set-xth! x i a)
) ) ) )

(defn getf* (xs xtag) ;`(:n ,n :x ,x)
  (if (<(len xs)2) nil
    (if (eq (car xs) xtag)
      (cadr xs)
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
(alias str->ss str-explode)


;C


(alias ref list-ref)

(def (xth xs . iths)
  ; (def (once x i)
    ; (if (atomp x) x ;< i 1 car ;cdr-nilp x car
      ; (list-ref x i)
  ; ) )
  (def (_ x iths i) ;
    (if (nilp iths) [list-ref x i]
      [_ (list-ref x i) (cdr iths) (car iths)] ;
  ) )
  (_ xs (cdr iths) (car iths)) ;
)
(def (nth xs . nths) ;raw
  (def (_ x nths i) ;
    (if (nilp nths) [list-ref x i]
      [_ (list-ref x i) (cdr nths) (1-(car nths))] ;
  ) )
  [_ xs (cdr nths) (1-(car nths))] ;
)

;lisp use quo and defsyt, instead of get-addr in c
(defsyt swap
  ( [_ a b]
    (if (eql a b)
      nil
      (let ([t a])
        (setq a b  b t)
    ) )
    (li a b)
) )

(def [car-atomp x] (atomp(car x)))

;pieces of the most beautiful code

(defn rev (xs)
  (def (_ xs ret)
    (if (nilp xs) ret
      (_ (cdr xs) [cons (car xs) ret])
  ) )
  (_ xs nil)
)
(alias rev! reverse!)

(defn flat (xs)
  (def (rec x ret)
    (if*
      (nilp  x) ret
      (atomp x) (cons x ret) ;
      (rec (car x)
        (rec (cdr x) ret) ;
  ) ) )
  (rec xs nil)
)

(defn deep-length (xs) ;deep-count
  (def (_ x n)
    (if* (nilp x) n
      (atomp x) (fx1+ n) ;
      (_ (car x)
        [_ (cdr x) n]
  ) ) )
  (_ xs 0)
)
(alias d-len deep-length) ;d-cnt
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
      (letn ([fa(car fmt)] [ln(d-len fa)] [fd(cdr fmt)] [head.(head x ln)] [tail.(tail x ln)]) ;d-len
        (if (car-atomp fmt) ;car-atomp
          [_ (car x) fa [_ tail. fd ret]] ;car
          (cons [_ head. fa ret] [_ tail. fd ret]) ;cons _ _
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
      [ret(if b 'Ok 'Wrong!!)] [ss `(resl " expect " test " ---> " ,ret)] )
    (redu echo ss) ;
    (newln)
) )
(def (assert0 resl test)
  (echol
    (if (eql resl test) 'Ok
      'Wrong!!
) ) )

; convert

(def (dec->hex dec) (fmt "0x~x" dec))
(def (hex->dec hex) (evs (str-replace hex "0" "#" 1))) ;@

; math

(def =0? (curry eq 0))
(def =1? (curry eq 1))
(def >0  (curry < 0))
(def <0  (curry > 0))
(def >1  (curry < 1))
(def <1  (curry > 1))
(def >=0 (curry <= 0))
(def <=0 (curry >= 0))
(def >=1 (curry <= 1))
(def <=1 (curry >= 1))

(alias =0 =0?)
(alias =1 =1?)
(def (not= a b) (not(= a b))) ;!==
(alias != not=)
(def [!=0 x] (not[=0 x]))
(alias >> bitwise-arithmetic-shift-right)
(alias << bitwise-arithmetic-shift-left)

(def (len0? x) (eq (len x) 0))
(alias len0 len0?)
(def [len>0  x] (>0 (len x)))
(def [len<0  x] (<0 (len x)))
(def [len>=0 x] (>=0(len x)))
(def [len<=0 x] (<=0(len x)))
(def [len1   x] (=1 (len x)))
(def [len>1  x] (>1 (len x)))
(def [len<1  x] (<1 (len x)))
(def [len>=1 x] (>=1(len x)))
(def [len<=1 x] (<=1(len x)))

(alias inexa inexact)

(def (xor . xs)
  (def (xor2% a b) ;logical ;(bitwise-xor 1 1 2 2 2 2 3 3 3)
    (if~ [eq a b] Fal
      Tru
  ) )
  (redu~ xor2% [map not xs]) ;not issue when: (xor x)
)

(def (avg . xs) (/ (redu~ + xs) (len xs)))
(def %
  (case-lam
    [(x) (inexa(/ x 100))]
    [(x . ys) (foldl mod x ys)]
) )

(def ./@ (compose exa->inexa /))
; (def (./ . nums)
  ; (exa->inexa (redu / nums))
; )
(def .* (compose exa->inexa *))

(def (pow . xs)
  (if [nilp (cdr xs)]
    (expt (car xs) 2) ;
    (fold-left expt (car xs) (cdr xs))
) )

(defn float->fix (flo) (flonum->fixnum [round flo]))

(def (not-exist-meet? g xs)
  (def (once ys x)
    (if (nilp ys) Tru ;
      (if (g x (car ys)) Fal
        [once (cdr ys) x]
  ) ) )
  (def (_ ys x)
    (if (nilp ys) Tru ;
      (if (once ys x)
        [_ (cdr ys) (car ys)]
        Fal
  ) ) )
  (_ (cdr xs) (car xs))
)
(def (!==  . xs) [not-exist-meet? =   xs])
(def (!eql . xs) [not-exist-meet? eql xs])

(def (reset-randseed)
  (random-seed (time-nanosecond (current-time)))
)

(def (pow-num? x) ;int
  (if (eq 0 [& x (1- x)]) Tru
    Fal
) )

(def (num-end-with num xx) ;int
  (letn ([xx-len (n-digits xx)] [tmp (pow 10 xx-len)])
    (eq xx (mod num tmp))
) )

(setq *max-deviation* (- [expt(sqrt 2)2] 2)) ;?
(setq *max-deviation-ratio* [-(/ (expt(sqrt 2)2) 2)1])
(def (~= a b)
  [<= (abs(-(/ a b)1)) *max-deviation-ratio*] ;/
  ; (let ([cal (if(> a b) call rcall%)])
    ; [<= (1-(cal / a b)) *max-accuracy-error-ratio*]
  ; )
)

(def distance
  (case-lam
    ( [p1 p2] ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1      
      (if [eq (len p1) (len p2)] ;fill 0? ;nil? [_ p2]
        (sqrt
          [apply + (map [lam(x y)(pow(- x y))] p2 p1)] )
        nil
    ) )
    ([p2] [distance (nlist% '(0) (len p2)) p2])
) )

(defn min-prime-factor (n) ;factorize prime-num?
  (def (_ n tmp max.)
    (if (<= tmp max.)
      (if (!= (% n tmp) 0)
        [_ n (+ 2 tmp) max.]
        tmp )
      nil ;
  ) )
  (let ([max. (pow n 1/2)])
    (if (!= (% n 2) 0)
      [_ n 3 max.] ;n
      (if (eq n 2) nil ;
        2
) ) ) )
(def min-factor min-prime-factor)

(defn factors (n)
  (def (_ n factors.)
    (let ([factor (min-factor n)])
      (if (nilp factor)
        (cons n factors.)
        [_ (/ n factor) (cons factor factors.)]
  ) ) )
  (_ n nil)
) ;(cost(factors 40224510201988069377423))

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
      (if b (fx1+ s)
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
        (if b (fx1+ s)
          (if b2 3 s) )
        (- n (if b2 1 0))
        (if b2 '(2) '())
) ) ) )

;(cost (prime (1-[redu~ * (primes 2 13)]) 1))
;402245102020351 is the nth? prime-num start from 2 ?

(alias quot quotient)

(def n-digits ;integer-length 128 2
  (case-lam
    ( [num m] ;@ not for float
      (def (_ num n)
        (let ([quot (quotient num m)]) ;@ 1 2 4 2 1
          (if [< quot 1] n
            [_ quot (1+ n)]
      ) ) )
      (_ num 1) )
    ([num] (n-digits num 10))
) )
(ali nbits n-digits)

(def (leap-year? yr)
  (or (=0 [% yr 400])
    (and
      (=0 [% yr 4])
      (!=0[% yr 100])
) ) )

(def inc-1 (rcurry - 1)) ;

(def (strnum- . snums)
  (number->string (redu~ - (map string->number snums)))
)
(def (strnum+ . snums)
  (number->string (redu~ + (map string->number snums)))
)

;math end

(def [len-1 x] (1-[len x]))
(def (find-ref% xs x st ed)
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
      (if [or (eq n 0) (nilp xs)] xs ;
        (if* [< n 0] [remov-all x xs] ;g
          [eq n 1] [remov-1 x xs]
          (let ([a (car xs)] [d (cdr xs)])
            (if (g a x)
              [_ d (1- n)]
              (cons a [_ d n]) ;
    ) ) ) ) )
    [_ xs n]
) )

(def remov
  (case-lam
    ( [x xs n] ;@
      (if [< n 0]
        (if [nilp x]
          (remov-nil xs)
          (remov-n x xs n) ) ;(remov-all x xs)
        (remov-n x xs n)
    ) )
    ([x xs] (remov x xs -1))
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
(alias permu permutation)

(def (combinations xs n)
  (def (_ xs n)
    (if~
      [eq n 0] nil
      [eq n 1] (map list xs)
      [>= n (len xs)] (li xs) ;
      (append~ ;
        [_ (cdr xs) n]
        (map [curry~ cons (car xs)] ;
          [_ (cdr xs) (1- n)]
  ) ) ) )
  (_ xs n)
)

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

;(deep-reverse '(1(2 3)4)) ;-> '(4(3 2)1)
(def (deep-reverse xs)
  (def (d-rev xs)
    (if~
      [nilp xs] '() ;
      [pair? xs]
      (map d-rev
        (rev xs) ) ;
      else xs
  ) )
  (d-rev xs)
)
(ali d-rev deep-reverse)

;onlisp

(def-syt [nreverse! stx]
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

(ali list-divide-per group)

(def (group xs m) ;?(= m per) (group '(1 2 3 4 5 6) 3 1)
  (let ([m (if [eq 0 m] 1 m)]) ;
    (def (_ ret xs)
      (if (nilp xs) ret
        (let ([aa (head% xs m)] [dd (tail xs m)]) ;%
          [_ (cons aa ret) dd]
    ) ) )
    (rev (_ nil xs)) ;
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

(def (prune g xs)                           ;rec remov-if satisfy g ;!keep
  (def (_ xs ret)
    (if [nilp xs] (rev ret)
      (let ([a (car xs)][d (cdr xs)])
        (if [consp a] ;
          (_ d (cons [_ a nil] ret))
          (_ d [if (g a) ret (cons a ret)]) ;
  ) ) ) )
  (_ xs nil)
)

;(map-all list '(1 2) '(4) '(5 6)) ;~> 4 lists
(def (map-for-combinations g . xz)
  (def (~ ret tmp0 xs0 xz)  
    (def [_ ret tmp xs xz]
      (if (nilp tmp)
        (if (nilp xz)
          (map (curry redu g) ret) ;;~map ~redu
          (~ nil [rev ret] (car xz) (cdr xz)) ) ;;@
        (if (nilp xs)
          [_ ret (cdr tmp) xs0 xz] ;
          [_ (cons [cons(car xs)(car tmp)] ret) tmp (cdr xs) xz] ;;
    ) ) )
    [_ ret tmp0 xs0 xz]
  )  
  (d-rev [~ nil (list nil) (car xz) (cdr xz)]) ;remov nil xz
) ;4x+ slow
(ali map-all map-for-combinations)

;

(def (sym-explode sym) ;[explode 'asd] ~> '[a s d]
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

;(dmap [lam(x)(if[nilp x]0 x)] xs)
;(def +.ori +) ;+.0

(def (sum-of-tree@ xs) ;@ < redu~ < +
  (redu~ + xs)
  ; (def (_ x ret)
    ; (if~
      ; (num?  x) (+ ret x) ;
      ; (atomp x) ret ;nilp
      ; (_ (car x)
        ; [_ (cdr x) ret]
  ; ) ) )
  ; (_ xs 0)
)
(def (sum-of-list xs)
  (def (_ x ret)
    (if~
      (nilp x) ret
      (let ([a (car x)])
        (_ (cdr x)
          (if (num? a) (+ ret a) ret) ;
  ) ) ) )
  (_ xs 0)
)
(def (my+ . xs) (sum-of-list xs)) ;2.5x slower than ori +
;(def + my+) ;to test (fib0 42) ;need to be restored bef reload this script

(def (fast-expt-algo x n g x0) ;g need to meet the Commutative Associative Law
  (def (_ n)
    (if*
      (eq n 0) x0
      (eq n 1) x ;(* x x0) ==> x
      (letn ([m (_ (>> n 1))] [y (g m m)])
        (if (fxeven? n) y
          [g y x]
    ) ) )
  )
  (_ n)
) ; N mod z ?=> a^q*s^w*d^e mod z => ... ; encrypt: 椭圆曲线加密 ; 所有基于群幂的离散对数的加密算法

(ali mat-unitlen matrix-unitlen)
(ali mat-unit   matrix-unit)
(ali mat-unitof matrix-unitof)
(ali mat-mul matrix-mul)
(ali mat-pow matrix-pow)

(def (matrix-unitlen m) [len (car m)])

(def (matrix-unit n) ;vec?
  (def (once ret m i)
    (def (_ ret m)
      (if (< m 1) ret
        [_ (cons 0 ret) (1- m)]
    ) )
    [_ [cons 1 (xn2lis 0 i)] m] ;
  )
  (def (_ ret i m)
    (if [< m 0] ret
      [_ (cons(once nil m i)ret) (1+ i) (1- m)]
  ) )
  (_ nil 0 (1- n))
)

(def (matrix-unitof m) [matrix-unit (matrix-unitlen m)])

(def (matrix-pow m n)
  (fast-expt-algo m n matrix-mul (matrix-unitof m)) ;(fast-expt-algo m n mat-mul '[(1 0)(0 1)])
)

(define (fib0 n)
  (define (_ n) ;
    (if (< n 3) 1
      (+ [_ (- n 2)] [_ (1- n)])
  ) )
  (if (< n 0) 0
    (_ n)
) )
;(cost (fib0 42)) ;realtime = 1.111~1.188 s

(def (fib1 n) ;gmp: (fib 1E) just 1s
  ;(let ([st(clock)] [1st Fal])
    (def_ (fibo1 ret nex n)
      (if (< n 1) ret
        ; (bgn
          ; (if [=0 (%[- (clock) st]100)]
            ; (when 1st (setq 1st Fal) (echo ".") )
            ; (setq 1st Tru) )
          [_ nex (+ nex ret) (1- n)]
    ) ) ;)
    (fibo1 0 1 n)
) ;)

(def (fib n)
  (def (fibo pre pos n)
    (caar
      (matrix-mul  ;
        (if [>0 n] ; or ret: if odd? n: positive, negative;
          (matrix-pow '([ 0  1]
                        [ 1  1]) n) ;matrix may slower than paras
          (matrix-pow '([-1  1]
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
;(elapse(fac 50000)) ;=> elapse = 1.559~1.567 s

(defn round% (x)
  (let ([f (floor x)])
    (if [>= (- x f) 0.5] (1+ f)
      f
) ) )
(def myround
  (case-lam
    ([fl nFlt]
      (let ([fac (pow 10 nFlt)])
        (inexact (/ [round% (* fl fac)] fac)) ;@
    ) )
    ([fl] (myround fl 0))
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

(ali lis2mat group) ;(lis2mat '(1 2 3 4 5) 2) -> ((1 2) (3 4) (5 0))?
; (def (_ xs)
  ; (if (<= (len xs) per) ;
    ; (li xs)
    ; (cons (head xs per) [_ (tail xs per)]) ;
; ) )
(ali mat2lis flat)

(ali mat-ref xth)

;?matlen submat
(def (dotmul da db) ;(1,2,3)*(4,5,6) ;dot-multiply: point1 point2
  (redu~ + (map * da db)) ;
)
(defn convolution1 (m1 m2) ;convolution: matrix1 matrix2
  (redu~ dotmul (map mat2lis (li m1 m2)))
)

;middle-function
(def (pt-mat-mul p m) ;'(1 2 3) '((4 7)(5 8)(6 9))
  (def (_ m)
    (if [nilp (car m)] nil
      (cons [dotmul p (map car m)] [_ (map cdr m)]) ;todo
  ) )
  [_ m]
)
(ali mat-1Muln pt-mat-mul)

(def (mat-mat-mul ma mb) ;mul-2-matrixes
  (def (_ ma)
    (if (nilp ma) nil
      (cons [pt-mat-mul (car ma) mb] [_ (cdr ma)]) ;
  ) )
  [_ ma]
)
(ali mat-nMuln mat-mat-mul)

(def (matrix-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-mat-mul (car mts) (cdr mts))
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

(defn/defa nonlin (x deriv) [Fal] ;
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

(def (rcdr xs)
  (def (_ xs)
    (if (nilp (cdr xs)) nil
      (cons (car xs) [_ (cdr xs)])
  ) )
  (_ xs)
) ;a bit slower than (head xs n)

(def (mk-cps0 g) ;cps相当于做了堆栈交换?
  (lam args
    (let ([r (rev args)])
      ( [car r] ;last
        (redu g
          (rev (cdr r)) ;
) ) ) ) )
(def (mk-cps g)
  (lam args
    ( [last args]
      (redu g
        (rcdr args)
) ) ) )

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

(defn/defa ev-n (x m) [1]
  (def (_ x n)
    (if~ (> n m) x
      ; (let ([ret (ev x)])
        ; (if~ (eql x ret) x ;?
      [_ (ev x) (1+ n)]
  ) ) ;) )
  (_ x 1)
)

(alias try-fail? condition?)
(ali bad-try? condition?)
(def (full-eval x) ;
  (def (_ x)
    (let ([ret (try(ev x))])
      (if~ (try-fail? ret) x
        (eql x ret) x
        [_ ret]
  ) ) )
  (_ x)
)
(alias ev-full full-eval)

; (defsyt lam-snest
  ; ([x] nil)
; )

;;church-number: https://www.zhihu.com/question/39930042 https://www.jianshu.com/p/73f80c379860

(defn nex-prime (p)
  (prime p 2) ;
)
(def inc (curry + 1)) ;for church's f, use 1+ is not rooty ?

;(def (zero f) (lam(x) x))
;(def (one f) (lam(x) (f x))) ;((one inc) 0)
; (def (add1 nf)
  ; (lam(f) (lam(x) [f ((nf f) x)] )) )
(defn-snest chur0 (f x)   x)
(defn-snest chur1 (f x)   (f x))
;(defn-snest chur2 (f x)   ((compose f f) x))
(defn-snest chur2 (f x)   ((lam[z] [f[f z]]) x)) ;
(defn-snest chur3 (f x)   ((compose f f f) x))

(def (mk-chur num)
  (lam (f)
    [lam (x) ;lam-snest
      ((redu compose (xn2lis f num)) x) ;
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
      (eq n 0) ret
      [_ (1- n) (g ret n)]
  ) )
  (_ (1- n) (g n))
)
(defn num->rbump-g (n g)
  (def (_ n ret)
    (if* (< n 0) nil
      (eq n 0) ret
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


;vec@: mk-vec n; vec-fill!; vec-set! v i x;

(ali vec-len  vector-length)
(ali mk-vec   make-vector)
(ali vec-copy vector-copy)
(ali vec-set-fnum! vector-set-fixnum!)
(ali vec-set! vector-set-fixnum!)
(ali vecar    vec-car)

(def-syt (ve-push* stx)
  (syt-case stx () ;
    ( [_ args ... x]
      (identifier? #'x) ;
      #'[setq x (ve-cons* args ... x)] ) ;mk-vec will slower than list's
    ( [_ . args]
      #'(ve-cons* . args)
) ) )

(def (vec-nilp x) ;
  (if [vecp x]
    (=0 (vec-len x))
    Fal
) )
(alias vnilp vec-nilp)

;(def num->lis (curry apply/reducing-num cons)) ;
(def num->lis iota)

(def vnil (vec))
(def (vec-car v) (vec-ref v 0))
(def (vecadr v) (vec-ref v 1))

(def (vec-consp v) (and (vecp v) [>0(vec-len v)]))

(defn num->vec (n)   ;vec-flat ;@(lis->vec (range n))
  (let ([ve (mk-vec n)])
    (for (i n)
      (vec-set! ve i i) )
    ve
) )

(def (ve-last ve)
  (vec-ref ve [1- (vec-len ve)])
)

(defn vec-cons (x vy) ;* . xxv
  (if (vecp vy)
    (let ([ve (mk-vec [1+ (vec-len vy)])])
      (vec-set! ve 0 x)
      (vec-copy! ve 1 vy)
      ve
    )
    nil ;
) )
(def [ve-cons* . xxv]
  (letn ([vy (last xxv)][n (len xxv)][m (1- n)])
    (if (vecp vy)
      (let ([ve (mk-vec [+ m (vec-len vy)])])
        (vec-copy! ve 0 (lis->vec [ncdr xxv -1])) ;->lis flat
        (vec-copy! ve m vy)
        ve )
      nil
) ) )
(alias vecons vec-cons)

(defn vec-conz (vx y)
  (if (vecp vx)
    (letn ([n (vec-len vx)][ve (mk-vec [1+ n])])
      (vec-copy! ve 0 vx)
      (vec-set! ve n y)
      ve
    )
    nil ;
) )
(alias veconz vec-conz)


(def (vec-head ve n) ;
  (letn ([ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve i]) )
    ret
) )

(def (vec-tail ve m)
  (letn ([n (-(vec-len ve)m)][ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve [+ m i]]) )
    ret
) )
(def vec-cdr (rcurry vec-tail 1)) ;@
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

; (def (vec-foldl g x ve) ;walker? ref nilp
  ; (vec-for y in ve ;
    ; [set! x (g x y)] ) ;tmp ;(_ g tmp ve) try
  ; x
; )
(def (vec-foldl g x ve)
  (let ([n (vec-len ve)])
    (def (_ ret i)
      (if (>= i n) ret
        (let ([y (vec-ref ve i)]) ;try is slow
          [_ (g ret y) (1+ i)]
    ) ) )
    (_ x 0)
) )

(def (vec-redu g ve) ;slower than redu
  ;(vec-foldl g (vec-car ve) (vec-cdr ve)) ;
  (redu g (vec->lis ve))
)

(def (vec-swap! ve i j) ;!
  (let ([t 0])
    (set! t (vec-ref ve i))
    (vec-set-fnum! ve i (vec-ref ve j))
    (vec-set-fnum! ve j t)
) )

(def (vec-rev! ve)
  (letn ([n (vec-len ve)] [m (1- n)] [h (quot n 2)])
    (for (i h)
      (vec-swap! ve i [- m i])
) ) )

(def vec-copy! ;
  (case-lam
    [(ve) (vec-copy ve)]
    [(des i) (vec-tail des i)]
    [(des i src)
      [vec-copy! des i src (vec-len src)] ] ;
    [(des i src n)
      (letn ([dn (vec-len des)][m (min n [- dn i])])
        (for (j m)
          (vec-set! des (+ i j) (vec-ref src j)) ) ) ]
) )

(def (vec-append . vz)
  (letn ([n (len vz)][ns (map vec-len vz)][ret (mk-vec [redu + ns])])
    (for (i n)
      (vec-copy! ret (redu + [head ns i]) (xth vz i)) )
    ret
) )


;algo for vec-sort

;sort

(def (car->end! xs)
  (if (cdr-nilp xs) xs
    (bgn
      (set-cdr! (last-pair xs) (li (car xs))) ;
      (set-car! xs (cadr xs)) ;
      (set-cdr! xs (cddr xs))
      xs
) ) )


(def qsort
  (case-lam
    ([xs f] (sort f xs ))
    ([xs]   (qsort xs <))
) )
      
(define (merge-sort ls lt?) ;2x slower than sort
  (define merge~
    (lambda (ls1 ls2)
      (if (nilp ls1)
          ls2
          (if (nilp ls2)
              ls1
              (if [lt? (car ls1) (car ls2)]
                  (cons (car ls1) [merge~ (cdr ls1) ls2]) ;
                  (cons (car ls2) [merge~ ls1 (cdr ls2)]) ) ) ) ) )
  (define (_ ls n)
    (if (fx< n 2)
      ls
      (let ([mid (quotient n 2)])
        (merge~
          [_ (head ls mid) mid]
          [_ (tail ls mid) (fx- n mid)]
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

(def randnums
  (case-lam
    ([n m]
      (def (_ n)
        (if (< n 1) nil
          (cons (random m) [_ (1- n)]) ;
      ) )
      (_ n)
    )
    ([n] [randnums n n])
) )

;exercise
(defsyt try
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

(def (exist-match? g xs)
  (def (_ xs)
    (if (nilp xs) Fal
      (if (g (car xs)) Tru ;
        [_ (cdr xs)]
  ) ) )
  (_ xs)
)

;todo: Dijkstra

(define (memoize proc)
  (let ([cache '()])
    (lambda (x) ;
      (cond
        [(assq x cache) => cdr] ;(call cdr resl)
        [else
          (let ([ans (proc x)])
            (set! cache (cons(cons x ans)cache))
            ans
) ] ) ) ) )

;;; standard prelude @

; list utilities

;(divide-at (str->list "asd") 1 2) ~> '([#\a]..)
(def (divide-at xs i)
  (def (_ ret xs j)
    (if (nilp xs)
      (list ret nil) ;
      (if (eq j i) ;
        (list ret xs)
        [_ (cons(car xs)ret) (cdr xs) (1+ j)]
  ) ) )
  (_ nil xs 0)
)

(define (split n xs)
  (let loop ((n n) (xs xs) (zs '()))
    (if (or (zero? n) (null? xs))
        (values (reverse zs) xs)
        (loop (- n 1) (cdr xs) (cons (car xs) zs)))))

(define (take-while pred? xs)
  (let loop ((xs xs) (ys '()))
    (if (or (null? xs) (not (pred? (car xs))))
        (reverse ys)
        (loop (cdr xs) (cons (car xs) ys)))))

(define (drop-while pred? xs)
  (let loop ((xs xs))
    (if (or (null? xs) (not (pred? (car xs)))) xs
      (loop (cdr xs)))))

(define (split-while pred? xs)
  (let loop ((xs xs) (ys '()))
    (if (or (null? xs) (not (pred? (car xs))))
        (values (reverse ys) xs)
        (loop (cdr xs) (cons (car xs) ys)))))

;
; pattern matching

(define-syntax list-match
  (syntax-rules ()
    ((_ expr (pattern fender ... template) ...)
      (let ((obj expr))
        (cond ((list-match-aux obj pattern fender ...
                (list template)) => car) ...
              (else (error 'list-match "pattern failure")))))))

(define-syntax list-match-aux
  (lambda (stx)
    (define (underscore? x)
      (and (identifier? x) (free-identifier=? x (syntax _))))
    (syntax-case stx (quote quasiquote)
      ((_ obj pattern template)
        (syntax (list-match-aux obj pattern #t template)))
      ((_ obj () fender template)
        (syntax (and (null? obj) fender template)))
      ((_ obj underscore fender template)
        (underscore? (syntax underscore))
        (syntax (and fender template)))
      ((_ obj var fender template)
        (identifier? (syntax var))
        (syntax (let ((var obj)) (and fender template))))
      ((_ obj (quote datum) fender template)
        (syntax (and (equal? obj (quote datum)) fender template)))
      ((_ obj (quasiquote datum) fender template)
        (syntax (and (equal? obj (quasiquote datum)) fender template)))
      ((_ obj (kar . kdr) fender template)
        (syntax (and (pair? obj)
                (let ((kar-obj (car obj)) (kdr-obj (cdr obj)))
                  (list-match-aux kar-obj kar
                        (list-match-aux kdr-obj kdr fender template))))))
      ((_ obj const fender template)
        (syntax (and (equal? obj const) fender template))))))

;;

(defn call-nest (g . xs) ;
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

; system

;ffi

(alias load-lib load-shared-object)
(alias ffi? foreign-entry?) ;
(alias ffi foreign-procedure)

;CFName nArgs tyRet fname? ;(defc Beep (void* void*) bool [beep]) ;(api: Beep 2 bool [])? ;(fname-sym CFName)
;(_ fname (var1 var2) ret FName (void* void*))
;(_ bool Beep (freq=1047 dura))

(defsyt defc*
  ( [_ f]
    (defc* f (void)) ) ;
  ( [_ f args]
    (defc* f args void*) ) ;
  ( [_ f args ret] ;defa
    (defc* f args ret f) ) ;
  ( [_ api args ret f] ;f is case-sensitive ;how many args ;void* is ok too ;no ret is ok too ;
    (def f (ffi (sym->str 'api) args ret)) ) ;outer-proc ;todo f?
  ( [_ api args ret f rems]
    (defc* api args ret f)
) )

(defsyt defc
  ( [_ ret f args]
    (def f (ffi (sym->str 'f) args ret)) )
  ( [_ fnam ret api args] ;
    (def fnam (ffi (sym->str 'api) args ret)) )
  ( [_ fnam rems ret api args]
    (defc fnam ret api args) )
  ( [_ fnam rems ret api args flg]
    (def fnam (ffi flg (sym->str 'api) args ret))
) )

;

(load-lib "kernel32.dll") ;Beep
(defc* GetCommandLineA () string get-command-line)
(defc beep (freq dura) void* Beep (void* void*))
(defc c-sleep (ms) unsigned Sleep (unsigned) __collect_safe) ;(defc c-sleep Sleep 1) ;(ms) ;__collect_safe "sleep"
(alias sleep c-sleep)

(load-lib "msvcrt.dll")
(defc void* clock ())

(load-lib "winmm.dll")
(defc midi-out-get-num-devs() int midiOutGetNumDevs()) ;
(alias numofMidiOut midi-out-get-num-devs)

;(def (main-args) (str-split (GetCommandLineA) spc))

(def CLOCKS_PER_SEC 1000)
(def (clock*)
  (inexact (/ (clock) CLOCKS_PER_SEC)) ;
)

; (def (get-sec) ;x get-sec-nano
  ; (letn ( [time(current-time)]
      ; [sec(time-second time)]
      ; [nano(time-nanosecond time)] )
    ; (+ sec (.* [pow 10 -9] nano))
; ) )
(def (get-ms) ;x get-sec-nano
  (letn ( [time(current-time)]
      [sec(time-second time)]
      [nano(time-nanosecond time)] ) ;
    ;(list sec nano)
    (+ (.* sec [pow 10 3]) (.* nano [pow 10 -6])) ;
) )

(defsyt cost
  ( [_ g]
    (let ([t 0] [res nil])
      (echol (fmt ": ~s" 'g))
      ;(set! t (clock))
      (set! t (get-ms))
      (set! res g)
      ;(set! t (inexa(/ (-(clock)t) CLOCKS_PER_SEC)))
      (set! t (-(get-ms)t))
      ;(echol ": elapse =" t "s")
      (echol ": elapse =" t "ms")
      (li res t)
) ) )
(defsyt elapse ;just elapse but result
  ( [_ g]
    (let ([t 0])
      (echol (fmt ": ~s" 'g))
      ;(set! t (clock))
      (set! t (get-ms))
      g
      ;(set! t (inexa(/ (-(clock)t) CLOCKS_PER_SEC)))
      (set! t (-(get-ms)t))
      (echol ": elapse =" t "ms")
      t
) ) )


(def (eq/eql x)
  (if (str/pair/vec? x) eql eq)
)

(def (mem?% x xs) (bool(mem? x xs)))

;(setq a '(1 2 2 3 3 3 4)) ;~> '(2 3)
(def (filter-same xs)   ;OK
  (def (_ xs pure same) ;curr .vs. 1.pure, 2.same -> 3.ign
    (if (nilp xs) same  ;return
      (let ([a (car xs)])
        (if (mem? a pure)          ;1
          (if (mem? a same)        ;2 ;
            [_ (cdr xs) pure same] ;3
            [_ (cdr xs) pure (cons a same)] )
          [_ (cdr xs) (cons a pure) same] ;
  ) ) ) )
  (rev [_ xs nil nil])  ;final handling
)

(def (remov-same xs) ;filter-pure
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

(def-syt ppat ;ppattern for ?
  (syt-ruls (? comma unquote quote) ;comma for unquo?
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

(def-syt pmatch-aux
  (syt-ruls (else guard)
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

(def-syt pmatch ;~= aux ;p for pat
  (syt-ruls (else guard)    ;guard for ?
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
                (set! n (1+ n))
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

(def (rec-chk n f x0 . xs0) ; ;(_ 20 + 0 1 2)
  (def (_ x m)
    (if (>= m n) x ;
      [_ (redu f (cons x xs0)) (1+ m)] ;recurse
  ) )
  (_ x0 0)
)
(def (fix-chk n f . xs0) ; to help speed improve
  (def (_ x m)
    (if (>= m n) x ;
      [_ (redu f xs0) (1+ m)] ;
  ) )
  (_ nil 0)
)
(ali chk fix-chk)
;(chk 10 cdr '(1 2 3))

(def with-head?
  (case-lam
    ([xs ys eql] ;(_ '(1 2 3 4) '(1 2/3)) ;-> Y/N
      (def (_ xs ys)  
        (if (nilp ys) T ;xs?
          (if (nilp xs) F
            (if [eql (car xs) (car ys)]
              [_ (cdr xs) (cdr ys)]
              F
      ) ) ) )
      (_ xs ys))
    ([xs ys]
      (with-head? xs ys eql)
) ) )
(def with?
  (case-lam
    ( [xs ys eql] ;(_ '(1 2 3 4) '(2 3/4)) ;-> Y/N ;with/contain
      (def (_ xs)
        (if (nilp xs) F
          (if (with-head? xs ys eql) T ;xs?
            [_ (cdr xs)] ;len?
      ) ) )
      (if (nilp ys) F
        (_ xs)
    ) )
    ( [xs ys]
      (with? xs ys eql)
) ) )
(def (with-sym? s x)
  (redu (rcurry with? eq) ;
    (map (compose str->list sym->str) ;
      (list s x) ;
) ) )

(def (syms) (environment-symbols (interaction-environment)))

(defm (api? x) (bool [mem? 'x (syms)]))

(defm (api-with x) ;(_ string) ;-> '(xx-string-xx string-xx blar blar)
  (filter (rcurry with-sym? 'x) (syms))
)

;

;num2lis num2abc abc2num

(def (repeats xs n) ;ng
  (redu (curry map li) (xn2lis xs n))
  ; (redu (curry map-all list)
    ; (nx->list n xs) )
)



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
    [atom e] (if[eql e (cadr s1)] (car s1) e) ;
    (let [(head.[_ (car e) s1]) (tail.[_ (cdr e) s1])]
      (cons head. tail.)
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

(def (sym->chs sym)
  (str->list (sym->str sym))
)
(def (chs->sym chs)
  (str->sym (list->str chs))
)

; data

(setq *tab/jp/key-a-A* ;Xy: y: a i u e o ;z: n
 '( [  a あ ア][  i い イ][  u う ウ][  e え エ][  o お オ]
    [ ka か カ][ ki き キ][ ku く ク][ ke け ケ][ ko こ コ] 
    [ sa さ サ][ si し シ][ su す ス][ se せ セ][ so そ ソ] 
    [ ta た タ][chi ち チ][tsu つ ツ][ te て テ][ to と ト] 
    [ na な ナ][ ni に ニ][ nu ぬ ヌ][ ne ね ネ][ no の ノ] 
    [ ha は ハ][ hi ひ ヒ][ fu ふ フ][ he へ ヘ][ ho ほ ホ] 
    [ ma ま マ][ mi み ミ][ mu む ム][ me め メ][ mo も モ] 
    [ ya や ヤ][ yu ゆ ユ][ yo よ ヨ]                
    [ ra ら ラ][ ri り リ][ ru る ル][ re れ レ][ ro ろ ロ]
    [ wa わ ワ][ wo を ヲ]                           
    [  n ん ン]                                      
    [ ga が ガ][ gi ぎ ギ][ gu ぐ グ][ ge げ ゲ][ go ご ゴ]
    [ za ざ ザ][ zi じ ジ][ zu ず ズ][ ze ぜ ゼ][ zo ぞ ゾ]
    [ da だ ダ][ di ぢ ヂ][ du づ ヅ][ de で デ][ do ど ド] ;,ji
    [ ba ば バ][ bi び ビ][ bu ぶ ブ][ be べ ベ][ bo ぼ ボ]
    [ pa ぱ パ][ pi ぴ ピ][ pu ぷ プ][ pe ぺ ペ][ po ぽ ポ]
) )
(ali *jp-tab* *tab/jp/key-a-A*)

(setq aud/doremi
  '(
    [256 288 320 1024/3 384 1280/3 480] ;Hz
    ;512? pre*2
) )

; logic for data

(def (jp/prono-divide prono) ;pronounce: hi ra ga na->ひらがな
  (let ( [vowels '(#\a #\i #\u #\e #\o )]
      [spec  #\n] )
    (def (~ cs ret tmp flg) ;aft-n
      (if (nilp cs) (cons tmp ret)
        (letn ( [a (car cs)] [d (cdr cs)]
            [a.tmp (cons a tmp)] ) ;
          (if~
            (mem? a vowels)
              [~ d (cons a.tmp ret) nil Fal]
            flg
              [~ d (cons tmp ret) (cons a nil) Fal]
            (eq a spec)
              [~ d ret a.tmp Tru]
            [~ d ret a.tmp Fal]
    ) ) ) )
    (map chs->sym
      (deep-reverse [~ (sym->chs prono) nil nil Fal]) ;
) ) )

;

(setq *current-path* (str-replace (command-result "cd") "\r\n" "")) ; ?"Pro File"

; (def car car%) ;
; (def cdr cdr%)
; (def cadr (compose car cdr))
; (def cddr (compose cdr cdr))
;cddddr

; how to refine?
(set! *script-path* ;%
  (car(string->path-file ;
      (car(remove ""
          (string-divide
            (cadr(remove ""
                (string-divide (get-command-line) " ") ) ) ;ng
            "\""
  ) ) ) ) ) ;bug if just use load
)

(define (load-relatived file) ;
  (load (string-append *script-path* [(if (sym? file) symbol->string id) file]))
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 

(alias clean restore)
(def (restore)
  (setq nil nil
    ; car car.ori
    ; cdr cdr.ori
    ; map map.ori
    ;+   +.ori
) )

#|
```
|#