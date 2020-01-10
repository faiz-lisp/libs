; Chez-lib.ss v2.00 - Written by Faiz

#|
  update notes:
    2020-1-6 v2.00: modularization

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

  versions: fast-> Grace-> safe: experimental
    
  seq of implements:
    (g x y)~> apply~= reduce-> curry
    
    last-pair last list?
    length
    append->conz->rpush ... slowest
    ? eval->reduce->compose/curry
    strcat
    remove
    lis->vec vec->lis
    
    sort, .., cond if, .., map, .., append;
    syntax, func    
    def_ set!~def alias
    cons vector list
    
    reverse append! list-copy 
    
    apply let 
    eq, =, eql

  todo:
    [random-seed (floor->fix(w* (elapse(fib 500000))))] ;too closed ;~> parallel universe id bytes, not work well
      time.ms->md5->cost.ns?
      . time activities info net:salt io? file:psw/md5
    (nthof-g-resl rand '(3 1 4) [max-n 10000000])
    (nthof-g rand nth [len 1])
    (list-head '() 1)
    d-rev
    grep grep-rn 
    (explode-str str sepa)
    (disting-code)
    clean reload? load compile udp/tcp get/post v3 juce ui test trace
    if(!#f/nil): cadr caddr cadddr eval, repl
    cond case, for map lambda foldl reduce curry recursion repl foldr
    lam-snest
    (range% sum f p n)
    ? (str/sep sep . xs)
      -> echo
      => any->int
    (_ xs . x) (-> -> x)
    code:dsl->raw
    api-search 可以 下载个网页, 然后用正则搜索; 每次defn时,记录信息到hashtable
    church yc algo
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
    let-values(<->)
    def-syn doesnt supp recursion directly, but case
    def-syn cant be in ano def-syn
    
  to-try
    walker 
    
  to-optimize:
    defa-def def/defa
    ;def_: fluid-let-syntax
    def-syn
    def f g -> alias f g
    def_/def -> def (def (_ ..) ..) ..
    nilp (cdr xs)
    [] -> ()
    (small .. big) -> (big .. small)
    
  to-debug:
    (trace fib)?, assert&print, debug?, call/cc+assert+return.false ...

  flow: work->fast->safe?->complete
    ;must-inits
    ; main-apis
    ;apis-for-main
    ; apps-api
    ;endups
    ; test
    
  common:
    (_ X x)
    ? syt -> '
|#

;

(define (list . xs) xs) ;~

(define (rev xs)
  (define (_ xs ret)
    (if (null? xs) ret
      (_ (cdr xs) [cons (car xs) ret])
  ) )
  (_ xs '())
)

;

(define (compose . gs) ;
  (define (_ ret gs)
    (cond ;[nilp gs] id ;nop x.id x.li
      ([null? (cdr gs)]
        (lambda xs (ret [apply(car gs)xs])) )
      (else
        (_ 
          (lambda (x) (ret [(car gs) x]))
          (cdr gs)
  ) ) ) )
  (_ id gs)
)

;

(define (str-explode s)
  (map (compose list->string list) (string->list s))
)
(alias str->ss str-explode)

(define (lis->revstr chs) ;lis->revstr
  (list->string (rev chs))
)
  
;(def/defa (string-divide s [sep " "])
(define (string-divide s sep)
  (if (eq? "" sep) [str->ss s] ;
    (let ([chs(string->list s)] [csep(car(string->list sep))]) ;
      (define (_ chs tmp ret)
        (if [null? chs] (cons[lis->revstr tmp]ret)
          (let ([a(car chs)]) ;
            (if [eq? a csep] ;
              [_ (cdr chs) '() (cons[lis->revstr tmp]ret)] ;
              [_ (cdr chs) (cons a tmp) ret]
      ) ) ) )
      [rev(_ chs '[] '[])]
) ) )

(define (string-divide-rhs-1 s sep) ;todo: str-sep
  (if (eq? "" sep) [str->ss s]
    (if (eq? "" s) s ;
      (let ([chs(string->list s)] [csep(car(string->list sep))]) ;
        (define (_ chs ret)
          (if (null? chs) (list "" [list->string ret]) ;
            (let ([a (car chs)]) ;
              (if [eq? a csep] ;
                (list [lis->revstr chs] [list->string ret]) ;
                [_ (cdr chs) (cons a ret)]
        ) ) ) )
        [_ (rev chs) '()]
) ) ) )
(define (string->path-file s)
  (string-divide-rhs-1 s "/") ;
)

;

(load-shared-object "kernel32.dll")
(define get-command-line [foreign-procedure (symbol->string 'GetCommandLineA) () string])

;

(set! *script-path* ;%
  ;(cadr(string-divide (get-command-line) "\"" ) ;
  (car(string->path-file
      (car(remove ""
          (string-divide
            (cadr(remove ""
                (string-divide (get-command-line) " ") ) )
            "\""
  ) ) ) ) ) ;bug if just use load
) ;relatived
;(display *script-path*)

;

(define (load-relatived file)
  (load (string-append *script-path* file)) ;
)
  
#|
todo:
  synt, func
  ? dis-ordered load func
  - debug tools
  . how to do when re-def/defsyt/setq/alias ?
|#

(load-relatived (symbol->string 'chez-libs/alias.ss))
(load-relatived (symbol->string 'chez-libs/syntax.ss)) ;
(load-relatived (symbol->string 'chez-libs/define.ss))
(load-relatived (symbol->string 'chez-libs/control.ss)) ;
(load-relatived (symbol->string 'chez-libs/nested.ss)) ;
(load-relatived (symbol->string 'chez-libs/global.ss))   ;
(load-relatived (symbol->string 'chez-libs/set!.ss)) 
(load-relatived (symbol->string 'chez-libs/core.ss)) 
(load-relatived (symbol->string 'chez-libs/faster.ss))   ;
(load-relatived (symbol->string 'chez-libs/shortcut.ss)) ;

(load-relatived (symbol->string 'chez-libs/extend.ss))   ;
(load-relatived (symbol->string 'chez-libs/syt-ext.ss))  ;
(load-relatived (symbol->string 'chez-libs/trial.ss))
(load-relatived (symbol->string 'chez-libs/vector.ss))   ;
(load-relatived (symbol->string 'chez-libs/list.ss))     ;
(load-relatived (symbol->string 'chez-libs/string.ss))   ;
(load-relatived (symbol->string 'chez-libs/number.ss))   ;
(load-relatived (symbol->string 'chez-libs/function.ss)) ;
(load-relatived (symbol->string 'chez-libs/math.ss)) ;
(load-relatived (symbol->string 'chez-libs/utility.ss)) ;
(load-relatived (symbol->string 'chez-libs/length.ss)) ;
(load-relatived (symbol->string 'chez-libs/algo.ss)) ;
(load-relatived (symbol->string 'chez-libs/nth.ss)) 
(load-relatived (symbol->string 'chez-libs/type.ss)) ;

(load-relatived (symbol->string 'chez-libs/cl-dsl.ss)) ;
(load-relatived (symbol->string 'chez-libs/c.ss)) ;
(load-relatived (symbol->string 'chez-libs/onlisp.ss)) ;
(load-relatived (symbol->string 'chez-libs/matrix.ss)) ;
(load-relatived (symbol->string 'chez-libs/test.ss))   ;
(load-relatived (symbol->string 'chez-libs/ai.ss))     ;
(load-relatived (symbol->string 'chez-libs/file.ss))   ;
(load-relatived (symbol->string 'chez-libs/theory.ss)) ;
(load-relatived (symbol->string 'chez-libs/church.ss)) ;
(load-relatived (symbol->string 'chez-libs/sort.ss))   ;
(load-relatived (symbol->string 'chez-libs/debug.ss))  ;

(load-relatived (symbol->string 'chez-libs/ffi.ss))    ;
(load-relatived (symbol->string 'chez-libs/tool.ss))   ;

(load-relatived (symbol->string 'chez-libs/pmatch.ss)) ;
(load-relatived (symbol->string 'chez-libs/cps.ss))

(load-relatived (symbol->string 'chez-libs/prolog.ss)) ;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
