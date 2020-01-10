
(def-syn define*
  (syn-ruls ()
    ( [_ x]
      (define x *v) ) ;
    ( [_ (g . args) body ...]
      (define (g . args) body ...) )
    ( [_ x e]
      (define x e) )
    ( [_ g (args ...) body ...] ;
      (def (g args ...) body ...) )
) )
(alias def define*)

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

;

(def-syn defun
  (syn-ruls ()
    ( [_ f (args ...)]
      (define (f args ...) *v) )
    ( [_ f args]
      (define (f . args) *v) ) ;
    ( [_ f args ...]
      (define f (lam args ...)) )
) )
(ali defn defun)

;

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

(def-syn defn_
  (syn-ruls ()
    ( [_$% f args bd...] ;
      (def_ (f . args) bd...)
) ) )

;


(def (list-the-front xs) ;partly ;(_ '(a (b) (c 1) d)) ~> '((a) (b) (c 1) (d)) ~> '((a) (b) (c 1) (d nil))
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a(car xs)])
        (if (sym? a) ;consp lisp sym? ?
          (cons (li a) [_ (cdr xs)]) ;
          xs
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

(def-syn defa-def ;@ g x . ys
  (syn-ruls ()
    ( [_ (g . args) body ...]
      (define (g . xs) ;
        (letn([max-ln (if [atomp(car 'args)] 10 (len 'args))] ;
              [raw-ln (len xs)] ;
              [ln (min raw-ln max-ln)]
              [need (sy/num-not-defa-vals% args 0)] ;numof-NotDefas
             )
          (ev `[define (f_ ,@(map car 'args)) body ...]) ;
          (if (< ln need) nil ;
            (redu f_
              (append xs
                (map [lam(x)[ev (cadr x)]] (list-tail 'args ln)) ;ev
) ) ) ) ) ) ) )
(defsyn def/defa ; (_ (g a b (c 3) (d 4)) (+ a b c d))
  ( [_ (g . args) body ...]
    (ev `(defa-def (g ,@[sy/list-the-front args]) body ...)) ;
) )


(defsyn defc*
  ( [_ f]
    (defc* f (void)) ) ;
  ( [_ f args]
    (defc* f args void*) ) ;
  ( [_ f args ret] ;defa
    (defc* f args ret f) )
  ( [_ api args ret f] ;f is case-sensitive ;how many args ;void* is ok too ;no ret is ok too ;
    (def f (ffi (sym->str 'api) args ret)) ) ;outer-proc ;todo f?
  ( [_ api args ret f rems]
    (defc* api args ret f) )
)

(defsyn defc
  ( [_ ret f args]
    (def f (ffi (sym->str 'f) args ret)) )
  ( [_ fnam ret api args]
    (def fnam (ffi (sym->str 'api) args ret)) )
  ( [_ fnam rems ret api args]
    (defc fnam ret api args) )
)