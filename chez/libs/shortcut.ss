

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
(def *v (void) )
(def *e '[(err)] ) ;
(def spc " ")
(def nil '()) ;
(def Fal *f) ;
(def Tru *t)
(def No  *f)
(def Yes *t)
(def Err *v) ;

(def void? (curry eq *v))
(def (str/pair? x) [or(string? x)(pair? x)]) ;x
(def (str/pair/vec? x) [or(string? x)(pair? x)(vector? x)]) ;for eql/eq

;

(def (set-alp! pr x)
  (set-car! (last-pair pr) x)
)
(def (set-dlp! pr x)
  (set-cdr! (last-pair pr) x)
)


(ali todo quiet)
(ali tofix id)
(ali ?~ if*)