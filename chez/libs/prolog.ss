
;unify

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