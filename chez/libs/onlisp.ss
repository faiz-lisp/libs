
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
