
(def (id x) x)
(ali identity id)

(def (quiet . xs) )

;


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

;

(defsyn while
  ([_ k bd ...]
    (call/cc
      (lam (break)
        (let loop ()
          (if k
            [bgn bd ... (loop)]
            (break) ;
) ) ) ) ) )

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


(defm (raw . xs) 'xs)



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


(alias readexp read-expr)
(def (evs . xs) [ev (redu readexp xs)])

(def (xth xs i) ;%
  (if (nilp xs) nil ;
    (if (< i 0) nil
      (list-ref xs i) ;use len wil be slow
) ) )
(def (nth xs n) (xth xs (1- n)))

(defm (assert resl test)
  (letn ([tmp resl] [b(eql tmp test)]
      [ret(if b 'Ok 'Wrong!!)] [ss`(resl " expect " test " ---> " ,ret)] )
    (redu echo ss) ;
    (newln)
) )

(def (car->end xs)
  (set-cdr! (last-pair xs) (li(car xs))) ;
  (set-car! xs (cadr xs)) ;
  (set-cdr! xs (cddr xs))
  xs
)