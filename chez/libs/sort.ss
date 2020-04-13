

;(def/defa (qsort xs [f <]) (sort f xs)) ;ratio will -6%
(def (qsort xs f) (sort f xs))

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