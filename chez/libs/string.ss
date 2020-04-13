

(defn str-mapcase% (mf s)
  (list->string (map mf (string->list s))) ;
)
(ali str-upcase   string-upcase)
(ali str-downcase string-downcase)


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



(def (str . xs) (lis->str xs))

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
