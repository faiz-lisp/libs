

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

(defn quine (g) `(,g ',g))

; (defsyn lam-snest
  ; ([x] nil)
; )

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