


(def (last pr)
  (car (last-pair pr))
)


(def (append% xz)
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        [_ (car yz) (cdr yz)]
        (cons (car xs) [_ (cdr xs) yz])
  ) ) )
  (let ([xz2 (remov-nil xz)])
    (_ (car xz2) (cdr xz2)) ;
) )

(def (append~ . xz)
  (apply append (remov-nil xz))
)

;

(def-syn (append!% stx) ;
  (syn-case stx ()
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

;
