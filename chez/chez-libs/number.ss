
(def (num2nth n)
  (str n
    (case (% n 10)
      (1 "st")
      (2 "nd")
      (3 "rd")
      (else "th")
) ) )

(def (num2mon n) ;int
  (let ([mons '(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec)])
    (if* (> n 12) nil
      (< n 1) nil
      (str (list-ref mons [1- n]))
) ) )



(def (w* num) (* num 10000))