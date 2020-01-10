
;(def (main-args) (str-split (GetCommandLineA) spc))

(def CLOCKS_PER_SEC 1000)
(def (clock*)
  (inexact (/ (clock) CLOCKS_PER_SEC)) ;
)

(defsyn cost
  ( [_ g]
    (let ([t 0] [res nil])
      (echol ":" 'g)
      (set! t (clock))
      (set! res g)
      (setq t [./ (-(clock)t) CLOCKS_PER_SEC])
      (echol ": elapse =" t "s")
      (li res t)
) ) )
(defsyn elapse ;just elapse but result
  ( [_ g]
    (let ([t 0])
      (echol ":" 'g)
      (set! t (clock))
      g
      (setq t [./ (-(clock)t) CLOCKS_PER_SEC])
      (echol ": elapse =" t "s")
      t
) ) )