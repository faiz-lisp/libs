
;C

(def-syn +=
  (syntax-rules()
    ((_ x . xs)
      (bgn
        (set! x (+ x . xs))
        x
) ) ) )
(def-syn -=
  (syntax-rules()
    ((_ x . xs)
      (bgn
        (set! x (- x (+ . xs)))
        x
) ) ) )

(ali >> bitwise-arithmetic-shift-right)
(ali << bitwise-arithmetic-shift-left)