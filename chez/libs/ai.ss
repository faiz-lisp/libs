
; AI

(alias relu ReLU)

;

(def ReLU (curry max 0))

;

(defn sigmoid (x)
  (/ (1+ [exp (- x)]))
)

(defn swish (x)
  (* x (sigmoid x))
)

(def/va (nonlin x [deriv F])
  (if (eq deriv T)
    (* x [- 1 x])
    (sigmoid x)
) )
