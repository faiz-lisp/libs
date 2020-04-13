

;AI

(def ReLU (curry max 0))
(alias relu ReLU)

(defn sigmoid (x)
  (/ (1+ [exp(- x)]))
)
(defn swish (x)
  (* x (sigmoid x))
)

(def/defa (nonlin x (deriv Fal)) ;
  (if (eql deriv Tru)
    (* x [- 1 x])
    (sigmoid x)
) )
