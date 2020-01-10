
(defn swap-para (g)
  (lam xs
    (redu g (rev xs)) ;!?
) )