
(alias cond? condition?)
(defsyn try
  ([_ exp]
    (guard (x(els x)) exp) ;(condiction? #condition) -> *t
) )