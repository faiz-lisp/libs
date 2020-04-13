

(defsyn setq
  [(_ a) (set! a (void))]
  ((_ a b)
    (bgn (set! a b) (if *will-ret* a))
  )
  ((_ a b c ...)
    (bgn
      (set! a b)
      (setq c ...) ;
) ) )