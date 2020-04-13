
;yin's code

(def cps ;cont-pass-style
  (lam (exp)
    (letrec ;recurse
      ( [trivial? (lam (x) ;
            (memq x '(zero? add1 sub1)) )] ;member-quo?
        ;[id   (lambda (v) v)]
        [ctx0 (lambda (v) `(k ,v))]      ; tail context
        [fv (let ([n -1])
              (lam ()
                (set! n (+ 1 n))
                (string->symbol (string-append "v" (number->string n)))))]
        [cps1 (lam (exp ctx)
            (pmatch exp ;
              ( ,x [guard (not(pair? x))] (ctx x) )
              ( (if ,test ,conseq ,alt)
                [cps1 test (lam (t)
                    (cond
                      [(memq ctx (list ctx0 id))
                       `(if ,t ,(cps1 conseq ctx) ,(cps1 alt ctx))]
                      [else
                        (let ([u (fv)])
                         `(let ([k (lambda (,u) ,(ctx u))])
                            (if ,t ,(cps1 conseq ctx0) ,(cps1 alt ctx0))
              ) ) ] ) ) ] )
              ( (lam (,x) ,body)
                (ctx `(lambda (,x k) ,(cps1 body ctx0))) )
              [ (,op ,a ,b)
                [cps1 a (lam (v1)
                    [cps1 b (lam (v2)
                        (ctx `(,op ,v1 ,v2))
              ) ] ) ] ]
              [ (,rator ,rand)
                [cps1 rator (lam (r)
                    [cps1 rand (lam (d)
                        (cond
                          [(trivial? r) (ctx `(,r ,d))]
                          [(eq? ctx ctx0) `(,r ,d k)]  ; tail call
                          [else
                            (let ([u (fv)])
                             `(,r ,d (lam (,u) ,(ctx u)))
      ) ] ) ) ] ) ] ] ) ) ] )
      (cps1 exp id)
) ) )


;to-test: (cps ...)