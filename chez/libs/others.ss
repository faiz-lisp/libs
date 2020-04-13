
(def (assert0 resl test)
  (echol
    (if (eql resl test) 'Ok
      'Wrong!!
) ) )

;

; todo: (_ + 2 * 3) (_ f a g b ...)
; (def (compose-fx . fxs) ;see to compose and xn-mk-list
  ; (_ (curry [car fxs] [cadr fxs]) [cddr fxs])
; )




;strcat
; (def (strcat% ss)
  ; (def (_ ss ret)
    ; (if (nilp ss) ret
      ; [_ (cdr ss) [append~ (string->list (car ss)) ret]]
  ; ) )
  ; (list->string (_ ss nil)) ;(list->string [append% (map string->list ss)])
; )


; (defn conz! (xs . ys) ;->syn
  ; (set-cdr! (last-pair xs) ys)
  ; xs
; )




; (defsyn cons~
  ; ([_ xs ...] ;[_ 1 2 3 '(4)] ~> [~ '(4) 3 2 1]
    ; (redu cons* (sy-rev xs ...))
; ) )

; (def (any->str/raw x)
  ; (cond
    ; ((symbol? x) (sym->str            x)) ;
    ; ((bool?   x) [if x "#t" "#f"]) ;               x
    ; ((number? x) (number->string      x))
    ; ((char?   x) (list->string (list  x)))
    ; ((string? x)                      x)
    ; ((list?   x) (lis->str            x))
    ; ((pair?   x) (lis->str(pair->list% x)))
    ; ((fn?     x)  "") ;ty?
    ; ((atom?   x) (sym->str           'x)) ;
    ; (els          "")
; ) )

;CFName nArgs tyRet fname? ;(defc Beep (void* void*) bool [beep]) ;(api: Beep 2 bool [])? ;(fname-sym CFName)
;(_ fname (var1 var2) ret FName (void* void*))
;(_ bool Beep (freq=1047 dura))

;num2lis num2abc abc2num
