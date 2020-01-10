

(def (mat-unitlen m) [len(car m)])

(def (mat-unit n)
  (def (once ret m i)
    (def (_ ret m)
      (if (< m 1) ret        
        [_ (cons 0 ret) (1- m)]
    ) )
    [_ [cons 1 (xn2lis 0 i)] m]
  )
  (def (_ ret i m)
    (if [< m 0] ret
      [_ (cons(once nil m i)ret) (1+ i) (1- m)]
  ) )
  (_ nil 0 (1- n))
)

(def (mat-unitof m) [mat-unit(mat-unitlen m)])

(def (mat-pow m n)
  (fast-expt-algo m n mat-mul (mat-unitof m)) ;(fast-expt-algo m n mat-mul '[(1 0)(0 1)])
)


;matrix:
;'(1 2 3 4 5 6) --m*3->
;a mat: '((1 2 3)(4 5 6))
;((mat m 3) 1 2 3 4 5 6)
;(_ numForOneRow aFlattenList): (_ 3 (range 6)) -> '((0 1 2)(3 4 5))
; (defn_ lis2mat (lst per)
  ; (if (<= (len lst) per)
    ; (li lst)
    ; (cons (carn per lst) (_ (cdrn per lst) per));;
; ) )
(defn mat2lis (mat) ;matrix->list: matrix1
  (flat mat)
)
;?matlen submat
(def (dotmul da db) ;(1,2,3)*(4,5,6) ;dot-multiply: point1 point2
  (redu~ + (map * da db)) ;
)
(defn convolution1 (m1 m2) ;convolution: matrix1 matrix2
  (redu~ dotmul (map mat2lis (li m1 m2)))
)

;middle-function
(def (mat-1Muln m1 mn) ;'(1 2 3) '((4 7)(5 8)(6 9))
  (def (_ mn)
    (if [nilp (car mn)] nil
      (cons [dotmul m1 (map car mn)] [_ (map cdr mn)]) ;todo
  ) )
  [_ mn]
)

(def (mat-nMuln ma mb) ;mul-2-matrixes
  (def (_ ma)
    (if (nilp ma) nil
      (cons [mat-1Muln (car ma) mb] [_ (cdr ma)]) ;
  ) )
  [_ ma]
)

(def (mat-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-nMuln (car mts) (cdr mts))
)