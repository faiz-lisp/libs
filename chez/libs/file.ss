
; file: load-file-cont-as-str

(def (save-file cont file)
  (if (file-exists? file) (delete-file file)) ;
  (let ([of (open-output-file file)])    
    (write cont of)
    (close-port of)
) )