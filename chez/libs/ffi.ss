

;

;complex-syntax

(define-syntax define-c-function
  (lambda (x)
    (define gen-id
      (lambda (k value)
        (datum->syntax k ;
          (string->symbol
            (id
              (let ([v (syntax->datum value)]) ;datum
                [if (string? v) v (symbol->string v)]
    ) ) ) ) ) )
    (syntax-case x () ;
      ( [k cfnam (In ...) Ret]
        (with-syntax ([name (gen-id #'k #'cfnam)]) ;
         #'(define name ;
            (foreign-procedure [if (string? 'cfnam) 'cfnam (symbol->string 'cfnam)]
              (In ...) Ret
      ) ) ) )
) ) )

;(load-lib "kernel32.dll") ;Beep
;(defc* GetCommandLineA () string get-command-line)
;(defc get-command-line () string GetCommandLineA ())
(defc beep (freq dura) void* Beep (void* void*))
(defc c-sleep (ms) void* Sleep (void*)) ;(defc c-sleep Sleep 1) ;(ms)
(alias sleep c-sleep)

(load-lib "msvcrt.dll")
(defc void* clock ())

(load-lib "winmm.dll")
(defc midi-out-get-num-devs() int midiOutGetNumDevs()) ;
(ali numofMidiOut midi-out-get-num-devs)