
== Faiz's ChezLib ==

- Usage:
  - For Windows
    - Double click `run.cmd` to run
    - Or, `chez a:/path/to/lib.sc` ...

---

- Define with DEFAULT values:
  - `(def/va (asd a [b 2]) (list a b)) (asd 1) ~> '(1 2)`
  
- API searching function:     
  - `(api-ls con) ~> '(cons cond)`
  
- Define with DOCUMENTATION:
  - `(def/doc (asd a) (list a))`
    - `(doc asd) ~> '(lam (a) ...)`
    - `(doc-paras asd) ~> '(a)`
  - Caution: Don't use def/doc for a internal recursive function!
