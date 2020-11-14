
== Faiz's ChezLib ==

---

- Define with DEFAULT values:
  - `(def/va (asd a (b 2)) (list a b)) (asd 1) ~> '(1 2)`
  
- API searching function:     
  - `(api-ls co) ~> '(cons cond)`
  
- Define with DOCUMENTATION:
  - `(def/doc (asd a) (list a))`
    - `(doc asd) ~> '(lam (a) ...)`
    - `(doc-paras asd) ~> '(a)`
  - Caution: Don't use def/doc for a internal recursive function!
