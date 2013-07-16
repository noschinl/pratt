(* Session name, add to AFP group, list base session: *)
session "Pratt_Certificate" (AFP) = "HOL-Number_Theory" +

(* Timeout (in sec) in case of non-termination problems *)
  options [timeout = 3600]

(* To suppres document generation of some theories *)
  theories [document = false]
    "~~/src/HOL/Algebra/Coset"
    "~~/src/HOL/Algebra/AbelCoset"
    "~~/src/HOL/Algebra/Ideal"
    "~~/src/HOL/Algebra/RingHom"
    "~~/src/HOL/Algebra/Module"
    "~~/src/HOL/Algebra/UnivPoly"

(* The top-level theories of the submission *)
  theories
    Pratt

(* Dependencies on non-Isabelle files *)
  files
    "document/root.tex"
    "document/root.bib"
