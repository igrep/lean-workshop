inductive proposition where
| atom (id : String)
| implies (p q : proposition)
| false

open proposition

def not (p : proposition) : proposition :=
  p.implies false

def true : proposition :=
  false.implies false

def ex_P :=
  /- P -> P -/
  (atom "P").implies (atom "P")

def ex_PQ :=
  /- P -> Q -/
  (atom "P").implies (atom "Q")

def ex_PQR :=
  /- (P -> Q -> R) -> (P -> Q) -> P -> R -/
    ((atom "P").implies ((atom "Q").implies (atom "R"))).implies
    (((atom "P").implies (atom "Q")).implies ((atom "P").implies (atom "R")))
