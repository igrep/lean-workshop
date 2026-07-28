inductive ev : Nat → Prop where
  | ev_0 : ev 0
  | ev_SS (n : Nat) (H : ev n) : ev (.succ (.succ n))


#check (ev.ev_SS : ∀ n, ev n → ev (.succ (.succ n)))

theorem ev_4 : ev 4 := by
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_0

#print ev_4
#check ((.ev_SS 2 (.ev_SS 0 .ev_0)) : ev 4)

theorem ev_4' : ev 4 := by
  apply (ev.ev_SS 2 (.ev_SS 0 .ev_0))

theorem ev_4'' : ev 4 := by
  show_term apply ev.ev_SS
  show_term apply ev.ev_SS
  show_term apply ev.ev_0

def ev_4''' : ev 4 :=
  .ev_SS 2 (.ev_SS 0 .ev_0)

#print ev_4
#print ev_4'
#print ev_4''
#print ev_4'''

theorem ev_8 : ev 8 := by
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_SS
  apply ev.ev_0

def ev_8' : ev 8 :=
  .ev_SS 6 (.ev_SS 4 (.ev_SS 2 (.ev_SS 0 .ev_0)))

theorem ev_plus4 : ∀ n, ev n → ev (n + 4) := by
  intro n H
  apply ev.ev_SS
  apply ev.ev_SS
  apply H

def ev_plus4' : ∀ n, ev n → ev (n + 4) :=
  fun (n : Nat) => fun (H : ev n) =>
    .ev_SS (.succ (.succ n)) (.ev_SS n H)

def ev_plus4'' (n : Nat) (H : ev n) : ev (n + 4) :=
  .ev_SS (.succ (.succ n)) (.ev_SS n H)

#check (ev_plus4'' : ∀ n : Nat, ev n → ev (n + 4))

def ev_plus2 : Prop :=
  ∀ n, ∀ (E : ev n), ev (n + 2)

def ev_plus2' : Prop :=
  ∀ n, ∀ (_ : ev n), ev (n + 2)

def ev_plus2'' : Prop :=
  ∀ n, ev n → ev (n + 2)

def add2 : Nat → Nat := by
  show_term intro n
  show_term apply Nat.succ
  show_term apply Nat.succ
  show_term apply n

#print add2
#eval add2 2

namespace Props

namespace And

inductive and (P Q : Prop) : Prop where
  | conj : P → Q → and P Q

#check and.conj

scoped infix : 60 (priority := high) " /\\ " => and

theorem proj1' : ∀ P Q,
  P /\ Q → P := by
  intro P Q HPQ
  cases HPQ
  case conj p q => apply p

theorem and_comm : ∀ P Q : Prop, P /\ Q ↔ Q /\ P := by
  intro P Q
  constructor
  · intro ⟨HP, HQ⟩
    constructor
    · apply HQ
    · apply HP
  · intro ⟨HQ, HP⟩
    constructor
    · apply HP
    · apply HQ

#print and_comm

def proj1'' P Q (HPQ : P /\ Q) : P :=
  match HPQ with
  | and.conj HP HQ => HP

def and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | and.conj HP HQ => and.conj HQ HP

def and_comm' P Q : P /\ Q ↔ Q /\ P :=
  Iff.intro (and_comm'_aux P Q) (and_comm'_aux Q P)

def conj_fact : ∀ P Q R, P /\ Q → Q /\ R → P /\ R :=
  fun _P _Q _R HPQ HQR =>
    match HPQ, HQR with
    | and.conj HP _HQ, and.conj _HQ' HR =>
      and.conj HP HR

end And

end Props

