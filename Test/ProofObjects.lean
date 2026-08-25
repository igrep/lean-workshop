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

namespace Or

inductive or (P Q : Prop) : Prop where
  | or_introl : P → or P Q
  | or_intror : Q → or P Q

scoped infix : 60 (priority := high) " \\/ " => or

theorem inj_l : ∀ (P Q : Prop), P → P \/ Q :=
  fun P Q HP => or.or_introl HP

theorem inj_l' : ∀ (P Q : Prop), P → P \/ Q := by
  intro P Q HP
  left
  apply HP

theorem or_elim : ∀ (P Q R : Prop),
  (P \/ Q) → (P → R) → (Q → R) → R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or.or_introl HP => HPR HP
    | or.or_intror HQ => HQR HQ

theorem or_elim' : ∀ (P Q R : Prop),
  (P \/ Q) → (P → R) → (Q → R) → R := by
  intro P Q R HPQ HPR HQR
  cases HPQ
  case or_introl HP =>
    apply HPR
    apply HP
  case or_intror HQ =>
    apply HQR
    apply HQ

/-
def or_bogus : ∀ P Q, P \/ Q → P :=
  fun (P Q : Prop) (A : P \/ Q) =>
    match A with
    | or.or_introl H => H
-/

end Or

theorem or_commut' : ∀ P Q, P ∨ Q → Q ∨ P :=
  fun P Q HPQ =>
    match HPQ with
    | Or.inl HP => Or.inr HP
    | Or.inr HQ => Or.inl HQ

namespace Ex

inductive ex {A : Type} (P : A → Prop) : Prop where
  | ex_intro : ∀ x : A, P x → ex P

notation "exists'" x ", " p => ex (fun x => p)

#check (ex (fun n => ev n) : Prop)

end Ex

theorem some_nat_is_even : ∃ n, ev n :=
  Exists.intro 4 (ev.ev_SS 2 (ev.ev_SS 0 ev.ev_0))

theorem ex_ev_Sn : Exists (fun n : Nat => ev n.succ) :=
  Exists.intro 1 (ev.ev_SS 0 ev.ev_0)

theorem dist_exists_or_term (X : Type) (P Q : X → Prop) :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x) :=
  fun H =>
    match H with
    | Exists.intro x Hx =>
      match Hx with
      | Or.inl HPx => Or.inl (Exists.intro x HPx)
      | Or.inr HQx => Or.inr (Exists.intro x HQx)

theorem ex_match : ∀ (A : Type) (P Q : A → Prop),
  (∀ x, P x → Q x) →
  (∃ x, P x) → (∃ x, Q x) :=
  fun A P Q H1 H2 =>
    match H2 with
    | Exists.intro x HPx => Exists.intro x (H1 x HPx)

inductive True : Prop where
  | I : True

theorem p_implies_true : ∀ P, P → True :=
  fun P HP => True.I

inductive False : Prop where

theorem contra : False := 
  match False with
  | _ => sorry

theorem false_implies_zero_eq_one : False → 0 = 1 :=
  fun contra =>
    nomatch contra

theorem ex_falso_quodlibet' : ∀ P : Prop, False → P :=
  fun P contra =>
    nomatch contra

namespace EqualityPlayground

inductive eq {X : Type} : X → X → Prop where
  | eq_refl : ∀ x, eq x x

scoped infix:50 " === " => eq

theorem four : 2 + 2 === 1 + 3 := by
  apply eq.eq_refl

theorem four' : 2 + 2 === 1 + 3 :=
  eq.eq_refl 4

theorem singleton : ∀ (X : Type) (x : X), [] ++ [x] === x :: [] :=
  fun (X : Type) (x : X) => eq.eq_refl [x]

theorem eq_add : ∀ (n1 n2 : Nat), n1 === n2 → n1.succ === n2.succ :=
  fun n1 n2 Heq =>
    match Heq with
    | eq.eq_refl n1 => eq.eq_refl n1.succ

theorem eq_add' : ∀ (n1 n2 : Nat), n1 === n2 → n1.succ === n2.succ := by
  intro n1 n2 Heq
  try rw [Heq] -- doesn't work for _our_ === relation
  cases Heq -- n1 and n2 replaced by n in the goal!
  try rfl -- doesn't work for _our_ === relation
  apply eq.eq_refl

theorem eq_cons : ∀ (X : Type) (h1 h2 : X) (t1 t2 : List X),
  h1 === h2 → t1 === t2 → h1 :: t1 === h2 :: t2 :=
  fun (X : Type) (h1 h2 : X) (t1 t2 : List X) HeqH HeqT =>
    match HeqH, HeqT with
    | eq.eq_refl h1, eq.eq_refl t1 => eq.eq_refl (h1 :: t1)

theorem equality__leibniz_equality : ∀ (X : Type) (x y: X),
    x === y → ∀ P : (X → Prop), P x → P y := by
  intro X x y Heq P HP
  cases Heq
  apply HP

theorem equality__leibniz_equality_term : ∀ (X : Type) (x y: X),
  x === y → ∀ (P : X → Prop), P x → P y :=
  fun (X : Type) (x y : X) Heq P HP =>
    match Heq with
    | eq.eq_refl x => HP

theorem leibniz_equality__equality : ∀ (X : Type) (x y: X),
  (∀ P : X → Prop, P x → P y) → x === y := by
  intro X x y H
  let P : X → Prop := fun z => x === z
  have Hxy : P y := H P (eq.eq_refl x)
  exact Hxy
  done

-- 別解
theorem leibniz_equality__equality' : ∀ (X : Type) (x y: X),
  (∀ P : X → Prop, P x → P y) → x === y := by
  intro X x y H
  apply H -- (fun z => x === z)
  apply eq.eq_refl

-- おまけ
@[simp] theorem eq_std_eq_iff : ∀ (X : Type) (x y : X), (x === y) ↔ (x = y) := by
  intro X x y
  constructor
  · intro Heq
    cases Heq
    rfl
  · intro Heq
    rw [Heq]
    apply eq.eq_refl

end EqualityPlayground

end Props

unsafe def infinite_loop {X : Prop} (n : Nat) : X :=
  infinite_loop n
 termination_by n

unsafe def falso : False := infinite_loop  0

#check And
#check Or

theorem my_and_assoc : ∀ P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  fun P Q R HPQR =>
    match HPQR with
    | And.intro HP (And.intro HQ HR) =>
      And.intro (And.intro HP HQ) HR

#check Iff

theorem or_distributes_over_and : ∀ P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
  fun P Q R =>
    Iff.intro
      (fun HPQR =>
        match HPQR with
        | Or.inl HP => And.intro (Or.inl HP) (Or.inl HP)
        | Or.inr (And.intro HQ HR) => And.intro (Or.inr HQ) (Or.inr HR))
      (fun H =>
        match H with
        | And.intro (Or.inl HP) _ => Or.inl HP
        | And.intro (Or.inr _) (Or.inl HP) => Or.inl HP
        | And.intro (Or.inr HQ) (Or.inr HR) => Or.inr (And.intro HQ HR))

#check Not

theorem double_neg : ∀ P : Prop,
  P → ¬¬P :=
  fun _P HP HNP =>
    HNP HP

theorem contradiction_implies_anything : ∀ P Q : Prop,
  (P ∧ ¬P) → Q :=
  fun P Q HPNP =>
    match HPNP with
    | And.intro HP HNP =>
      nomatch HNP HP

theorem de_morgan_not_or : ∀ P Q : Prop,
  ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
  fun _P _Q HNPQ =>
    And.intro
      (fun HP => HNPQ (Or.inl HP))
      (fun HQ => HNPQ (Or.inr HQ))

theorem curry : ∀ P Q R : Prop,
  ((P ∧ Q) → R) → (P → (Q → R)) :=
  fun _P _Q _R H HP HQ =>
    H (And.intro HP HQ)

theorem uncurry : ∀ P Q R : Prop,
  (P → (Q → R)) → ((P ∧ Q) → R) :=
  fun _P _Q _R H HPQ =>
    match HPQ with
    | And.intro HP HQ => H HP HQ

def propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q

theorem pe_implies_or_eq :
  propositional_extensionality →
  ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P) := by
  intro pe P Q
  apply pe
  constructor
  · intro HPQ
    cases HPQ
    case a.mp.inl HP =>
      apply Or.inr
      exact HP
    case a.mp.inr HQ =>
      apply Or.inl
      exact HQ
  · intro HQP
    cases HQP
    case a.mpr.inl HQ =>
      apply Or.inr
      exact HQ
    case a.mpr.inr HP =>
      apply Or.inl
      exact HP

theorem pe_implies_true_eq :
  propositional_extensionality →
  ∀ (P : Prop), P → True = P := by
  intro pe P HP
  apply pe
  constructor
  · intro HTrue
    exact HP
  · intro HP'
    exact True.intro

def proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2

theorem pe_implies_pi :
  propositional_extensionality → proof_irrelevance := by
  unfold propositional_extensionality
  intro pe P pf1 pf2
  have h1 := pe_implies_true_eq pe P pf1
  subst P
  cases pf1
  case intro =>
    cases pf2
    case intro =>
      rfl
