import Test.Basic
import Test.Induction
import Test.Logic

def div2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n + 2 => (div2 n) + 1

def csf (n : Nat) : Nat :=
  if evenb n then div2 n
  else (3 * n) + 1

partial def reaches1_in (n : Nat) : Nat :=
  if n == 1 then 0
  else 1 + reaches1_in (csf n)

#eval! reaches1_in 6
#eval! reaches1_in 19

partial def Collatz_holds_for_FAIL (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if evenb n
    then Collatz_holds_for_FAIL (div2 n)
    else Collatz_holds_for_FAIL ((3 * n) + 1)

inductive Collatz_holds_for : Nat → Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even
      (n : Nat)
      (heven : evenb n = true)
      (h : Collatz_holds_for (div2 n))
      : (Collatz_holds_for n)
  | Chf_odd
      (n : Nat)
      (hodd : evenb n = false)
      (h : Collatz_holds_for ((3 * n) + 1))
      : Collatz_holds_for n

open Collatz_holds_for in
example : Collatz_holds_for 12 := by
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_odd ; rfl ; simp
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_odd ; rfl ; simp
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_one
  done

inductive le : Nat → Nat → Prop where
  | le_n (n : Nat) : le n n
  | le_S (n m : Nat) : le n m → le n (m + 1)

-- ここからは標準の Nat.le を使う

#print Nat.le
#print Nat.le.refl
#print Nat.le.step

example : 3 ≤ 5 := by
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.refl
  done

inductive clos_trans {X: Type} (R: X → X → Prop) : X → X → Prop where
  | t_step
    {x y : X}
    (h : R x y)
    : clos_trans R x y
  | t_trans
    {x y z : X}
    (h1 : clos_trans R x y)
    (h2 : clos_trans R y z)
    : clos_trans R x z

inductive Person : Type where
  | Sage
  | Cleo
  | Ridley
  | Moss

inductive parent_of : Person → Person → Prop
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss

def ancestor_of : Person → Person → Prop :=
  clos_trans parent_of

example : ancestor_of .Sage .Moss := by
  unfold ancestor_of
  apply clos_trans.t_trans (y := .Cleo)
  · apply clos_trans.t_step
    apply parent_of.po_SC
  · apply clos_trans.t_step
    apply parent_of.po_CM

inductive clos_refl_trans
  {X: Type}
  (R: X → X → Prop)
  : X → X → Prop where
  | rt_step
    {x y : X}
    (h : R x y)
    : clos_refl_trans R x y
  | rt_refl
    {x : X}
    : clos_refl_trans R x x
  | rt_trans
    {x y z : X}
    (h1 : clos_refl_trans R x y)
    (h2 : clos_refl_trans R y z)
    : clos_refl_trans R x z

def cs (n m : Nat) : Prop := csf n = m

def cms n m := clos_refl_trans cs n m


inductive clos_refl_trans_sym
  {X: Type}
  (R: X → X → Prop)
  : X → X → Prop where
  | rt_step
    {x y : X}
    (h : R x y)
    : clos_refl_trans_sym R x y
  | rt_refl
    {x : X}
    : clos_refl_trans_sym R x x
  | rt_symm
    {x y : X}
    (h : clos_refl_trans_sym R x y)
    : clos_refl_trans_sym R y x
  | rt_trans
    {x y z : X}
    (h1 : clos_refl_trans_sym R x y)
    (h2 : clos_refl_trans_sym R y z)
    : clos_refl_trans_sym R x z

inductive Perm3 {X : Type} : List X → List X → Prop where
  | swap12 (a b c : X) :
      Perm3 [a, b, c] [b, a, c]
  | swap23 (a b c : X) :
      Perm3 [a, b, c] [a, c, b]
  | trans (l1 l2 l3 : List X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3

example : Perm3 [1, 2, 3] [3, 2, 1] := by
  apply Perm3.trans (l2 := [2, 3, 1])
  · apply Perm3.trans (l2 := [2, 1, 3])
    · apply Perm3.swap12
    · apply Perm3.swap23
  · apply Perm3.swap12
  done

example : Perm3 [1, 2, 3] [1, 2, 3] := by
  apply Perm3.trans (l2 := [1, 3, 2])
  · apply Perm3.swap23
  · apply Perm3.swap23
  done

#check Trans

inductive ev : Nat → Prop where
  | zero : ev 0
  | succ {n : Nat} (h : ev n) : ev (n + 2)

#check (ev.zero : ev 0)
#check (ev.succ ev.zero : ev 2)

namespace EvPlayground
  inductive ev : Nat → Prop where
    | ev_0 : ev 0
    | ev_SS : ∀ (n : Nat), ev n → ev (n + 2)
end EvPlayground

theorem ev_4 : ev 4 := by
  apply ev.succ
  apply ev.succ
  apply ev.zero
  done

theorem ev_4' : ev 4 := by
  apply (ev.succ (ev.succ ev.zero))
  done

theorem ev_plus4 : ∀ n, ev n → ev (n + 4) := by
  intro n h
  apply ev.succ
  apply ev.succ
  apply h
  done

theorem ev_double : ∀ n, ev (double n) := by
  intro n
  induction n
  case zero =>
    apply ev.zero
  case succ n ih =>
    apply ev.succ
    apply ih
  done

theorem ev_n_plus_n : ∀ n, ev (n + n) := by
  intro n
  rw [← myAdd_add, ← double_myAdd]
  apply ev_double

theorem Perm3_ex1 : Perm3 [1, 2, 3] [2, 3, 1] := by
  apply Perm3.trans (l2 := [2, 1, 3])
  · apply Perm3.swap12
  · apply Perm3.swap23
  done

theorem Perm3_refl : ∀ (X : Type) (a b c : X),
  Perm3 [a, b, c] [a, b, c] := by
  intro X a b c
  apply Perm3.trans (l2 := [a, c, b])
  · apply Perm3.swap23
  · apply Perm3.swap23
  done

theorem ev_inversion : ∀ (n : Nat),
  ev n →
  (n = 0) ∨ (∃ n', n = n' + 2 ∧ ev n') := by
  intro n h
  cases h
  case zero =>
    left
    rfl
  case succ n' h' =>
    right
    -- exists n'  -- 別解
    apply Exists.intro n'
    constructor
    case left =>
      rfl
    case right =>
      apply h'
  done

theorem le_inversion
  : ∀ (n m : Nat),
  n ≤ m →
  (n = m) ∨ (∃ m', m = m' + 1 ∧ n ≤ m') := by
  intro n m h
  cases h
  case refl =>
    left
    rfl
  case step m h' =>
    right
    apply Exists.intro m
    constructor
    case left =>
      rfl
    case right =>
      apply h'
  done

theorem evSS_ev : ∀ n, ev (n + 2) → ev n := by
  intro n h
  have h' := ev_inversion _ h
  rcases h' with (h0 | h1)
  · nomatch h0
  · rcases h1 with ⟨n', h2, h3⟩
    simp at h2
    rw [h2]
    apply h3
  done

theorem evSS_ev' : ∀ n, ev (n + 2) → ev n := by
  intro n h
  cases h
  case succ h' =>
    apply h'
    done

theorem one_not_even : ¬ ev 1 := by
  intro h
  have h' := ev_inversion _ h
  rcases h' with (h0 | ⟨m, hm, _⟩)
  · nomatch h0
  · nomatch hm

theorem one_not_even' : ¬ ev 1 := by
  intro h
  nomatch h

theorem SSSSev__even : ∀ n,
  ev (n + 4) → ev n := by
  intro n h
  rcases h with (_ | (_ | h'))
  exact h'

theorem ev5_nonsense :
  ev 5 → 2 + 2 = 9 := by
  intro h
  rcases h with (_ | (_ | h'))
  nomatch h'

theorem inversion_ex1 : ∀ (n m o : Nat),
  [n,  m] = [o,  o] → [n] = [m] := by
  intro n m o h
  cases h
  rfl

theorem inversion_ex2 : ∀ (n : Nat),
  n + 1 = 0 → 2 + 2 = 5 := by
  intro n contra
  cases contra
  done

theorem ev_Even_firsttry : ∀ n, ev n → Even n := by
  unfold Even
  intro n h
  rcases h with (heq | ⟨n', h1, heq⟩)
  · exists 0
  · exists 1
  · sorry

theorem ev_Even : ∀ n,
  ev n → Even n := by
  unfold Even
  intro n E
  induction E
  case zero =>
    exists 0
  case succ n' E' ih =>
   cases ih
   case intro k hk =>
      exists (k + 1)
      rw [hk, Nat.add_mul]
  done

theorem ev_Even_iff : ∀ n,
  ev n ↔ Even n := by
  intro n
  constructor
  case mp =>
    apply ev_Even
  case mpr =>
    unfold Even
    intro k
    cases k
    case intro k' hk =>
      rw [hk]
      rw [← double_mul]
      apply ev_double


-- inductive ev : Nat → Prop where
--   | zero : ev 0
--   | succ {n : Nat} (h : ev n) : ev (n + 2)

theorem ev_sum : ∀ n m,
  ev n → ev m → ev (n + m) := by
  intro n m en em
  induction em
  case zero =>
    exact en
  case succ m' em' =>
    apply ev.succ
    exact em'
  -- induction en
  -- case zero =>
  --   simp
  --   exact em
  -- case succ n' en' e_n'_m =>
  --   apply ev.succ

theorem ev_ev__ev : ∀ n m,
  ev (n + m) → ev n → ev m := by
  intro n m enm en
  induction en
  case zero =>
    simp at enm
    exact enm
  case succ n' en' =>
    rw [
      Nat.add_assoc,
      Nat.add_comm 2 m,
      ← Nat.add_assoc,
      ] at enm
    cases enm
    case succ h =>
      exact en' h

theorem ev_plus_plus : ∀ n m p,
  ev (n + m) → ev (n + p) → ev (m + p) := by
  intro n m p enm enp
  have enmnp := ev_sum _ _ enm enp
  have enn : ev (n + n) := by
    apply ev_n_plus_n
  have nnmp : n + m + (n + p) = n + n + (m + p) := by
    simp_arith
  rw [nnmp] at enmnp
  exact ev_ev__ev _ _ enmnp enn

inductive ev' : Nat → Prop where
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m)

theorem ev'_ev : ∀ n, ev' n ↔ ev n := by
  intro n
  constructor
  case mp =>
    intro h
    induction h
    case ev'_0 =>
      exact ev.zero
    case ev'_2 =>
      exact ev.succ ev.zero
    case ev'_sum Hn Hm Hn_ih Hm_ih =>
      apply ev_sum _ _ Hn_ih Hm_ih
      done

  case mpr =>
    intro h
    induction h
    case zero =>
      exact ev'.ev'_0
    case succ n' Hn_ih =>
      apply ev'.ev'_sum
      case Hn =>
        exact Hn_ih
      case Hm =>
        exact ev'.ev'_2
      done

theorem Perm3_symm : ∀ (X : Type) (l1 l2 : List X),
  Perm3 l1 l2 → Perm3 l2 l1 := by
  intro X l1 l2 E
  induction E
  case swap12 a b c =>
    apply Perm3.swap12
  case swap23 a b c =>
    apply Perm3.swap23
  case trans l1 l2 l3 E12 E23 IH12 IH23 =>
    --                ^^^^^^^^^^^^^^^^^
    --          引数の順番がRocqと違うので注意！
    apply (Perm3.trans _ l2 _)
    · apply IH23
    · apply IH12

theorem Perm3_In : ∀ (X : Type) (x : X) (l1 l2 : List X),
    Perm3 l1 l2 → In x l1 → In x l2 := by
  intro X x l1 l2 E h
  induction E
  case swap12 a b c =>
    rcases h with (h_ax | h_bx | h_cx | h_)
    · rw [h_ax]
      simp [In]
    · rw [h_bx]
      simp [In]
    · rw [h_cx]
      simp [In]
    · nomatch h_
  case swap23 a b c =>
    rcases h with (h_ax | h_bx | h_cx | h_)
    · rw [h_ax]
      simp [In]
    · rw [h_bx]
      simp [In]
    · rw [h_cx]
      simp [In]
    · nomatch h_
  case trans l1 l2 l3 E12 E23 IH12 IH23 =>
    apply IH23
    apply IH12
    exact h

-- all_goals・rotate_right を使った別解
theorem Perm3_In2 : ∀ (X : Type) (x : X) (l1 l2 : List X),
    Perm3 l1 l2 → In x l1 → In x l2 := by
  intro X x l1 l2 E h
  induction E
  case trans l1 l2 l3 E12 E23 IH12 IH23 =>
    apply IH23
    apply IH12
    exact h
  all_goals
    rcases h with (h_x | h_x | h_x | h_)
    rotate_right
    nomatch h_
    all_goals
      rw [h_x]
      simp [In]

theorem Perm3_NotIn : ∀ (X : Type) (x : X) (l1 l2 : List X),
  Perm3 l1 l2 → ¬In x l1 → ¬In x l2 := by
  intro X x l1 l2 E h h'
  apply h
  apply Perm3_In _ _ l2 l1
  · apply Perm3_symm
    exact E
  · exact h'

-- 別解
theorem Perm3_NotIn' : ∀ (X : Type) (x : X) (l1 l2 : List X),
  Perm3 l1 l2 → ¬In x l1 → ¬In x l2 := by
  intro X x l1 l2 E h

  have lemma12 : ∀ (x a b c : X), In x [a, b, c] ↔ In x [b, a, c] := by
    intro x a b c
    constructor
    case mp =>
      intro h'
      rcases h' with (h_ax | h_bx | h_cx | h_)
      · rw [h_ax]
        simp [In]
      · rw [h_bx]
        simp [In]
      · rw [h_cx]
        simp [In]
      · nomatch h_
    case mpr =>
      intro h'
      rcases h' with (h_ax | h_bx | h_cx | h_)
      · rw [h_ax]
        simp [In]
      · rw [h_bx]
        simp [In]
      · rw [h_cx]
        simp [In]
      · nomatch h_

  have lemma23 : ∀ (x a b c : X), In x [a, b, c] ↔ In x [a, c, b] := by
    intro x a b c
    constructor
    case mp =>
      intro h'
      rcases h' with (h_ax | h_bx | h_cx | h_)
      · rw [h_ax]
        simp [In]
      · rw [h_bx]
        simp [In]
      · rw [h_cx]
        simp [In]
      · nomatch h_
    case mpr =>
      intro h'
      rcases h' with (h_ax | h_bx | h_cx | h_)
      · rw [h_ax]
        simp [In]
      · rw [h_bx]
        simp [In]
      · rw [h_cx]
        simp [In]
      · nomatch h_

  induction E
  case swap12 a b c =>
    rw [lemma12]
    exact h
  case swap23 a b c =>
    rw [lemma23]
    exact h
  case trans l1 l2 l3 E12 E23 IH12 IH23 =>
    apply IH23
    apply IH12
    exact h
    done

theorem Perm3_example2 : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  intro h
  -- theorem Perm3_In : ∀ (X : Type) (x : X) (l1 l2 : List X),
  --     Perm3 l1 l2 → In x l1 → In x l2 := by
  have h1 : In 3 [1, 2, 3] := by
    simp [In]
  have h2 : In 3 [1, 2, 4] :=
    Perm3_In _ 3 [1, 2, 3] [1, 2, 4] h h1
  simp [In] at h2

-- 大変な別解（未解決））
theorem Perm3_example2' : ¬ Perm3 [1, 2, 3] [1, 2, 4] := by
  generalize h1 : [1, 2, 3] = l1
  generalize h3 : [1, 2, 4] = l3
  intro h
  induction h
  case swap12 a b c =>
    simp at h1 h3
    rcases h1 with ⟨_, _, h3c⟩
    rcases h3 with ⟨_, _, h4c⟩
    rw [← h3c] at h4c
    nomatch h4c
  case swap23 a b c =>
    simp at h1 h3
    rcases h1 with ⟨_, h2b, _⟩
    rcases h3 with ⟨_, _, h4b⟩
    rw [← h2b] at h4b
    nomatch h4b
  case trans l1 l2 l3 E12 E23 IH12 IH23 =>
    specialize IH12 h1
    have IH23' := fun h => IH23 h h3
    sorry

#print Nat.le
/-   n
  0 1 2 3 4
0 o
1 o o
2 o o o
3 o o o o
4 o o o o o
-/

theorem test_le1 :
  3 ≤ 3 := by
  apply Nat.le.refl
  done

theorem test_le2 :
  3 ≤ 6 := by
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.refl
  done

theorem test_le3 :
  (2 ≤ 1) → 2 + 2 = 5 := by
  intro h
  cases h
  case step h' =>
    nomatch h'
  done

def lt (n m : Nat) := le n.succ m

#print Nat.lt

def ge (m n : Nat) : Prop := le n m

-- Nat.ge はない
