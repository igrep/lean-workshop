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
    simp +arith
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
#print Nat.le

def ge (m n : Nat) : Prop := le n m

-- Nat.ge はない

theorem le_trans : ∀ m n o : Nat,
  m ≤ n → n ≤ o → m ≤ o := by
  intro m n o hmn hno
  induction hno
  case refl =>
    exact hmn
  case step n' hno' ih =>
    apply Nat.le.step
    exact ih

theorem O_le_n : ∀ n : Nat,
  0 ≤ n := by
  intro n
  induction n
  case zero =>
    exact Nat.le.refl
  case succ n' ih =>
    exact Nat.le.step ih

theorem n_le_m__Sn_le_Sm : ∀ n m : Nat,
  n ≤ m → n + 1 ≤ m + 1 := by
  intro n m h
  induction h
  case refl =>
    exact Nat.le.refl
  case step n' h' ih =>
    exact Nat.le.step ih

theorem Sn_le_Sm__n_le_m : ∀ n m : Nat,
  n + 1 ≤ m + 1 → n ≤ m := by
  intro n m h
  induction m
  case zero =>
    cases h
    case refl =>
      exact Nat.le.refl
    case step h' =>
      nomatch h'
  case succ m' ih =>
    cases h
    case refl =>
      exact Nat.le.refl
    case step h' =>
      apply Nat.le.step
      apply ih h'

theorem le_plus_l : ∀ a b : Nat,
  a ≤ a + b := by
  intro a b
  induction b
  case zero =>
    exact Nat.le.refl
  case succ b' ih =>
    apply Nat.le.step
    exact ih

theorem plus_le : ∀ n1 n2 m : Nat,
  n1 + n2 ≤ m →
  n1 ≤ m ∧ n2 ≤ m := by
  intro n1 n2 m h
  induction h
  case refl =>
    constructor
    · apply le_plus_l
    · rw [Nat.add_comm]
      apply le_plus_l
  case step n h ih =>
    constructor
    · apply Nat.le.step
      apply ih.left
    · apply Nat.le.step
      exact ih.right
  done

theorem plus_le_cases : ∀ n m p q : Nat,
  n + m ≤ p + q → n ≤ p ∨ m ≤ q := by
  intro n m p q h
  induction q generalizing n m p
  case zero =>
    simp at h
    have h' := plus_le _ _ _ h
    left
    exact h'.left
  case succ q' ih =>
    cases m
    case zero =>
      right
      apply O_le_n
    case succ m' =>
      have h' : n + m' ≤ p + q' := by
        apply Sn_le_Sm__n_le_m
        exact h
      specialize ih _ _ _ h'
      cases ih
      case inl hl =>
        left
        exact hl
      case inr hr =>
        right
        apply n_le_m__Sn_le_Sm
        exact hr
  done

-- Lean的にはplus_le_compat_rの方が解きやすそうなので先に
theorem plus_le_compat_r : ∀ n m p : Nat,
  n ≤ m →
  n + p ≤ m + p := by
  intro n m p h
  induction h
  case refl =>
    apply Nat.le.refl
  case step n' h' ih =>
    rw [Nat.succ_add]
    apply Nat.le.step
    apply ih

theorem plus_le_compat_l : ∀ n m p : Nat,
  n ≤ m → p + n ≤ p + m := by
  intro n m p h
  rw [Nat.add_comm p n, Nat.add_comm p m]
  apply plus_le_compat_r
  exact h

theorem le_plus_trans : ∀ n m p : Nat,
  n ≤ m →
  n ≤ m + p := by
  intro n m p h
  induction p
  case zero =>
    exact h
  case succ p' ih =>
    apply Nat.le.step
    exact ih

theorem le_plus_trans_r : ∀ n m p : Nat,
  n ≤ m →
  n ≤ p + m := by
  intro n m p h
  rw [Nat.add_comm p m]
  apply le_plus_trans
  exact h

theorem lt_ge_cases : ∀ n m : Nat,
  n < m ∨ n ≥ m := by
  intro n m
  rw [ ← Nat.add_one_le_iff
     , ge_iff_le
     ]
  induction m generalizing n
  case zero =>
    simp
  case succ m' ih =>
    cases n
    case zero =>
      left
      apply n_le_m__Sn_le_Sm
      apply O_le_n
    case succ n' =>
      specialize ih n'
      cases ih
      case inl h =>
        left
        apply n_le_m__Sn_le_Sm
        exact h
      case inr h =>
        right
        apply n_le_m__Sn_le_Sm
        exact h

theorem n_lt_m__n_le_m : ∀ n m : Nat,
  n < m →
  n ≤ m := by
  intro n m h
  rw [← Nat.add_one_le_iff] at h
  induction h
  case refl =>
    apply Nat.le.step
    apply Nat.le.refl
  case step n' h' ih =>
    apply Nat.le.step
    apply ih

theorem plus_lt : ∀ n1 n2 m : Nat,
  n1 + n2 < m →
  n1 < m ∧ n2 < m := by
  simp only [← Nat.add_one_le_iff]
  intro n1 n2 m h
  have h1 := plus_le (n1 + 1) n2 m (by
    rw [show n1 + n2 + 1 = n1 + 1 + n2 from by ac_rfl] at h
    exact h)
  have h2 := plus_le n1 (n2 + 1) m h
  exact And.intro h1.left h2.right

#check Nat.ble
theorem leb_complete : ∀ n m : Nat,
  n.ble m = true → n ≤ m := by
  intro n m h
  induction m generalizing n
  case zero =>
    cases n
    case zero =>
      apply Nat.le.refl
    case succ n' =>
      unfold Nat.ble at h
      contradiction
  case succ m' ih =>
    cases n
    case zero =>
      apply O_le_n
    case succ n' =>
      unfold Nat.ble at h
      specialize ih _ h
      apply n_le_m__Sn_le_Sm
      exact ih
  done

theorem leb_correct : ∀ n m : Nat,
  n ≤ m → n.ble m = true := by
  intro n m h
  induction m generalizing n
  case zero =>
    cases n
    case zero =>
      rfl
    case succ n' =>
      contradiction
  case succ m' ih =>
    cases n
    case zero =>
      rfl
    case succ n' =>
      unfold Nat.ble
      apply ih
      apply Sn_le_Sm__n_le_m
      exact h


inductive R : Nat → Nat → Nat → Prop where
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o ) : R m.succ n o.succ
  | c3 m n o (H : R m n o ) : R m n.succ o.succ
  | c4 m n o (H : R m.succ n.succ o.succ.succ) : R m n o
  | c5 m n o (H : R m n o ) : R n m o

example : R 1 1 2 := by
  apply R.c3
  apply R.c2
  exact R.c1
  done

-- m + n = o になる、という関係なので、該当しない！
example : R 2 2 6 := by
  sorry
  done

inductive R_no_c5 : Nat → Nat → Nat → Prop where
  | c1 : R_no_c5 0 0 0
  | c2 m n o (H : R_no_c5 m n o ) : R_no_c5 m.succ n o.succ
  | c3 m n o (H : R_no_c5 m n o ) : R_no_c5 m n.succ o.succ
  | c4 m n o (H : R_no_c5 m.succ n.succ o.succ.succ) : R_no_c5 m n o

example : R_no_c5 1 2 3 := by
  apply R_no_c5.c3
  apply R_no_c5.c3
  apply R_no_c5.c2
  exact R_no_c5.c1
  done

example : R_no_c5 2 1 3 := by
  apply R_no_c5.c2
  apply R_no_c5.c2
  apply R_no_c5.c3
  exact R_no_c5.c1
  done

def fR (m n : Nat) : Nat := m + n

theorem R_o_0_o : ∀ o, R o 0 o := by
  intro o
  induction o
  case zero =>
    exact R.c1
  case succ o' ih =>
    apply R.c2
    exact ih
  done

theorem R_0_o_o : ∀ o, R 0 o o := by
  intro o
  induction o
  case zero =>
    exact R.c1
  case succ o' ih =>
    apply R.c3
    exact ih
  done

theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o := by
  intro m n o
  constructor
  case mp =>
    intro h
    induction h
    case c1 =>
      rfl
    case c2 m' n' o' h' hfR =>
      simp [fR]
      simp [fR] at hfR
      omega
    case c3 m' n' o' h' hfR =>
      simp [fR]
      simp [fR] at hfR
      omega
    case c4 m' n' o' h' hfR =>
      simp [fR]
      simp [fR] at hfR
      omega
    case c5 m' n' o' h' hfR =>
      simp [fR]
      simp [fR] at hfR
      rw [Nat.add_comm]
      exact hfR
  case mpr =>
    intro h
    unfold fR at h
    induction o generalizing m n
    case zero =>
      cases m
      case zero =>
        cases n
        case zero =>
          exact R.c1
        case succ n' =>
          nomatch h
      case succ m' =>
        simp at h
    case succ o' ih =>
      cases m
      case zero =>
        rw [← h]
        simp
        apply R_0_o_o
      case succ m' =>
        apply R.c2
        apply ih
        omega


inductive Subseq : List Nat → List Nat → Prop where
  | nil : Subseq [] []
  | cons (x : Nat) (l1 l2 : List Nat)
      (h : Subseq l1 l2) : Subseq (x :: l1) (x :: l2)
  | skip (x : Nat) (l1 l2 : List Nat)
      (h : Subseq l1 l2) : Subseq l1 (x :: l2)

theorem subseq_refl : ∀ l : List Nat,
  Subseq l l := by
  intro l
  induction l
  case nil =>
    exact Subseq.nil
  case cons x l ih =>
    apply Subseq.cons
    exact ih
  done

theorem subseq_nil_l : ∀ l : List Nat,
  Subseq [] l := by
  intro l
  induction l
  case nil =>
    exact Subseq.nil
  case cons x l ih =>
    apply Subseq.skip
    exact ih
  done

theorem subseq_app : ∀ l1 l2 l3 : List Nat,
  Subseq l1 l2 → Subseq l1 (l2 ++ l3) := by
  intro l1 l2 l3 h
  induction h
  case nil =>
    apply subseq_nil_l
  case cons x l1' l2' h' ih =>
    apply Subseq.cons
    apply ih
  case skip x l1' l2' h' ih =>
    apply Subseq.skip
    apply ih
  done

theorem subseq_app_right : ∀ l1 l2 l3 : List Nat,
  Subseq l1 l3 → Subseq l1 (l2 ++ l3) := by
  intro l1 l2 l3 h
  induction l2
  case nil =>
    exact h
  case cons x l2' ih =>
    apply Subseq.skip
    exact ih

theorem subseq_cons : ∀ (x : Nat) (l1 l2 : List Nat),
  Subseq (x :: l1) l2 → Subseq l1 l2 := by
  intro x l1 l2 h
  induction l2 generalizing l1
  case nil =>
    nomatch h
  case cons y l2' ih =>
    apply Subseq.skip
    cases h
    case h.cons h' =>
      exact h'
    case h.skip h' =>
      exact ih l1 h'

theorem subseq_split
  : ∀ {x : Nat} {l1 l2 : List Nat},
  Subseq (x :: l1) l2 →
  ∃ (l2₁ l2₂ : List Nat),
    (l2 = l2₁ ++ x :: l2₂) ∧ Subseq l1 l2₂ := by
  intro x l1 l2 h
  induction l2 generalizing l1
  case nil =>
    nomatch h
  case cons y l2' ih =>
    cases h
    case cons h' =>
      exists []
      exists l2'
    case skip h' =>
      rcases ih h' with ⟨l2₁, l2₂, ⟨h_eq, h_sub⟩⟩
      -- exact ⟨y :: l2₁, l2₂, ⟨by rw [h_eq]; rfl, h_sub⟩⟩
      exists (y :: l2₁)
      exists l2₂
      constructor
      case left =>
        rw [h_eq]
        rfl
      case right =>
        exact h_sub
  done

theorem subseq_trans : ∀ l1 l2 l3 : List Nat,
  Subseq l1 l2 → Subseq l2 l3 → Subseq l1 l3 := by
  intro l1 l2 l3 h12 h23
  induction h12 generalizing l3
  case nil =>
    apply subseq_nil_l
  case cons x l1' l2' h' ih =>
    have ⟨l3₁, l3₂, l3_eq, h⟩ := subseq_split h23
    have ih' := Subseq.cons x _ _ (ih l3₂ h)
    rw [l3_eq]
    apply subseq_app_right
    exact ih'
  case skip x l1' l2' h' ih =>
    have ⟨l3₁, l3₂, l3_eq, h⟩ := subseq_split h23
    have ih' := Subseq.skip x _ _ (ih l3₂ h)
    rw [l3_eq]
    apply subseq_app_right
    exact ih'
  done

namespace RProvability2
inductive R : Nat → List Nat → Prop where
  | c1                        : R 0        []
  | c2 n l (H: R n        l) : R (n.succ) (n :: l)
  | c3 n l (H: R (n.succ) l) : R n        l

example : R 2 [1, 0] := by
  apply R.c2
  apply R.c2
  apply R.c1

example : R 1 [1, 2, 1, 0] := by
  apply R.c3
  apply R.c2
  apply R.c3
  apply R.c3
  apply R.c2
  apply R.c2
  apply R.c2
  apply R.c1

example : R 6 [3, 2, 1, 0] := by
  apply R.c3
  sorry

end RProvability2

inductive total_relation : Nat → Nat → Prop where
  | intro (n m : Nat) : total_relation n m

theorem total_relation_is_total
  : ∀ n m, total_relation n m := by
  intro n m
  constructor

inductive empty_relation : Nat → Nat → Prop where
  -- no constructor

theorem empty_relation_is_empty
  : ∀ n m, ¬ empty_relation n m := by
  intro n m h
  nomatch h


inductive reg_exp (T : Type) : Type where
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T)


inductive exp_match {T} : List T → reg_exp T → Prop where
  | MEmpty : exp_match [] .EmptyStr
  | MChar x : exp_match [x] (.Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2)
           : exp_match (s1 ++ s2) (.App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1)
              : exp_match s1 (.Union re1 re2)
  | MUnionR s2 re1 re2
                (H2 : exp_match s2 re2)
              : exp_match s2 (.Union re1 re2)
  | MStar0 re : exp_match [] (.Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (.Star re))
               : exp_match (s1 ++ s2) (.Star re)

infix:50 " =~ " => exp_match
#check ['a'] =~ .Char 'a'
#check "aaaaa".toList =~ (reg_exp.Char 'a').Star

theorem reg_exp_ex1 : [1] =~ .Char 1 := by
  apply exp_match.MChar

theorem reg_exp_ex2 : [1, 2] =~ .App (.Char 1) (.Char 2) := by
  apply exp_match.MApp [1]
  · apply exp_match.MChar
  · apply exp_match.MChar

theorem reg_exp_ex3 : ¬ ([1, 2] =~ .Char 1) := by
  generalize h1 : [1, 2] = s
  intro h
  cases h
  nomatch h1

def reg_exp_of_list {T} (l : List T) : reg_exp T :=
  match l with
  | [] => .EmptyStr
  | x :: l' => .App (.Char x) (reg_exp_of_list l')

example : [1, 2, 3] =~ reg_exp_of_list [1, 2, 3] := by
  simp [reg_exp_of_list]
  apply exp_match.MApp [1]
  · apply exp_match.MChar
  · apply exp_match.MApp [2]
    · apply exp_match.MChar
    · apply exp_match.MApp [3]
      · apply exp_match.MChar
      · apply exp_match.MEmpty
  done

theorem MStar1 :
  ∀ T s (re : reg_exp T) ,
    s =~ re →
    s =~ .Star re := by
  intro T s re h
  rw [← List.append_nil s]
  apply exp_match.MStarApp
  · exact h
  · apply exp_match.MStar0

theorem EmptySet_is_empty : ∀ T (s : List T),
  ¬ (s =~ .EmptySet) := by
  intro T s h
  cases h
  done

theorem MUnion' : ∀ T (s : List T) (re1 re2 : reg_exp T),
  s =~ re1 ∨ s =~ re2 →
  s =~ .Union re1 re2 := by
  intro T s re1 re2 h
  cases h
  case inl h1 =>
    apply exp_match.MUnionL
    exact h1
  case inr h2 =>
    apply exp_match.MUnionR
    exact h2

theorem MStar'_lemma
  : ∀ T (ss ss1 ss2 : List (List T)) (re : reg_exp T),
  ss = ss1 ++ ss2 →
  (∀ s, In s ss → s =~ re) →
  fold (· ++ ·) ss2 [] =~ .Star re := by
  intro T ss ss1 ss2 re h_eq h
  induction ss2 generalizing ss1
  case nil =>
    apply exp_match.MStar0
  case cons s ss2' ih =>
    rw [fold]
    apply exp_match.MStarApp
    · apply h
      rw [h_eq, In_app_iff]
      right
      left
      rfl
    · apply ih (ss1 ++ [s])
      rw [h_eq, List.append_assoc]
      rfl


theorem MStar' : ∀ T (ss : List (List T)) (re : reg_exp T),
  (∀ s, In s ss → s =~ re) →
  fold (· ++ ·) ss [] =~ .Star re := by
  intro T ss re h
  apply MStar'_lemma T ss [] ss re rfl h


def EmptyStr' {T : Type} := reg_exp.Star (T := T) .EmptySet

theorem EmptyStr_eq_EmptyStr' : ∀ (T : Type) (s : List T),
  s =~ .EmptyStr ↔ s =~ EmptyStr' := by
  intro T s
  constructor
  case mp =>
    intro h
    cases h
    apply exp_match.MStar0
  case mpr =>
    intro h
    cases h
    case MStar0 =>
      apply exp_match.MEmpty
    case MStarApp s1 s2 h1 h2 =>
      cases h1
  done


def re_chars {T} (re : reg_exp T) : List T :=
  match re with
  | .EmptySet => []
  | .EmptyStr => []
  | .Char x => [x]
  | .App re1 re2 => re_chars re1 ++ re_chars re2
  | .Union re1 re2 => re_chars re1 ++ re_chars re2
  | .Star re => re_chars re

theorem in_re_match
  : ∀ T (s : List T) (re : reg_exp T) (x : T),
  s =~ re →
  In x s →
  In x (re_chars re) := by
  intro T s re x h_match h_in
  induction h_match
  case MEmpty =>
    cases h_in
  case MChar y =>
    unfold re_chars
    exact h_in
  case MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    unfold re_chars
    rw [In_app_iff] at h_in ⊢
    cases h_in
    case inl h =>
      left
      exact ih1 h
    case inr h =>
      right
      exact ih2 h
  case MUnionL s1 re1 re2 h1 ih1 =>
    unfold re_chars
    rw [In_app_iff]
    left
    apply ih1 h_in
  case MUnionR s2 re1 re2 h2 ih2 =>
    unfold re_chars
    rw [In_app_iff]
    right
    apply ih2 h_in
  case MStar0 re =>
    cases h_in
  case MStarApp s1 s2 re h1 h2 ih1 ih2 =>
    unfold re_chars
    rw [In_app_iff] at h_in
    cases h_in
    case inl h =>
      apply ih1 h
    case inr h =>
      apply ih2 h
  done


-- tests whether a regular expression matches some string.
def re_not_empty {T : Type} (re : reg_exp T) : Bool :=
  match re with
  | .EmptySet => false
  | .EmptyStr => true
  | .Char _x => true
  | .App re1 re2 => re_not_empty re1 && re_not_empty re2
  | .Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | .Star _re => true

theorem re_not_empty_correct : ∀ T (re : reg_exp T),
  (∃ s, s =~ re) ↔ re_not_empty re := by
  intro T re
  constructor
  case mp =>
    intro ⟨s, h_match⟩
    induction h_match
    case MEmpty =>
      rfl
    case MChar x =>
      rfl
    case MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
      unfold re_not_empty
      rw [ih1, ih2]
      rfl
    case MUnionL s1 re1 re2 h1 ih1 =>
      unfold re_not_empty
      rw [ih1]
      rfl
    case MUnionR s2 re1 re2 h2 ih2 =>
      unfold re_not_empty
      rw [ih2]
      simp
    case MStar0 re =>
      rfl
    case MStarApp s1 s2 re h1 h2 ih1 ih2 =>
      unfold re_not_empty
      rfl
  case mpr =>
    intro h
    induction re
    case EmptySet =>
      cases h
    case EmptyStr =>
      exists []
      apply exp_match.MEmpty
    case Char x =>
      exists [x]
      apply exp_match.MChar
    case App re1 re2 ih1 ih2 =>
      simp_all [re_not_empty]
      rcases ih1 with ⟨s1, h1⟩
      rcases ih2 with ⟨s2, h2⟩
      exists (s1 ++ s2)
      apply exp_match.MApp _ _ _ _ h1 h2
    case Union re1 re2 ih1 ih2 =>
      simp_all [re_not_empty]
      cases h
      case inl h1 =>
        rcases ih1 h1 with ⟨s1, h1'⟩
        exists s1
        apply exp_match.MUnionL _ _ _ h1'
      case inr h2 =>
        rcases ih2 h2 with ⟨s2, h2'⟩
        exists s2
        apply exp_match.MUnionR _ _ _ h2'
    case Star re ih =>
      exists []
      apply exp_match.MStar0


theorem star_app_sorry: ∀ T (s1 s2 : List T) (re : reg_exp T),
  s1 =~ .Star re →
  s2 =~ .Star re →
  s1 ++ s2 =~ .Star re := by
  intro T s1 s2 re h1
  -- induction h1
  sorry

theorem star_app: ∀ T (s1 s2 : List T) (re : reg_exp T),
  s1 =~ re.Star →
  s2 =~ re.Star →
  s1 ++ s2 =~ re.Star := by
  intro T s1 s2 re h1
  generalize Eq : re.Star = re' at h1
  induction h1
  case MEmpty =>
    contradiction
  case MChar x =>
    contradiction
  case MApp s1' re1 s2' re2 h1' h2 ih1 ih2 =>
    contradiction
  case MUnionL s1' re1 re2 h1' ih1 =>
    contradiction
  case MUnionR s2' re1 re2 h2' ih2 =>
    contradiction
  case MStar0 re'' =>
    intro h2
    apply h2
  case MStarApp s1' s2' re'' h1' h2' ih1 ih2 =>
    intro h2
    rw [List.append_assoc]
    apply exp_match.MStarApp
    · apply h1'
    · apply ih2
      · apply Eq
      · apply h2
  done

#check List.flatten

-- ∃ ss, s1 ++ (s2 ++ s) =
-- fold (fun x1 x2 => x1 ++ x2) ss []
-- ∧ ∀ (s' : List T), In s' ss → s' =~ re
theorem MStar''_lemma
  : ∀ T (xs : List (List T)) (s : List T) (re : reg_exp T),
  (∀ x, In x xs → x =~ re) →
  s =~ re.Star →
  ∃ ss : List (List T),
    (xs.flatten ++ s) = ss.flatten
    ∧ ∀ s', In s' ss → s' =~ re := by
  intro T xs s re hx hs
  generalize re_h : re.Star = re' at hs
  induction hs generalizing xs
  case MStar0 re'' =>
    exists xs
    constructor
    · simp
    · exact hx
  case MStarApp s1 s2 re'' h1 h2 ih1 ih2 =>
    injection re_h with re_eq
    specialize ih2 (xs ++ [s1])
    -- ih1: In x xs → x =~ re → re.Star = re''
    -- ih2: In x (xs ++ [s1]) → x =~ re → re.Star = re''.Star

    -- ih1:  xs         .flatten ++  s1        = ss.flatten ∧ ∀ (s' : List T), In s' ss → s' =~ re
    -- ih2: (xs ++ [s1]).flatten ++        s2  = ss.flatten ∧ ∀ (s' : List T), In s' ss → s' =~ re
    -- ⊢     xs         .flatten ++ (s1 ++ s2) = ss.flatten ∧ ∀ (s' : List T), In s' ss → s' =~ re
    simp [List.append_assoc] at ih2
    apply ih2 ?ih2_pr re_eq
    case ih2_pr =>
      intro x h_in
      rw [In_app_iff] at h_in
      cases h_in
      case inl h =>
        apply hx
        exact h
        done
      case inr h =>
        simp [In] at h
        rw [← h]
        rw [re_eq]
        exact h1
  all_goals contradiction

theorem MStar'' : ∀ T (s : List T) (re : reg_exp T),
  s =~ reg_exp.Star re →
  ∃ ss : List (List T),
    s = fold (· ++ ·) ss []
    ∧ ∀ s', In s' ss → s' =~ re := by
  intro T s re h
  have := MStar''_lemma T [] s re (fun x h => False.elim h) h
  simp at this
  cases this
  case intro w h =>
    exists w
    rw [fold_append_eq_flatten]
    exact h
  done

-- 恐らくこれが想定解
theorem MStar''2  : ∀ T (s : List T) (re : reg_exp T),
  s =~ reg_exp.Star re →
  ∃ ss : List (List T),
    s = fold (· ++ ·) ss []
    ∧ ∀ s', In s' ss → s' =~ re := by
  intro T s re h
  generalize re_eq : re.Star = re' at h
  induction h
  any_goals contradiction
  case MStar0 re'' =>
    injection re_eq with re_eq'
    exists []
    constructor
    · simp
      rfl
    · intro s' h_in
      nomatch h_in
  case MStarApp s1 s2 re'' h1 h2 ih1 ih2 =>
    have ⟨ss, ih2_h1, h2⟩ := ih2 re_eq
    exists s1 :: ss
    constructor
    · rw [ih2_h1]
      rfl
    · intro s' h
      cases h
      case inl inl_h =>
        rw [← inl_h]
        injection re_eq with re_eq'
        rw [← re_eq'] at h1
        exact h1
      case inr inr_h =>
        exact h2 s' inr_h
  done


#print Exists


def pumping_constant {T} (re : reg_exp T) : Nat :=
  match re with
  | .EmptySet => 1
  | .EmptyStr => 1
  | .Char _ => 2
  | .App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | .Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | .Star r => pumping_constant r

theorem pumping_constant_ge_1 :
  ∀ T (re : reg_exp T),
    pumping_constant re ≥ 1 := by
  intro T re
  induction re
  case EmptySet =>
    simp [pumping_constant]
  case EmptyStr =>
    simp [pumping_constant]
  case Char x =>
    simp [pumping_constant]
  case App re1 re2 ih1 ih2 =>
    simp [pumping_constant]
    apply le_plus_trans
    apply ih1
  case Union re1 re2 ih1 ih2 =>
    simp [pumping_constant]
    apply le_plus_trans
    apply ih1
  case Star r ih =>
    simp [pumping_constant]
    apply ih

theorem pumping_constant_0_false :
  ∀ T (re : reg_exp T),
    pumping_constant re = 0 → False := by
  intro T re h
  have h1 := pumping_constant_ge_1 T re
  rw [h] at h1
  simp at h1

def napp {T} (n : Nat) (l : List T) : List T :=
  match n with
  | 0 => []
  | n' + 1 => l ++ napp n' l

theorem napp_plus : ∀ T (n : Nat) (m : Nat) (l : List T),
  napp (n + m) l = napp n l ++ napp m l := by
  intro T n m l
  induction n
  case zero =>
    simp
    rfl
  case succ n' ih =>
    rw [show n' + 1 + m = (n' + m) + 1 from by ac_rfl]
    simp [napp]
    exact ih

theorem napp_star :
  ∀ T m s1 s2 (re : reg_exp T),
    s1 =~ re → s2 =~ re.Star →
    napp m s1 ++ s2 =~ re.Star := by
  intro T m s1 s2 re h1 h2
  induction m
  case zero =>
    exact h2
  case succ m' ih =>
    simp [napp]
    apply exp_match.MStarApp
    · exact h1
    · exact ih

theorem weak_pumping : ∀ T (re : reg_exp T) s,
  s =~ re →
  pumping_constant re ≤ length s →
  ∃ s1 s2 s3,
    s = s1 ++ s2 ++ s3 ∧
    s2 ≠ [] ∧
    ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
  intro T re s h_match
  induction h_match
  case MEmpty =>
    simp [pumping_constant, length]
  case MChar x =>
    simp [pumping_constant, length]
  case MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    simp [pumping_constant] at ih1 ih2 ⊢
    rw [app_length_poly]
    intro h_len
    cases plus_le_cases _ _ _ _ h_len
    case inl h1_le =>
      specialize ih1 h1_le
      rcases ih1 with ⟨s1_1, s1_2, s1_3, ih1_1, ih1_2, ih1_3⟩
      exists s1_1, s1_2, (s1_3 ++ s2)
      constructor
      · rw [ih1_1]
        ac_rfl
      · constructor
        · exact ih1_2
        · intro m
          rw [show s1_1 ++ (napp m s1_2 ++ (s1_3 ++ s2))
                = (s1_1 ++ (napp m s1_2 ++ s1_3)) ++ s2 from by ac_rfl]
          apply exp_match.MApp
          case H1 =>
            apply ih1_3 m
          case H2 =>
            exact h2
    case inr h2_le =>
      specialize ih2 h2_le
      rcases ih2 with ⟨s2_1, s2_2, s2_3, ih2_1, ih2_2, ih2_3⟩
      exists (s1 ++ s2_1), s2_2, s2_3
      constructor
      · rw [ih2_1]
        ac_rfl
      · constructor
        · exact ih2_2
        · intro m
          rw [show (s1 ++ s2_1) ++ (napp m s2_2 ++ s2_3)
                = s1 ++ (s2_1 ++ (napp m s2_2 ++ s2_3)) from by ac_rfl]
          apply exp_match.MApp
          case H1 =>
            apply h1
          case H2 =>
            apply ih2_3 m
  case MUnionL s1 re1 re2 h1 ih1 =>
    simp [pumping_constant] at ih1 ⊢
    intro h_len
    have h_1_and_2 := plus_le _ _ _ h_len
    specialize ih1 h_1_and_2.left
    rcases ih1 with ⟨s1_1, s1_2, s1_3, ih1_1, ih1_2, ih1_3⟩
    exists s1_1, s1_2, s1_3
    constructor
    · exact ih1_1
    · constructor
      · exact ih1_2
      · intro m
        apply exp_match.MUnionL
        apply ih1_3 m
  case MUnionR s2 re1 re2 h2 ih2 =>
    simp [pumping_constant] at ih2 ⊢
    intro h_len
    have h_1_and_2 := plus_le _ _ _ h_len
    specialize ih2 h_1_and_2.right
    rcases ih2 with ⟨s2_1, s2_2, s2_3, ih2_1, ih2_2, ih2_3⟩
    exists s2_1, s2_2, s2_3
    constructor
    · exact ih2_1
    · constructor
      · exact ih2_2
      · intro m
        apply exp_match.MUnionR
        apply ih2_3 m
  case MStar0 re' =>
    simp [pumping_constant, length]
    intro h_zero
    nomatch pumping_constant_0_false _ _ h_zero
  case MStarApp s1 s2 re' h1 h2 ih1 ih2 =>
    simp [pumping_constant] at ih1 ih2 ⊢
    intro h_len
    rw [app_length_poly] at h_len
    cases s1
    case nil =>
      clear h1 ih1
      simp [length] at h_len
      apply ih2 h_len
    case cons x s1' =>
      clear ih1 ih2
      exists [], (x :: s1'), s2
      constructor
      · rfl
      · constructor
        · intro h_empty
          nomatch h_empty
        · intro m
          apply napp_star _ _ _ _ _ h1 h2

theorem pumping : ∀ T (re : reg_exp T) s,
  s =~ re →
  pumping_constant re ≤ length s →
  ∃ s1 s2 s3,
    s = s1 ++ s2 ++ s3 ∧
    s2 ≠ [] ∧
    length s1 + length s2 ≤ pumping_constant re ∧
    ∀ m, s1 ++ napp m s2 ++ s3 =~ re := by
  intro T re s h_match
  induction h_match
  case MEmpty =>
    simp [pumping_constant, length]
  case MChar x =>
    simp [pumping_constant, length]
  case MApp s1 re1 s2 re2 h1 h2 ih1 ih2 =>
    simp [pumping_constant] at ih1 ih2 ⊢
    rw [app_length_poly]
    intro h_len
    cases lt_ge_cases (length s1) (pumping_constant re1)
    case inr h1_ge =>
      specialize ih1 h1_ge
      rcases ih1 with ⟨s1_1, s1_2, s1_3, ih1_1, ih1_2, ih1_3, ih1_4⟩
      exists s1_1, s1_2, (s1_3 ++ s2)
      constructor
      · rw [ih1_1]
        ac_rfl
      · constructor
        · exact ih1_2
        · constructor
          · apply le_plus_trans
            apply ih1_3
          · intro m
            rw [show s1_1 ++ (napp m s1_2 ++ (s1_3 ++ s2))
                  = (s1_1 ++ (napp m s1_2 ++ s1_3)) ++ s2 from by ac_rfl]
            apply exp_match.MApp
            case H1 =>
              apply ih1_4 m
            case H2 =>
              exact h2
    case inl h1_lt =>
      have h2_le : pumping_constant re2 ≤ length s2 := by
        omega
      specialize ih2 h2_le
      rcases ih2 with ⟨s2_1, s2_2, s2_3, ih2_1, ih2_2, ih2_3, ih2_4⟩
      exists (s1 ++ s2_1), s2_2, s2_3
      constructor
      · rw [ih2_1]
        ac_rfl
      · constructor
        · exact ih2_2
        · constructor
          · rw [app_length_poly]
            omega
          · intro m
            rw [show (s1 ++ s2_1) ++ (napp m s2_2 ++ s2_3)
                  = s1 ++ (s2_1 ++ (napp m s2_2 ++ s2_3)) from by ac_rfl]
            apply exp_match.MApp
            case H1 =>
              apply h1
            case H2 =>
              apply ih2_4 m
  case MUnionL s1 re1 re2 h1 ih1 =>
    simp [pumping_constant] at ih1 ⊢
    intro h_len
    have h_1_and_2 := plus_le _ _ _ h_len
    specialize ih1 h_1_and_2.left
    rcases ih1 with ⟨s1_1, s1_2, s1_3, ih1_1, ih1_2, ih1_3⟩
    exists s1_1, s1_2, s1_3
    constructor
    · exact ih1_1
    · constructor
      · exact ih1_2
      · constructor
        · apply le_plus_trans
          exact ih1_3.left
        · intro m
          apply exp_match.MUnionL
          apply ih1_3.right
  case MUnionR s2 re1 re2 h2 ih2 =>
    simp [pumping_constant] at ih2 ⊢
    intro h_len
    have h_1_and_2 := plus_le _ _ _ h_len
    specialize ih2 h_1_and_2.right
    rcases ih2 with ⟨s2_1, s2_2, s2_3, ih2_1, ih2_2, ih2_3⟩
    exists s2_1, s2_2, s2_3
    constructor
    · exact ih2_1
    · constructor
      · exact ih2_2
      · constructor
        · apply le_plus_trans_r
          exact ih2_3.left
        · intro m
          apply exp_match.MUnionR
          apply ih2_3.right
  case MStar0 re' =>
    simp [pumping_constant, length]
    intro h_zero
    nomatch pumping_constant_0_false _ _ h_zero
  case MStarApp s1 s2 re' h1 h2 ih1 ih2 =>
    simp [pumping_constant] at ih1 ih2 ⊢
    intro h_len
    rw [app_length_poly] at h_len
    cases lt_ge_cases (length s1) (pumping_constant re')
    case inl h1_lt =>
      clear ih1
      cases s1
      case nil =>
        simp [length] at h_len
        specialize ih2 h_len
        simp
        exact ih2
      case cons x s1' =>
        exists [], x :: s1', s2
        simp [length]
        constructor
        · simp [length] at h1_lt
          apply n_lt_m__n_le_m
          assumption
        · intro m
          apply napp_star _ _ _ _ _ h1 h2
    case inr h1_ge =>
      clear ih2
      specialize ih1 h1_ge
      rcases ih1 with ⟨s1_1, s1_2, s1_3, ih1_1, ih1_2, ih1_3, ih1_4⟩
      exists s1_1, s1_2, (s1_3 ++ s2)
      constructor
      · rw [ih1_1]
        ac_rfl
      · constructor
        · exact ih1_2
        · constructor
          · exact ih1_3
          · intro m
            specialize ih1_4 m
            rw [show s1_1 ++ (napp m s1_2 ++ (s1_3 ++ s2))
                  = (s1_1 ++ (napp m s1_2 ++ s1_3)) ++ s2 from by ac_rfl]
            apply exp_match.MStarApp
            · exact ih1_4
            · exact h2


inductive reflect (P : Prop) : Bool → Prop where
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ¬ P) : reflect P false


theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b := by
  intro P b h
  cases b
  case true =>
    apply reflect.ReflectT
    rw [h]
  case false =>
    apply reflect.ReflectF
    rw [h]
    intro hP
    contradiction


theorem reflect_iff : ∀ P b, reflect P b → (P ↔ b = true) := by
  intro P b h
  constructor
  case mp =>
    intro hP
    cases h
    case ReflectT H =>
      rfl
    case ReflectF H =>
      contradiction
  case mpr =>
    intro h_eq
    cases h
    case ReflectT H =>
      exact H
    case ReflectF H =>
      contradiction


theorem eqbP : ∀ n m, reflect (n = m) (n =? m) := by
  intro n m
  apply iff_reflect
  rw [eqb_eq]
  done  -- rfl は不要


theorem filter_not_empty_In : ∀ n l,
  filter (fun x => n =? x) l ≠ [] → In n l := by
  intro n l
  induction l
  case nil =>
    intro h
    apply h
    rfl
  case cons x l' ih =>
    intro h
    cases hb : n =? x
    case true =>
      simp [In]
      left
      rw [eqb_eq] at hb
      rw [hb]
    case false =>
      simp [In]
      right
      apply ih
      simp [filter, hb] at h
      apply h


theorem filter_not_empty_In' : ∀ n l,
  filter (fun x => n =? x) l ≠ [] →
  In n l := by
  intro n l
  induction l
  case nil =>
    intro h
    apply h
    rfl
  case cons x l' ih =>
    intro h
    simp [In]
    have h_eqbP := eqbP n x
    generalize hb : (n =? x) = b at h_eqbP
    cases h_eqbP
    case ReflectT eqnm =>
      rw [eqnm]
      left
      rfl
    case ReflectF neqnm =>
      right
      apply ih
      simp [filter, hb] at h
      apply h


def count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'


theorem eqbP_practice : ∀ n l,
  count n l = 0 → ¬(In n l) := by
  intro n l h_count
  induction l
  case nil =>
    intro h_in
    contradiction
  case cons m l' ih =>
    intro h_in
    simp [count] at h_count
    specialize ih h_count.right
    simp [In] at h_in
    cases h_in
    case inl h_eq =>
      symm at h_eq
      rw [← eqb_eq] at h_eq
      rw [h_eq] at h_count
      nomatch h_count.left
    case inr h_in' =>
      contradiction

#print Decidable


inductive nostutter {X:Type} : List X → Prop where
  | nil : nostutter []
  | single {x : X} : nostutter [x]
  | cons {x y : X} {l : List X}
         (h1 : x ≠ y)
         (h2 : nostutter (y :: l)) :
       nostutter (x :: y :: l)

theorem test_nostutter_1: nostutter [3, 1, 4, 1, 5, 6] := by
  repeat apply nostutter.cons (by simp)
  apply nostutter.single

theorem test_nostutter_2: nostutter (X := Nat) [] := by
  apply nostutter.nil

theorem test_nostutter_3: nostutter [5] := by
  apply nostutter.single

theorem test_nostutter_4: ¬ nostutter [3, 1, 1, 4] := by
  intro h
  cases h
  case cons h1 h2 =>
    cases h2
    case cons h3 h4 =>
      simp at h1
      contradiction


inductive Merge { X : Type u }
  : List X → List X → List X → Prop where
  | mergeNilLeft : ∀ l : List X,
      Merge [] l l
  | mergeNilRight : ∀ l : List X,
      Merge l [] l
  | mergeConsLeft : ∀ (x : X) (l1 l2 l3 : List X),
      Merge l1 l2 l3 →
      Merge (x :: l1) l2 (x :: l3)
  | mergeConsRight : ∀ (x : X) (l1 l2 l3 : List X),
      Merge l1 l2 l3 →
      Merge l1 (x :: l2) (x :: l3)

theorem filter_all_nil :
  ∀ {X : Type} {l : List X} {test : X → Bool},
  All (fun n => test n = false) l →
  filter test l = [] := by
  intro X l test
  intro h
  induction l
  case nil =>
    rfl
  case cons hd tl ih =>
    unfold filter
    rcases h with ⟨h1, h2⟩
    rw [h1]
    simp
    apply ih h2

theorem filter_all_id :
  ∀ {X : Type} {l : List X} {test : X → Bool},
  All (fun n => test n = true) l →
  filter test l = l := by
  intro X l test h_all
  induction l
  case nil =>
    rfl
  case cons hd tl ih =>
    rcases h_all with ⟨h_hd, h_tl⟩
    unfold filter
    rw [h_hd]
    simp
    apply ih h_tl

theorem merge_filter
  : ∀ (X : Type) (test: X → Bool) (l l1 l2 : List X),
  Merge l1 l2 l →
  All (fun n => test n = true) l1 →
  All (fun n => test n = false) l2 →
  filter test l = l1 := by
  intro X test l sl l2 h_merge h_all1 h_all2
  induction h_merge
  case mergeNilLeft l' =>
    apply filter_all_nil
    exact h_all2
  case mergeNilRight l' =>
    rw [filter_all_id]
    exact h_all1
  case mergeConsLeft x l1' l2' l3' h_merge' ih =>
    rcases h_all1 with ⟨h_hd, h_tl⟩
    unfold filter
    rw [h_hd]
    simp
    apply ih
    · exact h_tl
    · exact h_all2
  case mergeConsRight x l1' l2' l3' h_merge' ih =>
    rcases h_all2 with ⟨h_hd, h_tl⟩
    unfold filter
    rw [h_hd]
    simp
    apply ih
    · exact h_all1
    · exact h_tl

def IsSubseq {X : Type} (sl l : List X) : Prop :=
  ∃ sl' : List X, Merge sl sl' l

theorem filter_subseq
  {X: Type} (test : X → Bool) (l : List X) :
  IsSubseq (filter test l) l := by
  unfold IsSubseq
  exists (filter (fun n => (test n) = false) l)
  induction l
  case nil =>
    apply Merge.mergeNilLeft
  case cons hd tl ih =>
    cases hb : test hd
    case true =>
      unfold filter
      simp [hb]
      apply Merge.mergeConsLeft
      simp at ih
      exact ih
    case false =>
      unfold filter
      simp [hb]
      apply Merge.mergeConsRight
      simp at ih
      exact ih


theorem filter_challenge_2
  {X: Type} (test : X → Bool) (l s : List X) :
  (h : IsSubseq s l) →
  (All (fun n => test n = true) s) →
  s.length ≤ (filter test l).length
  ∧ IsSubseq (filter test l) l := by
  intro h_subseq h_all
  apply And.intro
  · unfold IsSubseq at h_subseq
    rcases h_subseq with ⟨sl', h_merge⟩
    induction h_merge
    case mergeNilLeft l' =>
      apply Nat.zero_le
    case mergeNilRight l' =>
      simp [filter_all_id h_all]
    case mergeConsLeft x l1 l2 l3 h_merge' ih =>
      rcases h_all with ⟨h_hd, h_tl⟩
      simp
      simp [filter, h_hd]
      exact ih h_tl
    case mergeConsRight x l1 l2 l3 h_merge' ih =>
      have ih' := ih h_all
      simp [filter]
      cases test x
      case true =>
        simp
        apply Nat.le_trans ih'
        simp
      case false =>
        simp
        exact ih'
  · exact filter_subseq test l


inductive Pal { X : Type }
  : List X → Prop where
  | nil : Pal []
  | single : ∀ x : X, Pal [x]
  | cons : ∀ (x : X) (l : List X),
      Pal l →
      Pal (x :: (l ++ [x]))


theorem pal_app_rev
  : ∀ {X : Type} {l : List X},
  Pal (l ++ l.reverse) := by
  intro X l
  induction l
  case nil =>
    apply Pal.nil
  case cons hd tl ih =>
    rw [List.reverse_cons]
    rw [← List.append_assoc]
    apply Pal.cons
    exact ih

theorem pal_rev
  : ∀ {X : Type} {l : List X},
  Pal l → Pal l.reverse := by
  intro X l h_pal
  induction h_pal
  case nil =>
    apply Pal.nil
  case single x =>
    apply Pal.single
  case cons x l' h_pal' ih =>
    simp
    apply Pal.cons
    exact ih

namespace PalByReverse
inductive Pal { X : Type }
  : List X → Prop where
  | Pal : ∀ l : List X,
      l = l.reverse →
      Pal l

theorem pal_app_rev : ∀ (X : Type) (l : List X),
  Pal (l ++ l.reverse) := by
  intro X l
  apply Pal.Pal
  rw [List.reverse_append]
  rw [List.reverse_reverse]

theorem pal_rev : ∀ (X : Type) (l : List X),
  Pal l → l = l.reverse := by
  intro X l h_pal
  cases h_pal
  case Pal h_eq =>
    exact h_eq
end PalByReverse


theorem List.nil_or_append_last
  : ∀ {X: Type} (l: List X),
  l = [] ∨ ∃ (init : List X) (lst : X), l = init ++ [lst] := by
  intro X l
  induction l
  case nil =>
    left
    rfl
  case cons hd tl ih =>
    right
    cases ih
    case inl h_nil =>
      exists [], hd
      rw [h_nil]
      rfl
    case inr h_append =>
      rcases h_append with ⟨init', lst', h_eq⟩
      exists (hd :: init'), lst'
      rw [h_eq]
      rfl


theorem palindrome_converse : ∀ {X: Type} (l: List X),
  l = l.reverse → Pal l := by
  intro X l h_rev
  generalize h_len : l.length = n at h_rev
  revert h_len h_rev l
  induction n using Nat.strongRecOn
  case ind n ih =>
    intro l h_rev h_len
    cases l
    case nil =>
      apply Pal.nil
    case cons hd tl =>
      cases List.nil_or_append_last tl
      case inl h_nil =>
        rw [h_nil]
        apply Pal.single
      case inr h_append =>
        rcases h_append with ⟨init, lst, h_eq⟩
        rw [h_eq]
        rw [h_eq] at h_rev
        simp at h_rev
        rcases h_rev with ⟨h_rev_l, h_rev⟩
        subst hd tl
        apply Pal.cons
        have n_plus2 : init.length + 2 = n := by
          simp at h_len
          exact h_len
        specialize ih init.length (by omega) init
        apply ih
        · simp only [List.append_cancel_right_eq] at h_rev
          exact h_rev
        · rfl


inductive DisjointComplex {X : Type}
  : List X → List X → Prop where
  | NilLeft (l : List X) :
      DisjointComplex [] l
  | NilRight (l : List X) :
      DisjointComplex l []
  | ConsLeft (x : X) (l1 l2 : List X)
      (h_notin : ¬ In x l2)
      (h_disjoint : DisjointComplex l1 l2) :
      DisjointComplex (x :: l1) l2
  | ConsRight (x : X) (l1 l2 : List X)
      (h_notin : ¬ In x l1)
      (h_disjoint : DisjointComplex l1 l2) :
      DisjointComplex l1 (x :: l2)


inductive Disjoint {X : Type}
  : List X → List X → Prop where
  | Nil (l : List X) :
      Disjoint [] l
  | Cons (x : X) (l1 l2 : List X)
      (h_notin : ¬ In x l2)
      (h_disjoint : Disjoint l1 l2) :
      Disjoint (x :: l1) l2


theorem notin_disjoint_cons_right :
  ∀ {X : Type} {x : X} {l1 l2 : List X},
  ¬In x l1 →
  Disjoint l1 l2 →
  Disjoint l1 (x :: l2) := by
  intro X x l1 l2 h_notin h_disjoint
  induction h_disjoint
  case Nil l =>
    apply Disjoint.Nil
  case Cons y l1' l2' h_notin' h_disjoint' ih =>
    apply Disjoint.Cons
    · unfold In at h_notin ⊢
      simp at h_notin
      simp
      apply And.intro
      · intro h_eq
        apply h_notin.left h_eq.symm
      · exact h_notin'
    · apply ih
      unfold In at h_notin
      simp at h_notin
      exact h_notin.right


theorem disjoint_equiv :
  ∀ {X : Type} {l1 l2 : List X},
  DisjointComplex l1 l2 ↔ Disjoint l1 l2 := by
  intro X l1 l2
  constructor
  case mp =>
    intro h_disjoint
    induction h_disjoint
    case NilLeft l =>
      apply Disjoint.Nil
    case NilRight l =>
      induction l
      case nil =>
        apply Disjoint.Nil
      case cons x l' ih =>
        apply Disjoint.Cons
        · intro h_in
          contradiction
        · exact ih
    case ConsRight x l1' l2' h_notin h_disjoint' ih =>
      apply notin_disjoint_cons_right h_notin ih
    case ConsLeft x l1' l2' h_notin h_disjoint' ih =>
      apply Disjoint.Cons
      · exact h_notin
      · exact ih
  case mpr =>
    intro h_disjoint
    induction h_disjoint
    case Nil l =>
      apply DisjointComplex.NilLeft
    case Cons x l1' l2' h_notin h_disjoint' ih =>
      apply DisjointComplex.ConsLeft
      · exact h_notin
      · exact ih


def disjoint_norec
  {X : Type} (l1 l2: List X) :Prop :=
  ∀ x, In x l1 → ¬ In x l2

inductive NoDup {X : Type}
  : List X → Prop where
  | Nil : NoDup []
  | Cons (x : X) (l : List X)
      (h_notin : ¬ In x l)
      (h_nodup : NoDup l) :
      NoDup (x :: l)


theorem cons_disjoint_notin :
  ∀ {X : Type} {x : X} {l1 l2 : List X},
  Disjoint (x :: l1) l2 →
  ¬ In x l2 := by
  intro X x l1 l2 h_disjoint
  cases h_disjoint
  case Cons h_notin h_disjoint =>
    exact h_notin


theorem disjoint_cons_left :
  ∀ {X : Type} {x : X} {l1 l2 : List X},
  Disjoint (x :: l1) l2 →
  Disjoint l1 l2 := by
  intro X x l1 l2 h_disjoint
  cases h_disjoint
  case Cons h_notin h_disjoint' =>
    exact h_disjoint'


theorem nodup_disjoint : ∀ {X : Type} {l1 l2 : List X},
  NoDup l1 →
  NoDup l2 →
  Disjoint l1 l2 →
  NoDup (l1 ++ l2) := by
  intro X l1 l2 h_nodup1 h_nodup2 h_disjoint
  induction h_nodup1
  case Nil =>
    exact h_nodup2
  case Cons x l1' h_notin1 h_nodup1' ih =>
    simp
    apply NoDup.Cons
    · intro h_in
      rw [In_app_iff] at h_in
      cases h_in
      case inl h_inl =>
        exact h_notin1 h_inl
      case inr h_inr =>
        apply cons_disjoint_notin h_disjoint h_inr
    · apply ih
      apply disjoint_cons_left h_disjoint


theorem in_split : ∀ (X : Type) (x : X) (l : List X),
  In x l → ∃ l1 l2, l = l1 ++ x :: l2 := by
  intro X x l h_in
  induction l
  case nil =>
    contradiction
  case cons hd tl ih =>
    simp [In] at h_in
    cases h_in
    case inl h_eq =>
      rw [h_eq]
      exists [], tl
    case inr h_in' =>
      rcases ih h_in' with ⟨l1, l2, h_eq⟩
      exists (hd :: l1), l2
      rw [h_eq]
      rfl


inductive repeats {X : Type} : List X → Prop where
  | here {x : X} {l : List X}
      (h_in : In x l) :
      repeats (x :: l)
  | there {x : X} {l : List X}
      (h_repeats : repeats l) :
      repeats (x :: l)


theorem pigeonhole_principle : excluded_middle →
  ∀ (X : Type) (l1 l2 : List X),
  (∀ x, In x l1 → In x l2) →
  length l2 < length l1 →
  repeats l1 := by
  intro em X l1
  induction l1
  case nil =>
    intro l2 h_in h_len
    simp [length] at h_len
  case cons hd tl ih =>
    intro l2 h_in h_len
    rcases em (In hd tl) with (h_in_tl | h_notin_tl)
    · apply repeats.here
      exact h_in_tl
    · apply repeats.there
      have h_in_hd : In hd l2 := by
        apply h_in
        unfold In
        left
        rfl
      have in_split_hd := in_split X hd l2 h_in_hd
      rcases in_split_hd with ⟨l2_1, l2_2, h_eq⟩
      apply ih (l2_1 ++ l2_2)
      · intro x h_in_tl
        rw [In_app_iff]
        have h_x_in_l2 : In x l2 := by
          apply h_in
          right
          exact h_in_tl
        rw [h_eq] at h_x_in_l2
        rw [In_app_iff] at h_x_in_l2
        cases h_x_in_l2
        case inl h_in_l2_1 =>
          left
          exact h_in_l2_1
        case inr h_in_l2_2 =>
          right
          cases h_in_l2_2
          case inl h_eq_hd =>
            rw [← h_eq_hd] at h_in_tl
            contradiction
          case inr h_in_l2_2' =>
            exact h_in_l2_2'
      · simp [length] at h_len
        rw [h_eq] at h_len
        rw [app_length_poly] at h_len ⊢
        simp [length] at h_len
        rw [← Nat.add_assoc] at h_len
        rw [@Nat.add_lt_add_iff_right] at h_len
        exact h_len
        done
      done


-- Called `string` in https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html#lab292
def ListChar := List Char


theorem provable_equiv_true :
  ∀ (P : Prop), P → (P ↔ True) := by
  intro P hP
  constructor
  case mp =>
    intro h
    trivial
  case mpr =>
    intro h_true
    exact hP

theorem not_equiv_false :
  ∀ (P : Prop), ¬P → (P ↔ False) := by
  intro P hP
  constructor
  case mp =>
    intro h
    contradiction
  case mpr =>
    intro h_false
    contradiction

theorem null_matches_none :
  ∀ (s : ListChar), (s =~ .EmptySet) ↔ False := by
  intro s
  apply not_equiv_false
  intro h
  nomatch h

theorem empty_matches_eps :
  ∀ (s : ListChar), (s =~ .EmptyStr) ↔ s = [ ] := by
  intro s
  constructor
  case mp =>
    intro h
    cases h
    rfl
  case mpr =>
    intro h
    rw [h]
    constructor

theorem empty_nomatch_ne :
  ∀ (a : Char) s, (a :: s =~ .EmptyStr) ↔ False := by
  intro a s
  apply not_equiv_false
  intro h
  generalize saeq : a :: s = sa at h
  cases h
  nomatch saeq
  done


