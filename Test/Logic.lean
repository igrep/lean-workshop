#check (∀ n m : Nat, n + m = m + n)
#check 2 = 2
#check 3 = 2
#check ∀ n : Nat, n = 2

theorem plus_2_2_is_4 :
  2 + 2 = 4 := rfl

def plus_claim : Prop := 2 + 2 = 4
#check plus_claim

theorem plus_claim_is_true : plus_claim := rfl

def is_three (n : Nat) : Prop :=
  n = 3
#check is_three

def injective {A B} (f : A → B) : Prop :=
  ∀ x y : A, f x = f y → x = y

theorem succ_inj : injective Nat.succ := by
  -- unfold injective
  intro x y h
  injection h

#check @Eq
#check @Eq Type -- e.g. Nat = Bool
#check @Eq Nat -- e.g. 2 = 1
#check @Eq Nat 2 2 -- 2 = 2

theorem and_example : 3 + 4 = 7 ∧ 2 * 2 = 4 := by
  apply And.intro
  case left =>
    rfl
  case right =>
    rfl

#check @And.intro

theorem plus_is_O :
  ∀ n m : Nat, n + m = 0 → n = 0 ∧ m = 0 := by
  intro n m h
  apply And.intro
  case left =>
    cases m
    case zero =>
      simp at h
      rw [h]
    case succ m' =>
      nomatch h
  case right =>
    cases n
    case zero =>
      simp at h
      rw [h]
    case succ n' =>
      -- simp only [Nat.add_eq_zero_iff, Nat.add_one_ne_zero, false_and] at h
      -- ^ simp? した上で「try this」をクリックすると出てくる！
      simp at h

-- 別解
theorem plus_is_O' :
  ∀ n m : Nat, n + m = 0 → n = 0 ∧ m = 0 := by
  intro n m h
  cases m
  case succ m' =>
    nomatch h
  case zero =>
    simp at h
    rw [h]
    simp

theorem and_example2 :
  ∀ n m : Nat, n = 0 ∧ m = 0 → n + m = 0 := by
  intro n m h
  cases h
  case intro left right =>
  rw [left, right]

theorem and_example2' :
  ∀ n m : Nat, n = 0 ∧ m = 0 → n + m = 0 := by
  intro n m ⟨left, right⟩
  rw [left, right]

theorem and_example2'' :
  ∀ n m : Nat, n = 0 → m = 0 → n + m = 0 := by
  intro n m h1 h2
  rw [h1, h2]

theorem and_example3 :
  ∀ n m : Nat, n + m = 0 → n * m = 0 := by
  intro n m h
  replace ⟨h1, h2⟩ := plus_is_O n m h
  rw [h2]
  rfl

theorem proj1 : ∀ P Q : Prop,
  P ∧ Q → P := by
  intro p q ⟨h, _⟩
  apply h
