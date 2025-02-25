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

theorem proj2 : ∀ P Q : Prop,
  P ∧ Q → Q := by
  intro p q ⟨_, h⟩
  apply h

theorem and_commut : ∀ P Q : Prop,
  P ∧ Q → Q ∧ P := by
  intro p q ⟨hp, hq⟩
  constructor
  case left => apply hq
  case right => apply hp

theorem and_commut2 : ∀ P Q : Prop,
  P ∧ Q → Q ∧ P := by
  intro p q ⟨hp, hq⟩
  exact ⟨hq, hp⟩

-- and_assoc は組み込みであるらしい
theorem and_assoc' : ∀ P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro p q r ⟨hp, ⟨hq, hr⟩⟩
  constructor -- ゴールを複数のゴールに分解する
  case left =>
    constructor
    case left => apply hp
    case right => apply hq
  case right => apply hr

#check And
#check and -- こっちは Bool 用

#check Or

theorem factor_is_O:
  ∀ n m : Nat, n = 0 ∨ m = 0 → n * m = 0 := by
  rintro n m (hn | hm)
  case inl =>
    rw [hn, Nat.zero_mul]
    done
  case inr =>
    rw [hm]
    rfl

theorem or_intro_l
  : ∀ A B : Prop, A → A ∨ B := by
  intro a b ha
  left -- apply Or.inl と同等
  apply ha

theorem or_intro_l2
  : ∀ A B : Prop, A → A ∨ B := by
  intro a b ha
  constructor
  case h => apply ha

theorem zero_or_succ :
  ∀ n : Nat, n = 0 ∨ n = n.pred.succ := by
  intro n
  cases n
  case zero =>
    left
    rfl
  case succ n' =>
    right
    rfl

theorem mult_is_O :
  ∀ n m, n * m = 0 → n = 0 ∨ m = 0 := by
  intro n m hnm
  cases n
  case zero =>
    left
    rfl
  case succ n' =>
    cases m
    case zero =>
      right
      rfl
    case succ m' =>
      nomatch hnm

theorem or_commut : ∀ P Q : Prop,
  P ∨ Q → Q ∨ P := by
  rintro p q (hp | hq)
  case inl =>
    right
    apply hp
  case inr =>
    left
    apply hq

#print Not

theorem ex_falso_quodlibet : ∀ (P : Prop),
  False → P := by
  intro P contra
  cases contra

theorem not_implies_our_not : ∀ (P : Prop),
  ¬ P → (∀ (Q : Prop), P → Q) := by
  intro p np q hpq
  unfold Not at np
  cases (np hpq)

theorem zero_not_one : 0 ≠ 1 := by
  unfold Ne Not
  intro contra
  nomatch contra

theorem not_False :
  ¬ False := by
  unfold Not
  intro h
  cases h

theorem contradiction_implies_anything : ∀ P Q : Prop,
  (P ∧ ¬P) → Q := by
  rintro p q ⟨hp, hnp⟩
  unfold Not at hnp
  specialize hnp hp
  cases hnp

theorem double_neg : ∀ P : Prop,
  P → ¬¬P := by
  intro p hp
  -- unfold は見やすくするためだけなので、なくてもよい
  -- unfold Not
  intro np
  apply np hp

theorem contrapositive : ∀ (P Q : Prop),
  (P → Q) → (¬Q → ¬P) := by
  intro p q hpq nq hp
  specialize hpq hp
  unfold Not at nq
  specialize nq hpq
  cases nq

theorem not_both_true_and_false : ∀ P : Prop,
  ¬ (P ∧ ¬P) := by
  intro p ⟨hp, np⟩
  unfold Not at np
  specialize np hp
  cases np

theorem de_morgan_not_or : ∀ (P Q : Prop),
  ¬ (P ∨ Q) → ¬P ∧ ¬Q := by
  intro p q hpq
  unfold Not at hpq
  constructor
  case left =>
    unfold Not
    intro hp
    apply hpq (Or.inl hp)
  case right =>
    unfold Not
    intro hq
    apply hpq (Or.inr hq)

theorem not_S_pred_n : ¬(∀ n : Nat, n.pred.succ = n) := by
  intro h
  specialize h 0
  rw [Nat.pred] at h
  nomatch h

theorem not_true_is_false : ∀ b : Bool,
  b ≠ true → b = false := by
  intro b h
  cases b
  case false => rfl
  case true =>
    apply ex_falso_quodlibet
    apply h
    rfl

theorem not_true_is_false' : ∀ b : Bool,
  b ≠ true → b = false := by
  rintro (_ | _) h
  case false => rfl
  case true =>
    exfalso
    apply h
    rfl

theorem True_is_true : True := by
  apply True.intro

def disc_fn (n: Nat) : Prop :=
  match n with
  | 0 => True
  | _ + 1 => False

theorem disc_example : ∀ n, ¬ (0 = n + 1) := by
  intro n contra
  have h : disc_fn 0 := by
    unfold disc_fn
    apply True.intro
  rw [contra] at h
  unfold disc_fn at h
  apply h

def discriminate_list (xs : List X) : Prop :=
  match xs with
  | [] => True
  | _x :: _xs => False

theorem nil_is_not_cons
  : ∀ X (x : X) (xs : List X), ¬ ([] = x :: xs) := by
  intro X x xs contra
  have h : discriminate_list (X := X) [] := by
    unfold discriminate_list
    apply True.intro
  rw [contra] at h
  apply h

#print Iff

theorem iff_sym : ∀ P Q : Prop,
  (P ↔ Q) → (Q ↔ P) := by
  intro p q ⟨hpq, hqp⟩
  constructor
  case mp => apply hqp
  case mpr => apply hpq

theorem not_true_iff_false : ∀ b,
  b ≠ true ↔ b = false := by
  intro b
  constructor
  case mp => apply not_true_is_false
  case mpr =>
    intro hbf
    rw [hbf]
    intro hfb
    nomatch hfb

theorem apply_iff_example1 :
  ∀ P Q R : Prop, (P ↔ Q) → (Q → R) → (P → R) := by
  intro p q r hiff h hp
  apply h
  apply hiff.mp
  apply hp

theorem apply_iff_example1' :
  ∀ P Q R : Prop, (P ↔ Q) → (Q → R) → (P → R) := by
  intro p q r hiff
  rw [hiff] -- ↔ を = の用に扱うことができる
  intro qr
  apply qr

theorem apply_iff_example2:
  ∀ P Q R : Prop, (P ↔ Q) → (P → R) → (Q → R) := by
  intro p q r hiff h hq
  apply h
  apply hiff.mpr
  apply hq
