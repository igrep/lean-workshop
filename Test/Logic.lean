import Test.Basic

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

theorem iff_refl : ∀ P : Prop,
  P ↔ P := by
  intro p
  constructor
  case mp =>
    intro h
    apply h
  case mpr =>
    -- 別解1: exact (fun x => x)
    -- 別解2: exact id
    intro h
    apply h

theorem iff_refl2 : ∀ P : Prop,
  P ↔ P := by
  intro p
  rfl

theorem iff_trans : ∀ P Q R : Prop,
  (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro P Q R ⟨hpq, hqp⟩ ⟨hqr, hrq⟩
  constructor
  case mp =>
    intro p
    apply hqr
    apply hpq
    exact p
    -- exact (fun x => hqr (hpq x))
    -- exact (hqr ∘ hpq)
  case mpr =>
    intro r
    apply hqp
    apply hrq
    exact r

theorem iff_trans2 : ∀ P Q R : Prop,
  (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro P Q R hpq hqr
  rw [hpq, hqr]
  done

theorem or_distributes_over_and : ∀ P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  intro P Q R
  constructor
  case mp =>
    rintro (p | ⟨q, r⟩)
    case inl =>
      constructor
      case left =>
        left
        exact p
      case right =>
        left
        exact p
    case inr.intro =>
      constructor
      case left =>
        right
        exact q
      case right =>
        right
        exact r
  case mpr =>
    rintro ⟨(p | q), pr⟩
    case intro.inl =>
      left
      exact p
    case intro.inr =>
      cases pr
      case inl p =>
        left
        exact p
      case inr r =>
        right
        constructor
        case left =>
          exact q
        case right =>
          exact r


theorem mul_eq_0 : ∀ n m, n * m = 0 ↔ n = 0 ∨ m = 0 := by
  intro n m
  constructor
  case mp =>
    apply mult_is_O
  case mpr =>
    apply factor_is_O

theorem my_or_assoc :
  ∀ P Q R : Prop, P ∨ (Q ∨ R) ↔ (P ∨ Q) ∨ R := by
  intro P Q R
  constructor
  case mp =>
    rintro (p | (q | r))
    case inl =>
      left
      left
      exact p
    case inr.inl =>
      left
      right
      exact q
    case inr.inr =>
      right
      exact r
  case mpr =>
    rintro ((p | q) | r)
    case inl.inl =>
      left
      exact p
    case inl.inr =>
      right
      left
      exact q
    case inr =>
      right
      right
      exact r

theorem mul_eq_0_ternary :
  ∀ n m p, n * m * p = 0 ↔ n = 0 ∨ m = 0 ∨ p = 0 := by
  intro n m p
  rw [mul_eq_0, mul_eq_0, my_or_assoc]
  done

def Even x := ∃ n : Nat, x = n * 2
#check Even
#print Exists

theorem four_is_Even : Even 4 := by
  unfold Even
  exists 2
  -- 別解:
  -- apply Exists.intro 2
  -- rfl

theorem four_is_Even2 : Even 4 := by
  constructor
  case w => exact 2
  case h => rfl

theorem exists_example_2 : ∀ n,
  (∃ m, n = m + 4) →
  (∃ o, n = o + 2) := by
  intro n ⟨m, _⟩
  exists m + 2

theorem dist_not_exists : ∀ (X : Type) (P : X → Prop),
  (∀ x, P x) → ¬ (∃ x, ¬ P x) := by
  intro X P h1 ⟨x, h2⟩
  have h : P x := h1 x
  contradiction

theorem dist_exists_or : ∀ (X : Type) (P Q : X → Prop),
  (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  intro X P Q
  constructor
  case mp =>
    rintro ⟨x, (hp | hq)⟩
    case inl =>
      left
      exists x
    case inr =>
      right
      exists x
  case mpr =>
    rintro (⟨x, hp⟩ | ⟨x, hq⟩)
    case inl =>
      exists x
      left
      exact hp
    case inr =>
      exists x
      right
      exact hq

theorem leb_plus_exists
  : ∀ (n m : Nat), n ≤ m → ∃ x, m = n + x := by
  intro n m h
  exists (m - n)
  rw [Nat.add_sub_of_le h]
  done

theorem plus_exists_leb : ∀ (n m : Nat), (∃ x, m = n+x) → n ≤ m := by
  intro n m ⟨x, h⟩
  rw [h]
  apply Nat.le_add_right

def In {A : Type} (x : A) (l : List A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x ∨ In x l'

#print Or

theorem In_example_1 : In 4 [1, 2, 3, 4, 5] := by
  right
  right
  right
  left
  rfl

theorem In_example_2 :
  ∀ n, In n [2, 4] →
  ∃ n', n = 2 * n' := by
  rintro n (h | h | _)
  case inl =>
    exists 1
    rw [← h]
  case inr.inl =>
    exists 2
    rw [← h]
  case inr.inr =>
    contradiction

theorem In_map : ∀
  (A B : Type)
  (f : A → B)
  (l : List A)
  (x : A),
  In x l →
  In (f x) (l.map f) := by
  intro A B f l x
  induction l
  case nil =>
    intro h
    contradiction
  case cons hd tl tl_h =>
    rintro (h | h)
    case inl =>
      rw [h, List.map]
      left
      rfl
    case inr =>
      right
      apply tl_h h

#check @Exists Nat (fun x => x = 1)
#check @Exists.intro Nat (fun x => x = 1) 1 rfl
#print Exists

theorem In_map_iff :
  ∀ (A B : Type) (f : A → B) (l : List A) (y : B),
  In y (l.map f) ↔ ∃ x, f x = y ∧ In x l := by
  intro A B f l y
  constructor
  case mp =>
    induction l
    case nil =>
      intro h
      contradiction
    case cons hd tl tl_h =>
      intro h
      rw [List.map] at h
      cases h
      case inl h' =>
        exists hd
        constructor
        case left => exact h'
        case right =>
          left
          rfl
      case inr h' =>
        specialize tl_h h'
        rcases tl_h with ⟨x, hfx, hxl⟩
        exists x
        constructor
        case left => exact hfx
        case right =>
          right
          exact hxl
  case mpr =>
    rintro ⟨x, ⟨hfx, hxl⟩⟩
    induction l
    case nil =>
      contradiction
    case cons hd tl tl_h =>
      rcases hxl with (hxl' | hxl')
      case inl =>
        rw [hxl']
        rw [List.map]
        left
        exact hfx
      case inr =>
        rw [List.map]
        right
        apply tl_h hxl'

theorem In_app_iff : ∀ A l l' (a : A),
  In a (l ++ l') ↔ In a l ∨ In a l' := by
  intro A l l' a
  constructor
  case mp =>
    induction l
    case nil =>
      intro h
      right
      exact h
      done
    case cons hd tl tl_h =>
      intro h
      cases h
      case inl h' =>
        left
        left
        exact h'
      case inr h' =>
        cases tl_h h'
        case inl h'' =>
          left
          right
          exact h''
        case inr h'' =>
          right
          exact h''
  case mpr =>
    rintro (h' | h')
    case inl =>
      induction l
      case nil =>
        contradiction
      case cons hd tl tl_h =>
        rcases h' with (h'' | h'')
        case inl =>
          left
          exact h''
        case inr =>
          right
          apply tl_h
          exact h''
    case inr =>
      induction l
      case nil =>
        exact h'
      case cons hd tl tl_h =>
        right
        apply tl_h

def All {T : Type} (P : T → Prop) (l : List T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' ∧ All P l'


theorem All_In :
  ∀ T (P : T → Prop) (l : List T),
  (∀ x, In x l → P x) ↔ All P l := by
  intro T P l
  constructor
  case mp =>
    induction l
    case nil =>
      intro h
      apply True.intro
    case cons hd tl tl_h =>
      intro h
      constructor
      case left =>
        apply h
        left
        rfl
      case right =>
        apply tl_h
        intro x h'
        apply h
        right
        exact h'
  case mpr =>
    induction l
    case nil =>
      intro h x h'
      contradiction
    case cons hd tl tl_h =>
      intro h x h'
      rcases h with ⟨left, right⟩
      cases h'
      case inl h'' =>
        rw [← h'']
        exact left
      case inr h'' =>
        apply tl_h right x
        exact h''
  done

def combine_odd_even (Podd Peven : Nat → Prop) : Nat → Prop :=
  fun n => if evenb n then Peven n else Podd n

theorem combine_odd_even_intro :
  ∀ (Podd Peven : Nat → Prop) (n : Nat),
    (oddb n = true → Podd n) →
    (oddb n = false → Peven n) →
    combine_odd_even Podd Peven n := by
  intro Podd Peven n h1 h2
  unfold combine_odd_even
  cases h: evenb n
  case true =>
    apply h2
    unfold oddb
    rw [h]
    rfl
  case false =>
    apply h1
    unfold oddb
    rw [h]
    rfl

theorem combine_odd_even_elim_odd :
  ∀ (Podd Peven : Nat → Prop) (n : Nat),
    combine_odd_even Podd Peven n →
    oddb n = true →
    Podd n := by
  intro Podd Peven n h h'
  unfold combine_odd_even at h
  split at h
  case isTrue h'' =>
    unfold oddb at h'
    rw [h''] at h'
    contradiction
  case isFalse h'' =>
    exact h

theorem combine_odd_even_elim_even :
  ∀ (Podd Peven : Nat → Prop) (n : Nat),
    combine_odd_even Podd Peven n →
    oddb n = false →
    Peven n := by
  intro Podd Peven n h h'
  unfold combine_odd_even at h
  split at h
  case isTrue h'' =>
    exact h
  case isFalse h'' =>
    unfold oddb at h'
    simp at h''
    rw [h''] at h'
    contradiction

#check (Nat.add : Nat → Nat → Nat)
#check (@List.reverse : ∀ X, List X → List X)
#check (Nat.add_comm : ∀ n m : Nat, n + m = m + n)
