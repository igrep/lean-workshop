import Test.Basic
import Test.Induction
import Test.Tactics

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
open NatPlayground in
  #check (
    plus_id_example : ∀ n m : nat,
    n = m → (n +!+ n) = (m +!+ m)
    )

theorem add_comm3 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [Nat.add_comm]
  rw [Nat.add_comm]
  sorry

theorem add_comm3_take2 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intros x y z
  rewrite [Nat.add_comm]
  have h : y + z = z + y := by
    apply Nat.add_comm
  rw [h]
  done

theorem  add_comm3_take3 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [Nat.add_comm]
  rw [Nat.add_comm y z]
  done

theorem add_comm3_take4 :
  ∀ x y z : Nat, x + (y + z) = (z + y) + x := by
  intro x y z
  rw [Nat.add_comm x (y + z)]
  rw [Nat.add_comm y z]
  done

theorem in_not_nil :
  ∀ A (x : A) (l : List A), In x l → l ≠ [] := by
  intro A x l h
  unfold In at h
  intro hl
  rw [hl] at h
  apply h

#check in_not_nil

theorem in_not_nil_42 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l h
  apply in_not_nil
  sorry
  sorry

theorem in_not_nil_42_take2 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l h
  apply in_not_nil (x := 42)
  apply h
  done

theorem  in_not_nil_42_take3 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l h
  have h := in_not_nil _ _ _ h
  apply h
  done

theorem in_not_nil_42_take4 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l h
  apply in_not_nil Nat 42
  apply h
  done

theorem in_not_nil_42_take5 :
  ∀ l : List Nat, In 42 l → l ≠ [] := by
  intro l h
  apply in_not_nil _ _ _ h
  done

theorem lemma_application_ex :
  ∀ {n : Nat} {ns : List Nat},
    In n (ns.map (fun m ↦ m * 0)) →
    n = 0 := by
  intro n ns h
  -- cases (In_map_iff _ _ _ _ _).mp h
  rcases (In_map_iff ..).mp h with ⟨m, h1, h2⟩
  rw [Nat.mul_zero] at h1
  rw [← h1]
  done

theorem even_42_bool : evenb 42 = true := by
  rfl

theorem even_42_bool' : evenb 42 := by
  rfl

#check even_42_bool'

theorem even_42_prop : Even 42 := by
  unfold Even
  exists 21
  done

theorem even_double : ∀ k, evenb (2 * k) = true := by
  intro k
  induction k
  case zero =>
    rfl
  case succ k' ih_k' =>
    apply ih_k'
    done

theorem even_double_conv : ∀ n, ∃ k,
  n = if evenb n then 2 * k else (2 * k) + 1 := by
  intro n
  induction n
  case zero =>
    exists 0
  case succ n' ih_n' =>
    rw [evenb_S]
    cases h : evenb n'
    case false =>
      rw [h] at ih_n'
      simp at ih_n' ⊢
      rcases ih_n' with ⟨k, h'⟩
      rw [h']
      exists k + 1
    case true =>
      rw [h] at ih_n'
      simp at ih_n' ⊢
      rcases ih_n' with ⟨k, h'⟩
      rw [h']
      exists k

theorem even_bool_prop : ∀ n,
  evenb n = true ↔ Even n := by
  intro n
  constructor
  case mp =>
    intro h
    cases even_double_conv n
    case intro k hk =>
      rw [hk, h]
      exists k
      simp
      rw [Nat.mul_comm]
      done
  case mpr =>
    intro ⟨k, hk⟩
    rw [hk]
    rw [Nat.mul_comm]
    rw [even_double]
    done

theorem eqb_eq : ∀ n1 n2 : Nat,
  (n1 =? n2) = true ↔ n1 = n2 := by
  intro n1 n2
  constructor
  case mp =>
    apply eqb_true
  case mpr =>
    intro h
    rw [h]
    rw [eqb_refl]

def is_even_prime n :=
  -- Lean 4の場合、NatがDecidableEqなため、
  -- if 式の条件節に命題を書ける
  if n = 2 then true
  else false

#check ite

theorem even_1000'' : Even 1000 := by
  -- Rocqのapplyは Iff を特別扱いしているらしい
  apply (even_bool_prop _).mp
  rfl
  done

theorem evenb_eq : evenb n = (n % 2 == 0) := by
  induction n using evenb.induct
  case case1 => rfl
  case case2 => rfl
  case case3 n ih =>
    rw [evenb, ih, Nat.add_mod_right _ 2]

instance (n : Nat) : Decidable (Even n) :=
  if h : n % 2 == 0 then
    have h : evenb n := by rwa [evenb_eq]
    Decidable.isTrue ((even_bool_prop n).mp h)
  else by
    apply Decidable.isFalse
    intro h'
    have h'' := (even_bool_prop n).mpr h'
    rw [← evenb_eq, h''] at h
    contradiction

theorem even_1000''' : Even 1000 := by
  decide
  done

theorem not_even_1001 : evenb 1001 = false := by
  rfl

theorem not_even_1001' : ¬ Even 1001 := by
  rw [← even_bool_prop]
  unfold Not
  intro h
  contradiction
  done

theorem plus_eqb_example : ∀ n m p : Nat,
  n =? m = true → n + p =? m + p = true := by
  intro n m p h
  rw [eqb_eq] at h
  rw [h]
  rw [eqb_eq]
  done

theorem andb_true_iff : ∀ b1 b2 : Bool,
  (b1 && b2) = true ↔ b1 = true ∧ b2 = true := by
  intro b1 b2
  constructor
  case mp =>
    intro h
    cases b1
    case true =>
      cases b2
      case true =>
        constructor
        case left => rfl
        case right => rfl
      case false =>
        contradiction
    case false =>
      contradiction
  case mpr =>
    intro ⟨h1, h2⟩
    rw [h1, h2]
    rfl

theorem orb_true_iff : ∀ b1 b2 : Bool,
  (b1 || b2) = true ↔ b1 = true ∨ b2 = true := by
  intro b1 b2
  constructor
  case mp =>
    intro h
    cases b1
    case true =>
      left
      rfl
    case false =>
      cases b2
      case true =>
        right
        rfl
      case false =>
        contradiction
  case mpr =>
    rintro (h | h)
    case inl =>
      rw [h]
      rfl
    case inr =>
      rw [h]
      apply Bool.or_true

theorem eqb_neq : ∀ x y : Nat,
  (x =? y) = false ↔ x ≠ y := by
  intro x y
  constructor
  case mp =>
    intro h
    intro h'
    rw [← eqb_eq] at h'
    rw [h'] at h
    contradiction
  case mpr =>
    intro h
    unfold Ne Not at h
    rw [← eqb_eq] at h
    revert h
    cases x =? y
    case true =>
      intro h'
      contradiction
    case false =>
      intro h'
      rfl

-- 別解
theorem eqb_neq2 : ∀ x y : Nat,
  (x =? y) = false ↔ x ≠ y := by
  intro x y
  unfold Ne
  rw [← eqb_eq]
  cases x =? y <;> simp


def eqb_list
  {A : Type}
  (eqb : A → A → Bool)
  (l1 l2 : List A) : Bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 =>
    eqb x1 x2 && eqb_list eqb xs1 xs2
  | _, _ => false

#check eqb_list.induct

theorem eqb_list_true_iff :
  ∀ A (eqb : A → A → Bool),
    (∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2) →
    ∀ l1 l2, eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
  intro A eqb heqb l1 l2
  constructor
  case mp =>
    induction l1 generalizing l2
    case nil =>
      intro h
      cases l2
      case nil =>
        rfl
      case cons x xs =>
        contradiction
    case cons x xs ih =>
      intro h
      cases l2
      case nil =>
        contradiction
      case cons y ys =>
        rw [eqb_list] at h
        rw [andb_true_iff] at h
        rcases h with ⟨h1, h2⟩
        rw [heqb] at h1
        rw [h1]
        congr
        apply ih
        exact h2
        done
  case mpr =>
    intro h
    rw [h]
    induction l2 generalizing l1
    case nil =>
      rfl
    case cons x xs ih =>
      rw [eqb_list]
      specialize ih xs rfl
      rw [ih]
      rw [Bool.and_true]
      rw [heqb]
      done

-- eqb_list_true_iff の別解
example :
  ∀ A (eqb : A → A → Bool),
    (∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2) →
    ∀ l1 l2, eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
  intro A eqb heqb
  -- ↓代わりに`intro l1 l2; induction l1, l2 using eqb_list.induct eqb`としても良い
  apply eqb_list.induct
  -- 両方空リストのパターン
  case case1 => simp [eqb_list]
  -- 互いの長さが異なるパターン
  case case3 =>
    intro l1 l2 not_nil not_cons
    match l1, l2 with
    | [], [] => simp at not_nil
    | hd1 :: tl1, hd2 :: tl2 => specialize not_cons hd1 tl1 hd2 tl2; simp at not_cons
    | [], _ :: _ | _ :: _, [] => simp [eqb_list]
  -- 長さが同じで両方consのパターン
  case case2 =>
    intro hd1 tl1 hd2 tl2 ih
    -- 本当はここで `simp [eqb_list, heqb, ih]` したら終わる
    unfold eqb_list
    rw [andb_true_iff, heqb, ih, List.cons_eq_cons]

-- eqb_list_true_iff の別解2. `eqb_list.induct`を使うのと「unfoldしてsplitする」のはかなり似てる
example :
  ∀ A (eqb : A → A → Bool),
    (∀ a1 a2, eqb a1 a2 = true ↔ a1 = a2) →
    ∀ l1 l2, eqb_list eqb l1 l2 = true ↔ l1 = l2 := by
  intro A eqb heqb l1 l2
  unfold eqb_list
  split
  -- 両方空リストのパターン
  case h_1 => simp
  -- 互いの長さが異なるパターン
  case h_3 _ _ not_nil not_cons =>
    match l1, l2 with
    | [], [] => simp at not_nil
    | hd1 :: tl1, hd2 :: tl2 => specialize not_cons hd1 tl1 hd2 tl2; simp at not_cons
    | [], _ :: _ | _ :: _, [] => simp
  case h_2 _ _ hd1 tl1 hd2 tl2 =>
    have ih := _example _ _ heqb tl1 tl2
    rw [andb_true_iff, heqb, ih, List.cons_eq_cons]

theorem forallb_true_iff : ∀ X test (l : List X),
  forallb test l = true ↔ All (fun x => test x = true) l := by
  intro X test l
  induction l
  case nil =>
    constructor
    case mp =>
      intro h
      apply True.intro
    case mpr =>
      intro h
      rfl
  case cons hd tl ih =>
    unfold forallb All
    cases test hd
    case true =>
      simp
      exact ih
    case false =>
      simp only [Bool.false_eq_true]
      simp only [↓reduceIte]
      simp only [false_and]
      simp only [Bool.false_eq_true]

theorem function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (Nat.pred 4) + x) := rfl

theorem function_equality_ex2 :
  (fun x => x + 1) = (fun x => 1 + x) := by
  funext x
  rw [Nat.add_comm]
  done

#print axioms function_equality_ex2

axiom functional_extensionality : ∀ {X Y: Type}
                                    {f g : X → Y},
  (∀ (x : X), f x = g x) → f = g

theorem function_equality_ex2_2 :
  (fun x => x + 1) = (fun x => 1 + x) := by
  apply functional_extensionality
  intro x
  rw [Nat.add_comm]
  done

def rev_append {X} (l1 l2 : List X) : List X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)

def tr_rev {X} (l : List X) : List X :=
  rev_append l []

theorem rev_append_eq : ∀ X (l1 l2 : List X),
  rev_append l1 l2 = rev l1 ++ l2 := by
  intro X l1 l2
  induction l1 generalizing l2
  case nil =>
    rfl
  case cons hd tl ih =>
    rw [rev_append]
    rw [ih]
    rw [rev]
    rw [List.append_assoc]
    rfl

theorem tr_rev_correct : ∀ X, @tr_rev X = @rev X := by
  intro X
  funext l
  unfold tr_rev
  rw [rev_append_eq]
  rw [List.append_nil]
  done

def excluded_middle := ∀ P : Prop,
  P ∨ ¬ P

theorem restricted_excluded_middle : ∀ P b,
  (P ↔ b = true) → P ∨ ¬ P := by
  intro P b h
  cases b
  case true =>
    left
    apply h.mpr
    rfl
  case false =>
    right
    rw [h] -- もっとRocq版に近い書き方があるかも？
    simp
  done

theorem restricted_excluded_middle_eq : ∀ (n m : Nat),
  n = m ∨ n ≠ m := by
  intro n m
  apply restricted_excluded_middle (n = m) (n =? m)
  apply Iff.symm
  apply eqb_eq
  done

theorem excluded_middle_irrefutable: ∀ (P : Prop),
  ¬ ¬ (P ∨ ¬ P) := by
  intro P h
  apply h
  apply Or.inr
  intro h'
  apply h
  apply Or.inl
  exact h'

theorem not_exists_dist :
  excluded_middle →
  ∀ (X : Type) (P : X → Prop),
    ¬ (∃ x, ¬ P x) → (∀ x, P x) := by
  intro em X P h1 x
  have h : P x ∨ ¬ P x := by
    apply em
  cases h
  case inl h =>
    exact h
  case inr h =>
    exfalso
    apply h1
    exists x
  done

-- def excluded_middle := ∀ P : Prop, P ∨ ¬ P

def consequentia_mirabilis := ∀ P : Prop, (¬P → P) → P

def double_negation_elimination := ∀ P : Prop, ¬¬P → P

def peirce := ∀ P Q: Prop, ((P → Q) → P) → P

def de_morgan_not_and_not := ∀ P Q : Prop, ¬(¬P ∧ ¬Q) → P ∨ Q

def implies_to_or := ∀ P Q : Prop, (P → Q) → (¬P ∨ Q)

theorem excluded_middle_consequentia_mirabilis :
  excluded_middle → consequentia_mirabilis := by
  intro em P h
  have pOrNotP : P ∨ ¬ P := by
    apply em
  cases pOrNotP
  case inl p =>
    exact p
  case inr p =>
    apply h
    exact p
  done

theorem consequentia_mirabilis_double_negation_elimination :
  consequentia_mirabilis → double_negation_elimination := by
  intro cm P nnp
  have pcm := cm P
  apply pcm
  intro np
  specialize nnp np
  contradiction

theorem double_negation_elimination_peirce :
  double_negation_elimination → peirce := by
  intro dne P Q h
  unfold double_negation_elimination at dne
  apply dne
  intro np
  apply np
  apply h
  intro p
  contradiction
  -- have npp := np p
  -- exact npp.elim

theorem peirce_de_morgan_not_and_not :
  peirce → de_morgan_not_and_not := by
  intro pe P Q h
  unfold peirce at pe
  apply pe _ False
  intro h1
  exfalso
  apply h
  constructor
  · intro p
    apply h1
    left
    exact p
  · intro q
    apply h1
    right
    exact q
  done

theorem de_morgan_not_and_not_implies_to_or :
  de_morgan_not_and_not → implies_to_or := by
  intro dm P Q h
  unfold de_morgan_not_and_not at dm
  apply dm
  intro ⟨nnp, nq⟩
  apply nq
  apply h
  have p_or_not_p : P ∨ ¬ P := by
    apply dm
    intro ⟨np, _⟩
    contradiction
  cases p_or_not_p
  case a.inl p =>
    exact p
  case a.inr np =>
    contradiction

theorem implies_to_or_excluded_middle :
  implies_to_or → excluded_middle := by
  intro ito P
  unfold implies_to_or at ito
  rw [Or.comm]
  apply ito
  intro p
  exact p
