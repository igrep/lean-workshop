import Test.Basic
import Test.Poly

theorem silly1 : ∀ (n m : nat),
  n = m →
  n = m := by
  intro n m eq
  apply eq

theorem silly2 : ∀ (n m o p : Nat),
  n = m →
  (n = m → [n, o] = [m, p]) →
  [n, o] = [m, p] := by
  intro n m o p eq1 eq2
  -- もちろん apply eq2 ; apply eq1 と書いても良し
  apply eq2 eq1

theorem silly2' : ∀ (n m o p : Nat),
  n = m →
  (n = m → [n, o] = [m, p]) →
  [n, o] = [m, p] := by
  intro n m o p eq1 eq2
  apply (eq2 eq1) -- これを試したい

theorem silly2a : ∀ (n m : nat),
  (n, n) = (m, m) →
  (∀ (q r : nat), (q, q) = (r, r) → [q] = [r]) →
  [n] = [m] := by
  intro n m eq1 eq2
  apply eq2
  apply eq1

theorem silly_ex : ∀ p,
  (∀ n,   evenb n → ¬ evenb n.succ) →
  (∀ n, ¬ evenb n →   oddb n) →
  evenb p →
  oddb (.succ p) := by
  intro p h1 h2 even
  apply h2
  apply h1
  apply even

theorem silly3 : ∀ (n m : nat),
  n = m →
  m = n := by
  intro n m h
  -- エラーメッセージはでないらしい
  fail_if_success { apply h }
  symm
  apply h

theorem rev_exercise1 : ∀ (l l' : List Nat),
  l = rev l' →
  l' = rev l := by
  intro l l' h
  rw [h]
  -- rw [Eq.symm] は、
  --   l' = rev (rev l')
  -- における任意の式にマッチしうるので型変数を決定できなくなる
  apply Eq.symm
  apply rev_involutive_poly
  done

-- goal 全体にマッチさせるのが apply
-- subterm にマッチできるのが rw

theorem trans_eq_example : ∀ (a b c d e f : Nat),
  [a, b] = [c, d] →
  [c, d] = [e, f] →
  [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  rewrite [eq1]
  rewrite [eq2]
  rfl
  done

theorem trans_eq : ∀ (X : Type) (n m o : X),
  n = m → m = o → n = o := by
  intro X n m o eq1 eq2
  rewrite [eq1]
  rewrite [eq2]
  rfl
  done

theorem trans_eq_example' : ∀ (a b c d e f : Nat),
  [a, b] = [c, d] →
  [c, d] = [e, f] →
  [a, b] = [e, f] := by
  -- 原文では↓で eq1 eq2 も intro しているが、
  -- ここでは intro しないことで、rewrite [eq1] などしなくてよくしている
  intro a b c d e f
  apply trans_eq (m := [c, d])
  done

theorem trans_eq_example'' : ∀ (a b c d e f : nat),
  [a, b] = [c, d] →
  [c, d] = [e, f] →
  [a, b] = [e, f] := by
  intro a b c d e f
  -- Leanには transitivity 相当のものはない
  apply Trans.trans
  done

theorem trans_eq_exercise : ∀ (n m o p : Nat),
  m = (minusTwo o) →
  (n + p) = m →
  (n + p) = (minusTwo o) := by
  intro n m o p eq1 eq2
  apply Trans.trans eq2 eq1
  done

theorem S_injective : ∀ (n m : Nat),
  n.succ = m.succ →
  n = m := by
  intro n m h1
  have h2 : n = n.succ.pred := rfl
  rw [h2, h1]
  rfl
  done

theorem S_injective' : ∀ (n m : Nat),
  n.succ = m.succ →
  n = m := by
  intro n m h
  injection h

theorem injection_ex1 : ∀ (n m o : Nat),
  [n, m] = [o, o] →
  n = m := by
  intro n m o h
  injection h with h1 h2
  rw [h1]
  injection h2 with h3
  rw [h3]
  done

theorem injection_ex3 : ∀
  (X : Type) (x y z : X) (l j : List X),
  x :: y :: l = z :: j →
  j = z :: l →
  x = y := by
  -- simp_all で全て終わるが、見なかったことにする
  intro X x y z l j h1 h2
  injection h1 with h3 h4
  rw [h2] at h4
  injection h4 with h5
  rw [h5, h3]
  done

theorem discriminate_ex1 : ∀ (n m : Nat),
  false = true →
  n = m := by
  intro n m contra
  nomatch contra
  -- あるいは1 : injection contra
  -- あるいは2 : contradiction

theorem discriminate_ex2 : ∀ (n : Nat),
  n.succ = .zero →
  2 + 2 = 5 := by
  intro n contra
  nomatch contra

theorem discriminate_ex3 :
  ∀ (X : Type) (x y z : X) (l _j : List X),
  x :: y :: l = [] →
  x = z := by
  intro X x y z l j contra
  nomatch contra
  done

theorem eqb_0_l : ∀ (n : Nat),
  (0 == n) = true → n = 0 := by
  intro n
  cases n
  case zero =>
    intro h
    rfl
  case succ m =>
    intro h
    nomatch h

theorem f_equal : ∀ (A B : Type) (f: A → B) (x y: A),
  x = y → f x = f y := by
  intro A B f x y h
  rw [h]
  done

theorem eq_implies_succ_equal : ∀ (n m : Nat),
  n = m → n.succ = m.succ := by
  intro n m
  apply f_equal

theorem eq_implies_succ_equal' : ∀ (n m : Nat),
  n = m → n.succ = m.succ := by
  intro n m h
  congr
  done

theorem S_inj : ∀ (n m : Nat) (b : Bool),
  (n.succ == m.succ) = b →
  (n == m) = b := by
  intros n m b h
  -- 別解: simpa using h
  simp at h
  apply h
  done

theorem silly4 : ∀ (n m p q : Nat),
  (n = m → p = q) →
  m = n →
  q = p := by
  intro n m p q eq h
  symm at h
  replace h := eq h
  symm at h
  apply h

theorem silly4_another : ∀ (n m p q : Nat),
  (n = m → p = q) →
  m = n →
  q = p := by
  intro n m p q eq h
  rw [eq h.symm]
  done

theorem specialize_example: ∀ n,
  (∀ m, m * n = 0) → n = 0 := by
  intro n h
  specialize h (m := 1)
  simp at h
  apply h

theorem trans_eq_example''' : ∀ (a b c d e f : Nat),
  [a, b] = [c, d] →
  [c, d] = [e, f] →
  [a, b] = [e, f] := by
  intro a b c d e f eq1 eq2
  have h := trans_eq (m := [c, d])
  -- 別解1: apply h _ _ eq1 eq2
  -- 別解2: apply h <;> assumption
  --               ^^^
  -- <;> は、tactic が複数のサブゴールを生成する場合に、
  -- それぞれに対して次の tactic を適用する。
  -- この場合、全てのケースに対して assumption が適用される
  apply h
  apply eq1
  apply eq2
  done

theorem double_injective_FAILED: ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  induction n
  case zero =>
    intro eq
    cases m
    case zero =>
      rfl
    case succ m =>
      nomatch eq
  case succ n' ih_n =>
    intro eq
    cases m
    case zero =>
      nomatch eq
    case succ m' =>
      congr
      sorry

theorem double_injective : ∀ n m,
  double n = double m →
  n = m := by
  intro n
  induction n
  case zero =>
    intro m eq
    cases m
    case zero =>
      rfl
    case succ m =>
      nomatch eq
  case succ n' ih_n =>
    intro m eq
    cases m
    case zero =>
      nomatch eq
    case succ m' =>
      congr
      apply ih_n
      simp only [double] at eq -- なくても良いがあると分かりやすい
      injection eq with goal
      injection goal

theorem eqb_true : ∀ n m,
  n =? m = true → n = m := by
  intro n
  induction n
  case zero =>
    intro m h
    induction m
    case zero => rfl
    case succ m' m_ih =>
      nomatch h
  case succ n' n_ih =>
    intro m h
    cases m
    case zero => nomatch h
    case succ m' =>
      congr
      apply n_ih
      simp [eqb] at h
      exact h
  done

theorem plus_n_n_injective : ∀ (n m : Nat),
  n + n = m + m →
  n = m := by
  intro n
  induction n
  case zero =>
    intro m eq
    induction m
    case zero => rfl
    case succ m' m_ih =>
      nomatch eq
  case succ n' n_ih =>
    intro m eq
    cases m
    case zero =>
      nomatch eq
    case succ m' =>
      -- (n + m) + 1 = n + (m + 1)
      -- S (n + m) = n + (S m)
      rw [← Nat.add_assoc] at eq
      rw [← Nat.add_assoc] at eq
      simp [Nat.add] at eq
      rw [Nat.succ_add] at eq
      rw [Nat.succ_add] at eq
      injection eq with eq'
      have := n_ih _ eq'
      congr
      done
  done

theorem double_injective_take2_FAILED : ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  induction m
  case zero =>
    intro eq
    cases n
    case zero => rfl
    case succ n' =>
      nomatch eq
  case succ m' m_ih =>
    intro eq
    cases n
    case zero =>
      nomatch eq
    case succ n' =>
      congr
      sorry

theorem double_injective_take2 : ∀ n m,
  double n = double m →
  n = m := by
  intro n m
  revert n
  induction m
  case zero =>
    intro n eq
    cases n
    case zero => rfl
    case succ n' =>
      nomatch eq
  case succ m' m_ih =>
    intro n eq
    cases n
    case zero =>
      nomatch eq
    case succ n' =>
      congr
      apply m_ih
      injection eq with goal
      injection goal

theorem nth_error_after_last : ∀
  (n : Nat) (X : Type) (l : List X),
  l.length = n →
  l.get? n = none := by
  intro n _ l
  -- revert n
  induction l generalizing n
  case nil =>
    intro eq
    cases n
    case zero => rfl
    case succ => rfl
  case cons h t t_ih =>
    intro eq
    cases n
    case zero =>
      nomatch eq
    case succ n' =>
      simp at eq
      apply t_ih
      exact eq
  done

theorem nth_error_after_last2 : ∀
  (n : Nat) (X : Type) (l : List X),
  l.length = n →
  l.get? n = none := by
  intro n _ l eq
  induction n generalizing l
  case zero =>
    induction l
    case nil => rfl
    case cons h t t_ih =>
      nomatch eq
  case succ n' n_ih =>
    induction l
    case nil =>
      nomatch eq
    case cons h t t_ih =>
      apply n_ih
      simp at eq
      exact eq

def square (n : Nat) := n * n

theorem square_mult : ∀ n m,
  square (n * m) = square n * square m := by
  intro n m
  unfold square
  rw [← Nat.mul_assoc]
  have h : n * m * n = n * n * m := by
    rw [Nat.mul_comm, Nat.mul_assoc]
  rw [h, Nat.mul_assoc]
  done

def bar (x : Nat) :=
  match x with
  | .zero => 5
  | .succ _ => 5

theorem silly_fact_2_FAILED : ∀ m,
  bar m + 1 = bar (m + 1) + 1 := by
  intro m
  sorry

theorem silly_fact_2 : ∀ m,
  bar m + 1 = bar (m + 1) + 1 := by
  intro m
  cases m
  case zero => rfl
  case succ m' => rfl

theorem silly_fact_2' : ∀ m,
  bar m + 1 = bar (m + 1) + 1 := by
  intro m
  unfold bar
  cases m
  case zero => rfl
  case succ m' => rfl

def  sillyfun (n : Nat) : Bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false

theorem sillyfun_false : ∀ (n : Nat),
  sillyfun n = false := by
  intro n
  unfold sillyfun
  cases e1: n =? 3
  case true => rfl
  case false =>
    cases n =? 5
    case true => rfl
    case false => rfl

theorem sillyfun_false2 : ∀ (n : Nat),
  sillyfun n = false := by
  intro n
  unfold sillyfun
  split -- if や match を使った分岐を自動で subgoal に
  case isTrue => rfl
  case isFalse =>
    split
    case isTrue => rfl
    case isFalse => rfl

-- Lean 組み込みの tuple 向けに作り直す
def combine
  {X Y : Type}
  (lx : List X)
  (ly : List Y)
  : List (X × Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty

#check combine
#eval combine [1, 2] [false, false, true, true]

def split
  {X Y : Type}
  (l : List (X × Y))
  : (List X) × (List Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: l' =>
    match split l' with
    | (xs, ys) => (x :: xs, y :: ys)

#check split
#check split [(1, false), (2, false)]
#check ([1, 2], [false, false])
#guard split [(1, false), (2, false)] = ([1, 2], [false, false])

theorem combine_split : ∀ X Y (l : List (X × Y)) l1 l2,
  split l = (l1, l2) →
  combine l1 l2 = l := by
  intro X Y l l1 l2 h
  induction l generalizing l1 l2
  case nil =>
    -- simp する際に unfold する関数を指定できる
    simp [split] at h
    rw [h.left, h.right]
    rfl
  case cons hd tl tl_ih =>
    simp [split] at h
    rw [
      ← h.left,
      ← h.right,
      combine,
      ]
    congr
    apply tl_ih
    rfl

def sillyfun1 (n : Nat) : Bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false

theorem sillyfun1_odd_FAILED : ∀ (n : Nat),
  sillyfun1 n = true →
  oddb n = true := by
  intro n
  unfold sillyfun1
  cases n =? 3
  case false =>
    simp
    cases n =? 5
    case false =>
      simp
    case true =>
      simp
      sorry
  case true =>
    simp
    sorry

theorem sillyfun1_odd : ∀ (n : Nat),
  sillyfun1 n = true →
  oddb n = true := by
  intro n eq
  unfold sillyfun1 at eq
  cases heqe3: n =? 3
  case true =>
    replace heqe3 := eqb_true _ _ heqe3
    rw [heqe3]
    rfl
  case false =>
    cases heqe5: n =? 5
    case true =>
      replace heqe5 := eqb_true _ _ heqe5
      rw [heqe5]
      rfl
    case false =>
      rw [heqe3, heqe5] at eq
      contradiction


theorem bool_fn_applied_thrice :
  ∀ (f : Bool → Bool) (b : Bool),
  f (f (f b)) = f b := by
  intro f b
  cases b
  case true =>
    cases f_true: f true
    case true =>
      rw [f_true, f_true]
      done
    case false =>
      cases f_false: f false
      case true =>
        rw [f_true]
        done
      case false =>
        rw [f_false]
        done
      done
  case false =>
    cases f_false: f false
    case true =>
      cases f_true: f true
      case true =>
        rw [f_true]
        done
      case false =>
        rw [f_false]
        done
      done
    case false =>
      rw [f_false, f_false]
      done
  done

-- 別解
example (f : Bool → Bool) (b : Bool) : f (f (f b)) = f b := by
  cases f_true : f true <;> cases f_false : f false <;> cases b <;> simp [f_true, f_false]

theorem eqb_sym : ∀ (n m : Nat),
  (n =? m) = (m =? n) := by
  intro n m
  induction n generalizing m
  case zero =>
    cases m
    case zero => rfl
    case succ => rfl
  case succ n n_ih =>
    cases m
    case zero => rfl
    case succ =>
      simp [eqb]
      apply n_ih

theorem eqb_trans : ∀ n m p,
  n =? m = true →
  m =? p = true →
  n =? p = true := by
  intro n m p b1 b2
  have h1 := eqb_true _ _ b1
  have h2 := eqb_true _ _ b2
  rw [h1, h2, eqb_refl p]
  done

theorem split_combine : ∀ X Y (l : List (X × Y)) l1 l2,
  l1.length = l2.length →
  combine l1 l2 = l →
  split l = (l1, l2) := by
  intro X Y l l1 l2 hypo1 hypo2
  induction l generalizing l1 l2
  case nil =>
    cases l1
    case nil =>
      cases l2
      case nil =>
        rfl
      case cons h2 t2 =>
        nomatch hypo1
    case cons h1 t1 =>
      cases l2
      case nil =>
        nomatch hypo1
      case cons h2 t2 =>
        nomatch hypo2
  case cons h t ih =>
    cases l1
    case nil =>
      cases l2
      case nil =>
        nomatch hypo2
      case cons h2 t2 =>
        nomatch hypo1
    case cons h1 t1 =>
      cases l2
      case nil =>
        nomatch hypo2
      case cons h2 t2 =>
        cases h
        case mk x y =>
          dsimp [split]
          simp
          simp [combine] at hypo2
          rcases hypo2 with ⟨⟨h1x, h2y⟩, c⟩
          rw [h1x, h2y]
          simp
          simp at hypo1
          specialize ih t1 t2 hypo1 c
          rw [ih]
          apply And.intro
          case left => rfl
          case right => rfl
          done

theorem filter_exercise
  : ∀ (X : Type) (pred : X → Bool)
      (x : X) (l lf : List X),
  filter pred l = x :: lf → pred x = true := by
  intro X pred x l lf hypo
  induction l generalizing x lf
  case nil =>
    nomatch hypo
  case cons h t ih =>
    simp [filter] at hypo
    split at hypo
    case isTrue ht =>
      injection hypo with head_eq tail_eq
      rw [head_eq] at ht
      rw [ht]
      done
    case isFalse hf =>
      specialize ih _ _ hypo
      assumption

def forallb {X : Type} (pred : X → Bool) (l : List X) : Bool :=
  match l with
  | [] => true
  | h :: t =>
    if pred h then forallb pred t else false

#guard forallb oddb [1, 3, 5, 7, 9]
#guard forallb not [false, false]
#guard forallb evenb [0, 2, 4, 5] = false
#guard forallb (eqb 5) []

def existsb {X : Type} (pred : X → Bool) (l : List X) : Bool :=
  match l with
  | [] => false
  | h :: t =>
    if pred h then true else existsb pred t

#guard existsb (eqb 5) [0, 2, 3, 6] = false
#guard existsb (and true) [true, true, false]
#guard existsb oddb [1, 0, 0, 0, 0, 3]
#guard existsb evenb [] = false

def existsb' {X : Type} (pred : X → Bool) (l : List X) : Bool :=
  not (forallb (not ∘ pred) l)

#guard existsb' (eqb 5) [0, 2, 3, 6] = false
#guard existsb' (and true) [true, true, false]
#guard existsb' oddb [1, 0, 0, 0, 0, 3]
#guard existsb' evenb [] = false

-- こう書くと intro が要らない！
theorem existsb_existsb' (X : Type) (pred : X → Bool) (l : List X):
  existsb pred l = existsb' pred l := by
  induction l
  case nil => rfl
  case cons h t ih =>
    rw [existsb, existsb', forallb]
    simp [Function.comp]
    cases hypo : pred h
    case false =>
      simp
      simp [existsb'] at ih
      rw [ih]
    case true =>
      rfl
