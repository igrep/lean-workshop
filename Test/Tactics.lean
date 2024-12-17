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
      injection eq with goal
      injection goal
