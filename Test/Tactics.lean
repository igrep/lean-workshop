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
  apply Eq.symm -- 専用のtacticはない？
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
