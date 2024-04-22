import Test.Basic

#print Bin

-- Leanでは足し算が右辺に対してパターンマッチしているので、
-- 右単位元の方が簡単に証明できる
theorem plus_n_O_firsttry : forall n : Nat,
  n = n + 0 := by
  intros
  rfl
-- Ref.
#print Nat.add

def myAdd (n m : Nat) :=
  match n with
    | .zero => m
    | .succ n' => .succ (myAdd n' m)

example : myAdd 3 4 = 7 := by rfl

theorem myAdd_n_O_firsttry : forall n : Nat,
  n = myAdd n 0 := by
  intros
  -- rfl
  sorry

theorem myAdd_n_O_secondtry : ∀ n : Nat,
  n = myAdd n 0 := by
  intro n
  cases n
  case zero =>
    rfl
  case succ n' =>
    simp only [myAdd]
    -- rfl
    sorry

theorem myAdd_n_O : ∀ n : Nat,
  n = myAdd n 0 := by
  intro n -- Leanでは intro 必須。Coqではなくてもいいらしい
  induction n
  case zero => rfl
  case succ n' iH =>
    simp only [myAdd]
    rewrite [← iH]
    rfl

#print Nat.mul_succ

-- やはりかけ算の場合も右ゼロ元の方が
-- Leanでは簡単らしいので、左辺と右辺を入れ替える
-- Coq版とは恐らくアプローチが違うので注意
theorem mult_0_r : forall n:Nat,
  0 * n = 0 := by
  intro n
  induction n
  case zero => rfl
  case succ n' iH =>
    rewrite [Nat.mul_succ, Nat.add_zero, iH]
    rfl

theorem myAdd_n_Sm : forall n m : Nat,
  .succ (myAdd n m) = myAdd n (.succ m) := by
  intro n m
  induction n
  case zero => rfl
  case succ n' iH =>
    simp only [myAdd]
    rewrite [← iH]
    rfl

theorem myAdd_comm : forall n m : Nat,
  myAdd n m = myAdd m n := by
  intro n m
  induction n
  case zero =>
    rewrite [← myAdd_n_O]
    rfl
  case succ n' iH =>
    simp only [myAdd]
    rewrite [← myAdd_n_Sm, ← iH]
    rfl

theorem myAdd_assoc : forall n m p : Nat,
  (myAdd n (myAdd m p)) = (myAdd (myAdd n m) p) := by
  intro n m p
  induction n
  case zero =>
    simp only [myAdd]
  case succ n' iH =>
    simp only [myAdd]
    rewrite [← iH]
    rfl

def double (n : Nat): Nat :=
  match n with
  | .zero => .zero
  | .succ n' => .succ (.succ (double n'))

theorem double_myAdd : forall n,
  double n = myAdd n n := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [double, myAdd]
    rewrite [← myAdd_n_Sm, n_ih]
    rfl

theorem evenb_S : forall n : Nat,
  evenb (.succ n) = not (evenb n) := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [evenb]
    -- もちろん Bool.not_not を使っても良い
    -- rewrite [n_ih, Bool.not_not]
    rewrite [n_ih]
    cases (evenb n')
    case true => rfl
    case false => rfl

theorem mult_0_plus' : forall n m : Nat,
  (n + 0) * m = n * m := by
  intro n m
  have h : n + 0 = n := rfl
  rewrite [h]
  rfl

theorem myAdd_rearrange_firsttry : forall n m p q : Nat,
  myAdd (myAdd n m) (myAdd p q) = myAdd (myAdd m n) (myAdd p q) := by
  intro n m p q
  rewrite [myAdd_comm]
  sorry

theorem myAdd_rearrange : forall n m p q : Nat,
  myAdd (myAdd n m) (myAdd p q) = myAdd (myAdd m n) (myAdd p q) := by
  intro n m p q
  have h : myAdd n m = myAdd m n := by
    rewrite [myAdd_comm]
    rfl
  rewrite [h]
  rfl

-- 別解
theorem myAdd_rearrange2 : forall n m p q : Nat,
  myAdd (myAdd n m) (myAdd p q) = myAdd (myAdd m n) (myAdd p q) := by
  intro n m p q
  -- 引数を指定することで、書き換える箇所を特定できる！
  rewrite [myAdd_comm n m]
  rfl
