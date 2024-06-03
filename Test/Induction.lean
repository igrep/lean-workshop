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

infixl:150 " +!+ " => myAdd

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

@[simp] theorem myAdd_zero : ∀ n : Nat,
  myAdd n 0 = n := by
  intro n -- Leanでは intro 必須。Coqではなくてもいいらしい
  induction n
  case zero => rfl
  case succ n' iH =>
    simp only [myAdd]
    rewrite [iH]
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

theorem myAdd_swap : ∀ n m p : Nat,
  myAdd n (myAdd m p) = myAdd m (myAdd n p) := by
  intro n m p
  -- 引数を指定することで、書き換える箇所を特定できる！
  -- だからhaveを使わなくても証明できる！
  rewrite [myAdd_assoc, myAdd_comm n m, myAdd_assoc]
  rfl

-- comm:  myAdd n m = myAdd m n
-- assoc: (myAdd n (myAdd m p)) = (myAdd (myAdd n m) p)

def myMult (n m : Nat): Nat :=
  match n with
    | .zero => .zero
    | .succ n' => myAdd m (myMult n' m)

infixl:160 " *!* " => myMult

example : myMult 0 3 = 0 := rfl
example : myMult 3 0 = 0 := rfl
example : myMult 3 1 = 3 := rfl
example : myMult 1 3 = 3 := rfl
example : myMult 2 3 = 6 := rfl
example : myMult 3 2 = 6 := rfl

@[simp] theorem myMult_left_zero : ∀ n : Nat,
  myMult .zero n = .zero := by
  intro n
  rfl

@[simp] theorem myMult_right_zero : ∀ n : Nat,
  myMult n .zero = .zero := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [myMult, myAdd]
    -- rw: rewrite と rfl を一緒にやる
    rw [n_ih]

theorem myMult_right_succ : ∀ n m : Nat,
  myMult n (Nat.succ m) = myAdd n (myMult n m) := by
  intro n m
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [myMult, myAdd]
    rw [
      n_ih,
      myAdd_assoc,
      myAdd_assoc,
      myAdd_comm m n',
    ]

-- myMult n 0 = 0
-- myMult (Nat.succ n) m = n + (myMult n m)
-- myMult n (Nat.succ m) = m + (myMult n m)

theorem myMult_comm : ∀ m n : Nat,
  myMult m n = myMult n m := by
  intro m n
  induction m
  -- .zero ではなく zero。
  -- constructorの名前ではなくgoalの名前なので。
  -- goalの名前はconstructorの名前から自動でつく
  case zero =>
    -- 「@[simp] myMult_right_zero」と書いているので、
    -- myMult_right_zero を使っての証明を自動で行ってくれる
    simp
  case succ m' m_ih =>
    simp only [myMult]
    rw [m_ih, myMult_right_succ]

-- Basic.lean の nat 向け leb を Nat 向けに書き直し
def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 =>
      match m with
      | 0 => false
      | m' + 1 => leb n' m'

infixl:55 " <=? " => leb

theorem leb_refl : ∀ n : Nat,
  -- n <=? n = true とか書かなくていい！
  n <=? n := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [leb]
    rw [n_ih]
    done

-- Basic.lean の nat 向け eqb を Nat 向けに書き直し
def eqb (n m : Nat) : Bool :=
  match n with
  | 0 =>
    match m with
      | 0 => true
      | _m' + 1 => false
  | n' + 1 =>
    match m with
      | 0 => false
      | m' + 1 => eqb n' m'

infixl:55 " =? " => eqb

theorem zero_nbeq_S : ∀ n : Nat,
  ((0 : Nat) =? (n + 1)) = false := by
  intro n
  rfl

open example1

theorem andb_false_r : ∀ b : bool,
  andb b .false = .false := by
  intro b
  cases b
  case true => rfl
  case false => rfl

#eval Lean.versionString

theorem plus_ble_compat_l : ∀ n m p : Nat,
  n <=? m → (p + n) <=? (p + m) := by
  intro n m p h
  induction p
  case zero =>
    simp
    -- 前提である h に基いて証明
    -- exact h でも可
    assumption
  case succ p' p_ih =>
    rewrite [Nat.succ_add, Nat.succ_add]
    -- simp [leb] してもしなくても
    exact p_ih
  done

theorem S_nbeq_0 : ∀ n : Nat,
  (n.succ =? 0) = false := by
  intro n
  rfl

theorem mult_1_l : ∀ n : Nat, myMult 1 n = n := by
  intro n
  simp [myMult, myAdd]

theorem all3_spec : ∀ b c : Bool,
  (b && c) || (!b || !c) := by
  intro b c
  cases b
  case true =>
    cases c
    case false => rfl
    case true => rfl
  case false =>
    rfl
  done

theorem mult_plus_distr_r : ∀ n m p : Nat,
  myMult (myAdd n m) p = myAdd (myMult n p) (myMult m p) := by
  intro n m p
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp [myAdd, myMult]
    rw [n_ih, myAdd_assoc]

theorem mult_assoc : ∀ n m p : Nat,
  n *!* (m *!* p) = (n *!* m) *!* p := by
  intro n m p
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp [myMult]
    --  m *!* p +!+ n' *!* (m *!* p) =
    -- (m       +!+ n' *!* m) *!* p
    rw [n_ih]
    --  m *!* p +!+ n' *!* m  *!* p =
    -- (m       +!+ n' *!* m) *!* p
    rw [mult_plus_distr_r]
  done

theorem eqb_refl : ∀ n : Nat,
  true = (n =? n) := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [eqb]
    rw [n_ih]
    done

theorem plus_swap' : ∀ n m p : Nat,
  (n +!+ (m +!+ p)) = (m +!+ (n +!+ p)) := by
  intro n m p
  rw [
    myAdd_assoc,
    myAdd_assoc,
    myAdd_comm m n
    ]


theorem bin_to_nat_pres_incr : ∀ n : Bin,
  n.inc.toNat = n.toNat.succ := by
  intro n
  induction n
  case Z => rfl
  case B0 n' _n_ih =>
    simp [Bin.inc, Bin.toNat]
  case B1 n' n_ih =>
    simp [Bin.inc, Bin.toNat]
    rw [n_ih]
    rw [Nat.succ_mul]
    done
