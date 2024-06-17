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

-- nat_to_bin (n:nat) : bin
def Bin.ofNat (n:Nat) : Bin :=
  match n with
  | .zero => .Z
  | .succ n' => Bin.inc (Bin.ofNat n')

example : Bin.ofNat 0 = .Z := by rfl
example : Bin.ofNat 1 = .B1 .Z := by rfl
example : Bin.ofNat 2 = .B0 (.B1 .Z) := by rfl
example : Bin.ofNat 3 = .B1 (.B1 .Z) := by rfl

theorem inc_bin_ofNat : ∀ n, Bin.inc (Bin.ofNat n) = Bin.ofNat (.succ n) := by
  intro n
  cases n
  case zero => rfl
  case succ n' =>
    simp only [Bin.ofNat]
  done

theorem inc_bin_toNat : ∀ b, Bin.toNat (Bin.inc b) = .succ (Bin.toNat b) := by
  intro b
  induction b
  case Z => rfl
  case B0 b' _b_ih =>
    simp [Bin.toNat]
    done
  case B1 b' b_ih =>
    simp [Bin.toNat]
    rw [b_ih]
    generalize Bin.toNat b' = x
    rw [Nat.succ_mul]
    done

theorem nat_bin_nat : ∀ n, Bin.toNat (Bin.ofNat n) = n := by
  intro n
  induction n
  case zero => rfl
  case succ n' n_ih =>
    simp only [Bin.ofNat]
    rw [inc_bin_toNat, n_ih]
    done

-- (b) 逆方向も示した方がいいのでは？と思うでしょう。
-- 逆とはつまり、2進数を自然数に変換し、それをまた2進数に戻すと、
-- 元の2進数になる、というものです。 しかし、これは正しくありません。
-- なぜそうなるのかを（コメントとして）説明しなさい。
--
-- 回答例: 同じNatに対して複数のBin型による表現が存在しうるため、
-- あるBin型の値をNatに変換してからまたBin型の値に変換すると、
-- 異なる表現のBin型の値になってしまう可能性があるため。
-- 例:
#eval Bin.toNat (.B0 .Z) -- 結果は0だが、正しい表現ではない
#eval Bin.toNat (.B0 (.B0 .Z)) -- こちらも結果は0だが以下略
#eval Bin.toNat (.B1 (.B0 .Z)) -- こちらは結果は1だが以下略

def Bin.isZero (b : Bin): Bool :=
  match b with
  | .Z => true
  | .B0 b' => Bin.isZero b'
  | .B1 _b' => false

theorem Bin.isZero_toNat (b : Bin) (h : Bin.toNat b = 0) :
  Bin.isZero b := by
  induction b
  case Z => rfl
  case B1 b' _b_ih =>
    simp [Bin.toNat] at h
    done
  case B0 b' b_ih =>
    simp [Bin.toNat] at h
    simp [Bin.isZero]
    apply b_ih
    generalize (toNat b') = x at h ⊢
    cases x
    case zero => rfl
    case succ x' =>
      rw [Nat.succ_mul] at h
      rw [Nat.add_succ] at h
      simp at h
    done

def Bin.normalize (b : Bin): Bin :=
  match b with
  | .Z => .Z
  | .B1 b' => .B1 (Bin.normalize b')
  | .B0 b' =>
    if Bin.isZero b' then
      .Z
    else
      .B0 (Bin.normalize b')

#eval Bin.normalize (.B0 .Z)
#eval Bin.normalize (.B0 (.B0 .Z))
#eval Bin.normalize (.B1 (.B0 .Z))
#eval Bin.toNat (Bin.normalize (.B0 (.B1 .Z)))
#eval Bin.toNat (.B0 (.B1 .Z))

theorem ofNat_double_zero (n : Nat) (h : n = 0):
  Bin.ofNat (n * 2) = .Z := by
  rw [h]
  rfl
  done

theorem ofNat_double_nonzero (n : Nat) (h : n ≠ 0):
  Bin.ofNat (n * 2) = .B0 (Bin.ofNat n) := by
  induction n
  case zero =>
    simp only [Bin.ofNat]
    apply h
    rfl
  case succ n' n_ih =>
    simp [Bin.ofNat, Nat.succ_add]
    rw [show n' + n' = n' * 2 from by simp_arith]
    clear h
    by_cases h : n' = 0
    case pos =>
      simp [h]
      rfl
      done
    case neg =>
      rw [n_ih h]
      rfl
      done
    done

theorem normalize_ofNat_toNat : ∀ b,
  Bin.ofNat (Bin.toNat b) = Bin.normalize b := by
  intro b
  induction b
  case Z => rfl
  case B1 b' b_ih =>
    simp only [Bin.ofNat, Bin.normalize]
    cases b'_isZero : Bin.isZero b'
    case false =>
      rw [ofNat_double_nonzero (Bin.toNat b')]
      . rw [b_ih]
        rfl
      . -- TODO: 次回はここから！
      done
    case true =>
      done
    done
  case B0 b' b_ih =>
    done
