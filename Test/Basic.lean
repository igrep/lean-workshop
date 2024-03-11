set_option autoImplicit false

def hello := "world"

inductive day : Type where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

#check day.monday
#eval day.friday

open day

def next_weekday (d: day): day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday

#check monday
#eval friday

#check next_weekday tuesday
#eval next_weekday tuesday
#eval next_weekday friday
#eval next_weekday (next_weekday saturday)

-- example は型チェックだけ行う。名前を新たに増やさない
example : (next_weekday (next_weekday saturday)) = tuesday := rfl
--       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^    ^^^
--         ここまでが型                                      ここが証明

-- これは名前を付ける。「def」とほぼ一緒
theorem some_example : (next_weekday (next_weekday saturday)) = tuesday := rfl

-- デフォルトでは、識別子を間違えていても「型エラー」になる
-- 防ぐには、「set_option autoImplicit false」を有効にしよう
set_option autoImplicit false
-- example : (next_weekday (next_weekday saturday)) = tueday := rfl
#check_failure (next_weekday (next_weekday saturday)) = tueday
#check_failure (rfl : (next_weekday (next_weekday saturday)) = monday)

namespace example1

inductive bool : Type where
  | true
  | false
  deriving Repr

open example1
#check bool.true

def negb (b: bool) : bool :=
  match b with
  | .true => .false
  | .false => .true

def andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | .true => b2
  | .false => .false

def orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | .true => .true
  | .false => b2

example : (orb .true .false) = .true := rfl
example : (orb .false .false) = .false := rfl

-- && は標準のと被るので違う名前に。
-- 前後の空白は pretty printing のために使うので、入力時は関係がない
infixl:50 " &!& " => andb
infixl:50 " |!| " => orb
#eval .true &!& .false &!& .true
#check (.true &!& .false) &!& .true
#check andb .true (orb .false .true)

-- def nandb (b1: bool) (b2: bool) : bool := sorry
def nandb (b1: bool) (b2: bool) : bool :=
  negb (b1 &!& b2)

example : (nandb .true .false) = .true := by
  rfl
example : (nandb .false .false) = .true := by
  rfl
example : (nandb .false .true) = .true := by
  rfl
example : (nandb .true .true) = .false := by
  rfl

def andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  b1 &!& b2 &!& b3

example : (andb3 .true .true .true) = .true := by
  rfl
example : (andb3 .false .true .true) = .false := by
  rfl
example : (andb3 .true .false .true) = .false := by
  rfl
example : (andb3 .true .true .false) = .false := by
  rfl

#check negb .true
#check negb
-- バックスラッシュ r か バックスラッシュ -> で →
#check (negb : bool → bool)
-- 実はカッコで囲うだけでも、仮引数の情報は消える
#check (negb)
#check andb
#check (andb)


-- コンストラクターは小文字で始めるが、
-- 型の名前は慣習上大文字で始めることが多い
inductive rgb : Type where
  | red
  | green
  | blue
  deriving Repr

inductive color : Type where
  | black
  | white
  | primary (p : rgb)
  deriving Repr

def monochrome (c : color) : bool :=
  match c with
  | .black => .true
  | .white => .true
  | .primary _q => .false

def isred (c : color) : bool :=
  match c with
  | .black => .false
  | .white => .false
  | .primary .red => .true
  -- ^ .red ではなく単に red と書くと、redがワイルドカードとして扱われてしまう！
  --   open rgb と書いていると違う（cf. isred2）
  | .primary _ => .false

open rgb
def isred2 (c : color) : bool :=
  match c with
  | .black => .false
  | .white => .false
  | .primary red => .true
  | .primary _ => .false

inductive bit : Type where
  | B0
  | B1
  deriving Repr

inductive nybble : Type where
  | bits (b0 b1 b2 b3 : bit)
  deriving Repr

/- これがブロックコメント -/
#check nybble.bits .B1 .B0 .B1 .B0
-- やっぱりカリー化されている
#check nybble.bits .B1 .B0 .B1
#check nybble.bits .B1 .B0

def all_zero (nb : nybble) : bool :=
  match nb with
  | .bits .B0 .B0 .B0 .B0 => .true
  | _ => .false

#eval (all_zero (.bits .B1 .B0 .B1 .B0))
#eval (all_zero (.bits .B0 .B0 .B0 .B0))

end example1

namespace NatPlayground

inductive nat : Type where
  | O
  | S (n : nat)
  deriving Repr

-- ちなみに組み込みのNatはこちら
#eval Nat.succ .zero

open nat

def Nat2nat (n : Nat) : nat :=
  match n with
    | .zero => O
    | .succ n' => S (Nat2nat n')

instance : OfNat nat .zero where
  ofNat := O

-- set_option autoImplicit false にしている場合、
-- 変数の宣言をしないと「unknown identifier n'」になる
instance (n' : Nat) : OfNat nat (n') where
  ofNat := Nat2nat n'

example : Nat2nat 3 = S (S (S O)) := rfl

#eval (3 : nat)
#eval (0 : nat)

#eval Lean.versionString

def pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'

#eval pred O
#eval pred (S O)
#eval pred (S (S O))

def plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)

def mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)

def minus (n m : nat) : nat :=
  match n   , m with
    | O   , _ => O
    | S _ , O => n
    | S n', S m' => minus n' m'

def exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)

def factorial (n : nat) : nat :=
  match n with
    | .O => S O
    | (S n') => mult n (factorial n')

example : factorial 3 = 6 := rfl

example : factorial 5 = mult 10 12 := rfl

infixl:50 " +!+ " => plus
infixl:50 " -!- " => minus
infixl:60 " *!* " => mult

example : (3 +!+ 2 *!* 0) = 3 := rfl

def eqb (n m : nat) : Bool :=
  match n with
  | O =>
  /-
  -- ここまでOK
  match m with
 -- これはダメ
 match m with
  -/
    match m with
      | O => true
      | S _m' => false
  | S n' =>
    match m with
      | O => false
      | S m' => eqb n' m'

def leb (n m : nat) : Bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'

infixl:30 " =? " => eqb
infixl:30 " <=? " => leb

def ltb (n m : nat) : Bool :=
  if n =? m
    then false
    else n <=? m

example : (ltb 2 2) = false := rfl
example : (ltb 2 4) = true := rfl
example : (ltb 2 3) = true := rfl
example : (ltb 4 2) = false := rfl
example : (ltb 3 2) = false := rfl

theorem plus_O_n' : ∀ (n : nat), (0 +!+ n) = n := by
  -- intro （またはintros）で n を導入しないと「等式を返す関数」なので
  -- rflで照明できない（等式ではないので）
  intro
  rfl

#print plus_O_n'

theorem plus_O_n'' : ∀ (n : nat), (0 +!+ n) = n :=
  fun n => @rfl nat n

-- lemma は Mathlib に: https://github.com/leanprover-community/mathlib4/blob/e903c3fc8ef8b337628c4c5e5f545828d7c63499/Mathlib/Tactic/Lemma.lean#L14-L16

theorem plus_id_example : ∀ (n m : nat),
  n = m → (n +!+ n) = (m +!+ m) := by
  intro n m H
  -- 「rewrite [←H]」逆向きの変換
  rewrite [H]
  rfl

theorem plus_id_exercise : ∀ (n m o : nat),
  n = m -> m = o -> (n +!+ m) = (m +!+ o) := by
  intro n m o H1 H2
  rewrite [H1, H2]
  rfl

theorem mult_0_plus : ∀ (n m : nat),
  ((0 +!+ n) *!* m) = (n *!* m) := by
  intros
  rewrite [plus_O_n']
  rfl

#print mult_0_plus

theorem mult_S_1 : ∀ n m : nat,
  m = S n -> (m *!* (1 +!+ n)) = (m *!* m) := by
  intro n m H

  -- 「plus 関数で式を簡約せよ」という意味
  --  実際にはここでは不要だった！
  -- simp [plus]

  rewrite [H]
  rfl

theorem plus_1_neq_0_firsttry : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n
  sorry

theorem plus_1_neq_0 : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n
  cases n
  case O => rfl
  case S n' => rfl
  -- 最初に書いておくと証明が終わってない場合に赤線が出て分かりやすい
  done

-- plus_1_neq_0 の他の書き方
theorem plus_1_neq_0' : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n
  cases n
  . rewrite [] -- · や {} でもよい
    rfl
  . rewrite []
    rfl
  done
theorem plus_1_neq_0'' : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n
  cases n
  rewrite [] -- 何もしないtacticとして
  rfl
  rewrite []
  rfl
  done
theorem plus_1_neq_0''' : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n
  cases n with
  | O => rfl
  | S n' => rfl
  done
-- 短くまとめるバージョン。
-- <;> は Coq の ; 相当
theorem plus_1_neq_0'''' : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro n ; cases n <;> rfl
  done
theorem plus_1_neq_0''''' : ∀ n : nat,
  ((n +!+ 1) =? 0) = false := by
  intro
  | O => rfl
  | S n' => rfl
  done

theorem negb_involutive : ∀ b : Bool,
  ! (! b) = b := by
  intro b ; cases b
  case true => rfl
  case false => rfl
  done

theorem andb_commutative : ∀ b c, and b c = and c b := by
  intro b c
  cases b
  case true =>
    cases c
    case true => rfl
    case false => rfl
  case false =>
    cases c
    case true => rfl
    case false => rfl
  done
theorem andb_commutative' : ∀ b c, and b c = and c b := by
  intro
  | true =>
    intro
    | true => rfl
    | false => rfl
  | false =>
    intro
    | true => rfl
    | false => rfl
  done
theorem andb_commutative'' : ∀ b c, and b c = and c b := by
  intro b c ; cases b <;> cases c <;> rfl
  done

theorem andb_true_elim2 : ∀ b c : Bool,
  and b c = true → c = true := by
  intro b c H
  cases b
  case true =>
    cases c
    case true => rfl
    case false =>
      rewrite [← H]
      rfl
  case false =>
      rewrite [← H]
      cases c
      case false => rfl
      case true =>
        rewrite [H]
        rfl
  done

theorem zero_nbeq_plus_1 : ∀ n : nat,
  (0 =? (n +!+ 1)) = false := by
  done

end NatPlayground

-- 標準の Nat では Nat.zero_add
#check Nat.zero_add

def minusTwo (n : Nat) : Nat :=
  match n with
    | .zero => .zero
    | .succ .zero => .zero
    | .succ (.succ n') => n'

#eval minusTwo 4
#check Nat.succ
#check Nat.pred
#check minusTwo

def evenb (n : Nat) : Bool :=
  match n with
  | .zero => true
  | .succ .zero => false
  | .succ (.succ n') => evenb n'

def oddb (n : Nat) : Bool := not (evenb n)
def oddbPointfree : Nat → Bool := not ∘ evenb
#print oddb
#print oddbPointfree

universe u v w

def comp' {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=
  fun x => f (g x)

def oddbPointfree' : Nat → Bool := comp' not evenb

-- inline の有無は関係なく、展開した関数で証明できる！
example: oddb = oddbPointfree := rfl
example: oddb = oddbPointfree' := rfl
example: oddb 1 = true := rfl
example: oddb 4 = false := rfl

def plus (n m : Nat) : Nat :=
  match n with
    | .zero => m
    | .succ n' => .succ (plus n' m)

def plus' (m : Nat) : (Nat) → Nat
    | .zero => m
    | .succ n' => .succ (plus' m n')

-- TODO: 後で証明
example: ∀ n m, plus n m = plus' m n := sorry

#eval plus 3 2


def mult (n m : Nat) : Nat :=
  match n with
    | .zero => .zero
    | .succ n' => plus m (mult n' m)

def minus (n m : Nat) : Nat :=
  match n   , m with
  | .zero   , _ => .zero
  | .succ _ , .zero => n
  | .succ n', .succ m' => minus n' m'

def exp (base power : Nat) : Nat :=
  match power with
    | .zero => .succ .zero
    | .succ p => mult base (exp base p)
