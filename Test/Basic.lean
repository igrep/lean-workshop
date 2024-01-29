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
