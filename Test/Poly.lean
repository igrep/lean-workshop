import Test.Lists

-- inductiveの型で使われているパラメーター（この場合X）を
-- 値コンストラクターで使っていない場合 implicit になる
inductive MyList (X : Type) : Type :=
  | Nil
  | Cons (x : X) (l : MyList X)

-- アットマーク @ で、implicitな引数を強引にexplicitにする
#check @MyList.Nil Nat
#check MyList.Nil (X := Nat)
#check (@MyList.Cons Nat 3 (@MyList.Nil Nat))
#check (@MyList.Cons _ 3 (@MyList.Nil _)) -- もちろんholeにしても推論してくれる
#check MyList.Nil
#check MyList.Cons
-- 最初からimplicitなので、特に型を明示する必要はなし！
#check MyList.Cons 2 (.Cons 1 .Nil)

-- 改めて記法などを定義するのも面倒なので、
-- 以降は組み込みのListを使う

-- repeat は組み込みのtacticらしいのでmyRepeatに。
def myRepeat (X : Type) (x : X) (count : Nat) : List X :=
  match count with
  | 0 => .nil
  | count' + 1 => .cons x (myRepeat X x count')

#guard myRepeat Nat 4 2 = .cons 4 (.cons 4 .nil)
#guard myRepeat Bool false 1 = [false]

section MumbleGrumble

inductive Mumble : Type :=
  | a
  | b (x : Mumble) (y : Nat)
  | c

inductive Grumble (X : Type) : Type :=
  | d (m : Mumble)
  | e (x : X)

open Mumble Grumble

#check d (b a 5) -- Coqだと、型引数を明示していないのでエラーになるはず
#check @d Mumble (b a 5)
#check @d Bool (b a 5)
#check @e Bool true
#check @e Mumble (b c 0)
#check_failure @e Bool (b c 0)
#check c -- 唯一、型が通るけどGrumble型にならないケース

end MumbleGrumble

-- 返値の型を明示した場合、
-- 関数本体から引数の型を推論できた場合でも、
-- 引数の型を明示しないと型エラーになる。
-- なのでここでは返値の型も省略
def repeat' X x count :=
  match count with
  | 0 => @List.nil X
  | count' + 1 => @List.cons X x (repeat' X x count')

#check repeat'
#check myRepeat

def id' X (x : X) := x
def id'' X x := (x : X)
#check id' Nat 9
#check id'' Nat 9

def repeat''' {X : Type} (x : X) (count : Nat) : List X :=
  match count with
  | 0 => .nil
  | count' + 1=> .cons x (repeat''' x count')

-- Xを暗黙の引数としているので、
-- .true だとどの型の true か分からずエラーに。
#eval repeat''' true 3

-- 値コンストラクターも型自身のパラメーターもimplicit
inductive List' {X : Type} : Type where
  | Nil'
  | Cons' (x : X) (l : @List' X)

#check List'.Nil'
#check List'.Cons'

def app {X : Type} (l1 l2 : List X) : (List X) :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)

def rev {X : Type} (l : List X) : List X :=
  match l with
  | [] => []
  | h :: t => (rev t) ++ [h]

def length {X : Type} (l : List X) : Nat :=
  match l with
  | [] => 0
  | _ :: l' => .succ (length l')

#guard rev [1, 2] = [2, 1]
#guard rev [true] = [true]
#guard length [1, 2, 3] = 3

-- これはエラーに（CoqのFail相当の命令がなかったのでコメントアウト）
-- def myNil := []

def myNil : List Nat := .nil
def myNil' := @List.nil Nat

infixl:55 " :: " => MyList.Cons
-- https://lean-lang.org/lean4/doc/syntax_example.html
-- [] は被ってしまうので[||]で囲う
declare_syntax_cat ElemSeq
-- term: 予約済みの任意のLeanの式を表す非終端記号
---- termがElemSeqになり得ることを表す
syntax term : ElemSeq
syntax term ";" ElemSeq : ElemSeq
---- termに [| NatSeq0個か1個 |] を追加する
syntax "[|" ElemSeq ? "]" : term

-- 追加した構文を利用したマクロの定義
macro_rules
  | `([|]) => `(MyList.Nil)
  | `([|$t:term]) => `(MyList.Cons $t MyList.Nil)
  | `([|$t1:term; $t2]) => `(MyList.Cons $t1 [|$t2])

def list123''' := [|1; 2; 3]
#check list123'''
#check [|]
#check [|""]
#check [|""; "a"]

theorem app_nil_r_poly : ∀ (X : Type), ∀ l : List X,
  l ++ [] = l := by
  intro X l
  induction l
  case nil => rfl
  case cons h t t_ih =>
    rw [List.cons_append, t_ih]
  done

theorem app_assoc_poly : ∀ A (l m n : List A),
  -- 両辺のカッコを明示しよう。Leanでは左結合らしい
  l ++ (m ++ n) = (l ++ m) ++ n := by
  intro A l m n
  induction l
  case nil =>
    rfl
  case cons h t t_ih =>
    rw [List.cons_append, t_ih]
    rfl
  done

theorem app_length_poly : ∀ (X : Type) (l1 l2 : List X),
  length (l1 ++ l2) = length l1 + length l2 := by
  intro X l1 l2
  rw [Nat.add_comm]
  induction l1
  case nil =>
    rfl
  case cons h t t_ih =>
    rw [List.cons_append]
    rw [length, length, t_ih, Nat.add_succ]
  done

theorem rev_app_distr_poly: ∀ X (l1 l2 : List X),
  rev (l1 ++ l2) = rev l2 ++ rev l1 := by
  intro X l1 l2
  induction l1
  case nil =>
    rw [rev, List.nil_append, app_nil_r_poly]
  case cons h t t_ih =>
    rw [rev, List.cons_append, rev, app_assoc_poly, t_ih]

theorem rev_involutive_poly : ∀ X : Type, ∀ l : List X,
  rev (rev l) = l := by
  intro X l
  induction l
  case nil => rfl
  case cons h t t_ih =>
    rw [
      rev,
      rev_app_distr_poly,
      rev,
      rev,
      List.nil_append,
      List.cons_append,
      List.nil_append,
      t_ih
      ]

inductive MyProd (X Y : Type) : Type where
| Pair (x : X) (y : Y)
deriving Repr, DecidableEq

notation "(|" a:60 ", " b:60 ")" => MyProd.Pair a b
#check (|1, 2)
#check (|1, false)

-- Lean標準のpair。右結合らしい
#check (99, ("", true))
#check (99, "", true)
#check ((99, ""), true)

namespace MyProd
-- -- type_scope はLeanにはないっぽい？
-- scoped instance : Mul Type where
--   mul a b := MyProd a b
-- scoped instance {a b : Type} : DecidableEq (a * b) where

infixr :60 " *, " => MyProd

#check Nat *, Bool

def fst {X Y : Type} (p : X *, Y) : X :=
  match p with
  | (|x, _y) => x

def snd {X Y : Type} (p : X *, Y) : Y :=
  match p with
  | (|_x, y) => y

def combine
  {X Y : Type}
  (lx : List X)
  (ly : List Y)
  : List (X *, Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (|x, y) :: combine tx ty

#check combine
#eval combine [1,2] [false, false, true, true]

def split
  {X Y : Type}
  (l : List (X *, Y))
  : (List X) *, (List Y) :=
  match l with
  | [] => (|[], [])
  | (|x, y) :: l' =>
    match split l' with
    | (|xs, ys) => (|x :: xs, y :: ys)

#check split
#check split [(|1, false), (|2, false)]
#check (|[1, 2], [false, false])
#guard split [(|1, false), (|2, false)] = (|[1, 2], [false, false])

end MyProd

#check Option.some 1

namespace OptionPlayground

inductive Option (X : Type) : Type where
  | Some (x : X)
  | None : Option X
  deriving DecidableEq

def nth_error
  {X : Type}
  (l : List X)
  (n : Nat) : Option X :=
  match l with
  | [] => Option.None
  | a :: l' =>
    if n = 0 then Option.Some a else nth_error l' n.pred

-- = は本来Prop用なので、BEq用の == を使う
#guard nth_error [4,5,6,7] 0 == Option.Some 4
#guard nth_error [[1],[2]] 1 == Option.Some [2]
#guard nth_error [true] 2 == Option.None

def hd_error {X : Type} (l : List X) : Option X :=
  match l with
  | [] => Option.None
  | a :: _ => Option.Some a

#check hd_error
#check @hd_error Nat
#check hd_error (X := Nat)

#guard hd_error [1,2] == Option.Some 1
#guard hd_error [[1],[2]] == Option.Some [1]
#guard hd_error (X := Bool) [] == Option.None

end OptionPlayground

def doit3times {X : Type} (f : X → X) (n : X) : X :=
  f (f (f n))

#guard doit3times (· - 2) 9 == 3
#guard doit3times Bool.not true == false

def filter
  {X : Type}
  (test : X → Bool)
  (l : List X) : (List X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then
      h :: (filter test t)
    else
      filter test t

#guard filter evenb [1, 2, 3, 4] == [2, 4]

def length_is_1 {X : Type} (l : List X) : Bool :=
  (length l) =? 1

#guard filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  == [ [3], [4], [8] ]

def countOddMembers' (l : List Nat) : Nat :=
  length (filter oddb l)

#guard countOddMembers' [1, 0, 3, 1, 4, 5] = 4
#guard countOddMembers' [0, 2, 4] = 0
#guard countOddMembers' .nil = 0

#guard doit3times (fun n => n * n) 2 = 256
#guard filter (fun l => (length l) =? 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ]

def filter_even_gt7 (l : List Nat) : List Nat :=
  l.filter (fun n => evenb n && n > 7)

#guard filter_even_gt7 [1, 2, 6, 9, 10, 3, 12, 8]
  == [10, 12, 8]

#guard filter_even_gt7 [5, 2, 6, 19, 129] = []

def partition
  {X : Type}
  (test : X -> Bool)
  (l : List X) : List X × List X :=
  (filter test l, filter (fun x => (test x).not) l)

#guard partition oddb [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4])
#guard partition (fun _x => false) [5, 9, 0] = ([], [5, 9, 0])

def map {X Y : Type} (f : X → Y) (l : List X) : (List Y) :=
  match l with
  | [] => []
  | h :: t => f h :: map f t

#guard map (fun x => plus 3 x) [2, 0, 2] = [5, 3, 5]
#guard map oddb [2, 1, 2, 5] = [false, true, false, true]
#guard map (fun n => [evenb n, oddb n]) [2, 1, 2, 5]
  = [[true, false], [false, true], [true, false], [false, true]]

theorem map_append_distrib
  : ∀ (X Y : Type) (f : X -> Y) (l1 l2 : List X),
  map f (l1 ++ l2) = map f l1 ++ map f l2 := by
  intro X Y f l1 l2
  induction l1
  case nil => rfl
  case cons h1 t1 t1_ih =>
    simp [map, t1_ih]
    done

theorem map_rev : ∀ (X Y : Type) (f : X -> Y) (l : List X),
  map f (rev l) = rev (map f l) := by
  intro X Y f l
  induction l
  case nil => rfl
  case cons h t t_ih =>
    simp [
      rev,
      map,
      map_append_distrib,
      t_ih,
      ]
  done

def flat_map
  {X Y: Type}
  (f: X -> List Y)
  (l: List X) : (List Y) :=
  match l with
  | [] => []
  | h :: t => f h ++ flat_map f t

#guard flat_map (fun n => [n, n+1, n+2]) [1, 5, 10]
      = [1,  2,  3,  5,  6,  7,  10,  11,  12]
#guard flat_map (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4]

def option_map
  {X Y : Type}
  (f : X -> Y)
  (xo : Option X) : Option Y :=
  match xo with
    | .none => .none
    | .some x => .some (f x)

#guard @flat_map Nat Nat (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4]
#guard flat_map (Y := Nat) (X := Nat) (fun n => [n, n, n]) [1, 5, 4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4]
#guard partition (X := Nat) (fun _x => false) [5, 9, 0] = ([], [5, 9, 0])

def fold
  {X Y : Type}
  (f: X → Y → Y)
  (l: List X)
  (b: Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)

#check fold and
#guard fold mult [1, 2, 3, 4] 1 = 24
#guard fold and [true, true, false, true] true = false
#guard fold app [[1], [], [2, 3], [4]] [] = [1, 2, 3, 4]

def filter'
  {X : Type}
  (test : X → Bool)
  (l : List X) : (List X) :=
  fold (fun x l' => if test x then (x :: l') else l' ) l []

theorem filter_filter'
  : ∀
  {X : Type}
  (test : X → Bool)
  (l : List X),
  filter test l = filter' test l := by
  intro X test l
  induction l
  case nil => rfl
  case cons h t t_ih =>
    rw [filter, t_ih]
    rfl
