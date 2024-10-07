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

-- orphan instance を避けるためにnamspace scopedにする
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
