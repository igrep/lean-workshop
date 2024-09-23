import Test.Lists


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
