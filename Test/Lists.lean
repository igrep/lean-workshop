import Test.Induction

inductive NatProd : Type where
  | Pair (n1 n2 : Nat)
  deriving Repr

#check NatProd.Pair 1 0

def fst (p : NatProd) : Nat :=
  match p with
  | NatProd.Pair x _y => x

def snd (p : NatProd) : Nat :=
  match p with
  | NatProd.Pair _x y => y

#eval fst (.Pair 3 5)
#eval snd (.Pair 3 5)

notation "(|" a:60 ", " b:60 "|)" => NatProd.Pair a b

#eval (|1, 4|)

def fst' (p : NatProd) : Nat :=
  match p with
  | (|x, _y|) => x

def snd' (p : NatProd) : Nat :=
  match p with
  | (|_x, y|) => y

def swap_pair (p : NatProd) : NatProd :=
  match p with
  | (|x, y|) => (|y, x|)

#eval fst' (.Pair 3 5)
#eval snd' (.Pair 3 5)
#eval swap_pair (.Pair 3 5)

theorem surjective_pairing' : ∀ (n m : Nat),
  (|n, m|) = (|fst (|n, m|), snd (|n, m|)|) := by
  intro n m
  rfl

theorem surjective_pairing_stuck : ∀ (p : NatProd),
  p = (|fst p, snd p|) := by
  intro p
  rfl

theorem snd_fst_is_swap : ∀ (p : NatProd),
  (|snd p, fst p|) = swap_pair p := by
  intro p
  rfl

theorem fst_swap_is_snd : ∀ (p : NatProd),
  fst (swap_pair p) = snd p := by
  intro p
  rfl

inductive NatList : Type where
  | Nil
  | Cons (n : Nat) (l : NatList)
  deriving DecidableEq

def NatList.toString (xs : NatList): String :=
  "[|" ++ go xs ++ "|]"
 where
  go l :=
    match l with
    | Nil => ""
    | Cons x Nil =>
      ToString.toString x
    | Cons x xs' =>
      ToString.toString x ++ ";" ++ go xs'

#eval NatList.Nil.toString
#eval (NatList.Cons 1 .Nil).toString
#eval (NatList.Cons 2 (NatList.Cons 1 .Nil)).toString
#eval (NatList.Cons 3 (NatList.Cons 2 (NatList.Cons 1 .Nil))).toString

instance : ToString NatList where
  toString := NatList.toString

#check NatList.Cons 1 (.Cons 2 (.Cons 3 .Nil))

infixl:55 " :: " => NatList.Cons
-- https://lean-lang.org/lean4/doc/syntax_example.html
-- [] は被ってしまうので[||]で囲う
declare_syntax_cat NatSeq
-- term: 予約済みの任意のLeanの式を表す非終端記号
---- termがNatSeqになり得ることを表す
syntax term : NatSeq
syntax term ";" NatSeq : NatSeq
---- termに [| NatSeq0個か1個 |] を追加する
syntax "[|" NatSeq ? "|]" : term

-- 追加した構文を利用したマクロの定義
macro_rules
  | `([||]) => `(NatList.Nil)
  | `([|$t:term|]) => `(NatList.Cons $t NatList.Nil)
  | `([|$t1:term; $t2|]) => `(NatList.Cons $t1 [|$t2|])

#check [||]
#check [|1|]
#check [|1; 2|]
#check [|1; 2; 3|]

#eval [||]
#eval [|1|]
#eval [|1; 2|]
#eval [|1; 2; 3|]
-- notation "[" a:60 ";" .. ";" b:60 "]" => NatProd.Pair a b

def NatList.repeat (n count : Nat) : NatList :=
  match count with
  | .zero => .Nil
  | .succ count' => n :: (NatList.repeat n count')
  /- Leanだとこうも書ける。こちらの方が主流
  | 0 => .Nil
  | count' + 1 => n :: (repeatN n count')
  -/
def NatList.length (l : NatList) : Nat :=
  match l with
  | [||] => 0
  | _h :: t => (length t) + 1

def NatList.append (l1 l2 : NatList) : NatList :=
  match l1 with
  | [||] => l2
  | h :: t => h :: (NatList.append t l2)

instance : Append NatList where
  append := NatList.append

#eval [|3; 4; 5|] ++ [| 9; 8; 7|]
example : [|1;2;3|] ++ [|4;5|] = [|1;2;3;4;5|] := rfl

-- Leanの銘々の慣習ではheadD（Dは「default」のD）
def hd (default : Nat) (l : NatList) : Nat :=
  match l with
  | [||] => default
  | h :: _t => h

def tl (l : NatList) : NatList :=
  match l with
  | [||] => [||]
  | _h :: t => t

example : hd 0 [|1; 2; 3|] = 1 := rfl
example : hd 0 [||] = 0 := rfl
example : tl [|1; 2; 3|] = [|2; 3|] := rfl
example : tl [||] = [||] := rfl

def nonzeros (l : NatList) :=
  match l with
  | [||] => [||]
  | h :: t =>
    if h = 0 then
      nonzeros t
    else
      h :: nonzeros t

example : nonzeros [|0;1;0;2;3;0;0|] = [|1;2;3|] := rfl

def oddMembers (l : NatList) :=
  match l with
  | [||] => [||]
  | h :: t =>
    if h % 2 = 1 then
      h :: oddMembers t
    else
      oddMembers t

example : oddMembers [|0;1;0;2;3;0;0|] = [|1;3|] := rfl

def countOddMembers : NatList -> Nat :=
  NatList.length ∘ oddMembers

example : countOddMembers [|1;0;3;1;4;5|] = 4 := rfl
#guard countOddMembers [|0;2;4|] = 0
#guard countOddMembers [||] = 0

def alternate (l1 l2: NatList): NatList :=
  match l1, l2 with
  | [||], _ => l2
  | _, [||] => l1
  | h1 :: t1, h2 :: t2 =>
    h1 :: (h2 :: (alternate t1 t2))

#guard alternate [|1; 2; 3|] [|4; 5; 6|] = [|1; 4; 2; 5; 3; 6|]
#guard alternate [|1|] [|4; 5; 6|] = [|1; 4; 5; 6|]
#guard alternate [|1; 2; 3|] [|4|] = [|1; 4; 2; 3|]
#guard alternate [||] [|20; 30|] = [|20; 30|]

def NatList.filter (p : Nat → Bool) (l : NatList) : NatList :=
  match l with
  | [||] => [||]
  | h :: t =>
    if p h then
      h :: t.filter p
    else
      t.filter p

def Bag := NatList
def Bag.count (v : Nat) (s: Bag): Nat :=
  s.filter (· == v) |>.length

#guard Bag.count 1 [|1;2;3;1;4;1|] = 3
#guard Bag.count 6 [|1;2;3;1;4;1|] = 0

def Bag.sum : Bag -> Bag -> Bag := NatList.append

#guard Bag.count 1 (Bag.sum [|1;2;3|] [|1;4;1|]) = 3

-- def Bag.add (v : Nat) (s : Bag) : Bag := v :: s
def Bag.add : Nat → Bag → Bag := .Cons

#guard Bag.count 1 (Bag.add 1 [|1;4;1|]) = 3
#guard Bag.count 5 (Bag.add 1 [|1;4;1|]) = 0

def Bag.member (n : Nat) (l : NatList) : Bool :=
  match l with
  | [||] => false
  | h :: t => h == n || member n t

#guard Bag.member 1 [|1; 4; 1|] = true
#guard Bag.member 2 [|1; 4; 1|] = false

@[noinline]
def cheat (b : Bool) : Bool :=
  dbg_trace (s! "evaluated! {b}") ; b

-- 「||」 は短絡評価になっている？
#eval cheat true || cheat false
#eval cheat false || cheat true
#eval cheat false || cheat false
---- ↓だと最適化のせいか、dbg_traceが出力されない！
#eval true || (dbg_trace "evaluated!" ; false)
#eval (dbg_trace "evaluated!" ; false) || true
#eval (dbg_trace "evaluated!" ; false) || false
