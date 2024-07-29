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

def Bag.removeOne (v: Nat) (s: Bag): Bag :=
  match s with
  | [||] => s
  | h :: t =>
    if h == v then
      t
    else
      h :: removeOne v t

#guard Bag.count 5 (Bag.removeOne 5 [|2;1;5;4;1|]) = 0
#guard Bag.count 5 (Bag.removeOne 5 [|2;1;4;1|]) = 0
#guard Bag.count 4 (Bag.removeOne 5 [|2;1;4;5;1;4|]) = 2
#guard Bag.count 5 (Bag.removeOne 5 [|2;1;5;4;5;1;4|]) = 1

def Bag.removeAll (v: Nat) (s: Bag): Bag :=
  s.filter (· ≠ v)

#guard Bag.count 5 (Bag.removeAll 5 [|2;1;5;4;1|]) = 0
#guard Bag.count 5 (Bag.removeAll 5 [|2;1;4;1|]) = 0
#guard Bag.count 4 (Bag.removeAll 5 [|2;1;4;5;1;4|]) = 2
#guard Bag.count 5 (Bag.removeAll 5 [|2;1;5;4;5;1;4;5;1;4|]) = 0

def Bag.subset (s1: Bag) (s2: Bag): Bool :=
  match s1 with
  | [||] => true
  | h1 :: t1 =>
    if Bag.member h1 s2 then
      Bag.subset t1 (Bag.removeOne h1 s2)
    else
      false

#guard Bag.subset [|1;2|] [|2;1;4;1|] = true
#guard Bag.subset [|1;2;2|] [|2;1;4;1|] = false

example : ∀ (n : Nat) (s: Bag),
  Bag.count n (Bag.removeAll n s) = 0 := by
  intro n s
  induction s
  case Nil =>
    rfl
    done
  case Cons h t t_ih =>
    -- decide: PropじゃなくてBoolを返さないといけないので変換する関数
    rw [Bag.removeAll, NatList.filter]
    split -- if式を分割する
    case inl =>
      rw [Bag.count, NatList.filter]
      split
      case inl =>
        -- simp_all だけでもよい！simp_allすごい！
        rename_i h1 h2
        simp at h1 h2
        contradiction
        done
      case inr =>
        rw [Bag.removeAll, Bag.count] at t_ih
        exact t_ih
        done
    case inr =>
      rw [Bag.removeAll] at t_ih
      exact t_ih
      done

theorem nil_app : ∀ l : NatList, [||] ++ l = l := by
  intros
  rfl

theorem tl_length_pred : ∀ l : NatList,
  (l.length).pred = (tl l).length := by
  intro l
  cases l
  case Nil => rfl
  case Cons _h _t => rfl


theorem app_assoc :∀ l1 l2 l3 : NatList,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3) := by
  intro l1 l2 l3
  induction l1
  case Nil =>
    rfl
    done
  case Cons h l1_t ih_l1_t =>
    simp [HAppend.hAppend, Append.append, NatList.append]
    exact ih_l1_t
    done

def NatList.rev (l : NatList): NatList :=
  match l with
  | [||] => [||]
  | h :: t => t.rev ++ [|h|]

#guard [|1;2;3|].rev = [|3;2;1|]

theorem rev_length_firsttry : ∀ l : NatList,
  l.rev.length = l.length := by
  intro l
  induction l
  case Nil =>
    rfl
    done
  case Cons n l' ih_l' =>
    rw [NatList.rev, NatList.length, ← ih_l']
    sorry

theorem app_length : ∀ l1 l2 : NatList,
  (l1 ++ l2).length = l1.length + l2.length := by
  intro l1 l2
  induction l1
  case Nil =>
    simp [
      HAppend.hAppend,
      Append.append,
      NatList.append,
      NatList.length,
      ]
    done
  case Cons h l1_t ih_l1_t =>
    simp [
      HAppend.hAppend,
      Append.append,
      NatList.append,
      NatList.length,
      ] at ih_l1_t ⊢
      -- ^^^^^^^^^^^^
      -- ⊢ は、goalを表す記号。ih_l1_tとgoal両方をrwする
    rw [
      ih_l1_t,
      Nat.add_assoc,
      Nat.add_comm l2.length,
      Nat.add_assoc,
      ]
      -- ac_rfl でもよい
    done

theorem rev_length : ∀ l : NatList,
  l.rev.length = l.length := by
  intro l
  induction l
  case Nil =>
    rfl
    done
  case Cons n l' ih_l' =>
    rw [
      NatList.rev,
      NatList.length,
      app_length,
      ih_l',
      ]
    rfl
    done

@[simp]
theorem app_cons : ∀ (l l' : NatList) (n : Nat),
  (n :: l) ++ l' = n :: (l ++ l') := by
  intros
  rfl

@[simp]
theorem app_nil_l : ∀ l : NatList,
  [||] ++ l = l := by
  intros
  rfl

@[simp]
theorem app_nil_r : ∀ l : NatList,
  l ++ [||] = l := by
  intro l
  induction l
  case Nil =>
    rfl
    done
  case Cons h l' ih_l' =>
    simp
    rw [ih_l']
    done

theorem rev_app_distr: ∀ l1 l2 : NatList,
  (l1 ++ l2).rev = l2.rev ++ l1.rev := by
  intro l1 l2
  induction l1
  case Nil =>
    rw [NatList.rev]
    simp
    done
  case Cons h l1_t ih_l1_t =>
    simp
    rw [
      NatList.rev,
      ih_l1_t,
      NatList.rev,
      app_assoc,
      ]
    done

theorem rev_involutive : ∀ l : NatList,
  l.rev.rev = l := by
  intro l
  induction l
  case Nil =>
    rfl
    done
  case Cons h l' ih_l' =>
    rw [NatList.rev, rev_app_distr, ih_l']
    rfl
    done
