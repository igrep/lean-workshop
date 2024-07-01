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

#check NatList.Cons 1 (.Cons 2 (.Cons 3 .Nil))

infixl:55 " :: " => NatList.Cons
-- TODO: 次回できたらこれも定義する
-- notation "[" a:60 ";" .. ";" b:60 "]" => NatProd.Pair a b
