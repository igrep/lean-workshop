import Test.Basic

def div2 (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | n + 2 => (div2 n) + 1

def csf (n : Nat) : Nat :=
  if evenb n then div2 n
  else (3 * n) + 1

partial def reaches1_in (n : Nat) : Nat :=
  if n == 1 then 0
  else 1 + reaches1_in (csf n)

#eval! reaches1_in 6
#eval! reaches1_in 19

partial def Collatz_holds_for_FAIL (n : Nat) : Prop :=
  match n with
  | 0 => False
  | 1 => True
  | _ => if evenb n
    then Collatz_holds_for_FAIL (div2 n)
    else Collatz_holds_for_FAIL ((3 * n) + 1)

inductive Collatz_holds_for : Nat → Prop :=
  | Chf_one : Collatz_holds_for 1
  | Chf_even
      (n : Nat)
      (heven : evenb n = true)
      (h : Collatz_holds_for (div2 n))
      : (Collatz_holds_for n)
  | Chf_odd
      (n : Nat)
      (hodd : evenb n = false)
      (h : Collatz_holds_for ((3 * n) + 1))
      : Collatz_holds_for n

open Collatz_holds_for in
example : Collatz_holds_for 12 := by
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_odd ; rfl ; simp
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_odd ; rfl ; simp
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_even ; rfl ; simp [div2]
  apply Chf_one
  done

inductive le : Nat → Nat → Prop where
  | le_n (n : Nat) : le n n
  | le_S (n m : Nat) : le n m → le n (m + 1)

-- ここからは標準の Nat.le を使う

#print Nat.le
#print Nat.le.refl
#print Nat.le.step

example : 3 ≤ 5 := by
  apply Nat.le.step
  apply Nat.le.step
  apply Nat.le.refl
  done

inductive clos_trans {X: Type} (R: X → X → Prop) : X → X → Prop where
  | t_step
    {x y : X}
    (h : R x y)
    : clos_trans R x y
  | t_trans
    {x y z : X}
    (h1 : clos_trans R x y)
    (h2 : clos_trans R y z)
    : clos_trans R x z

inductive Person : Type where
  | Sage
  | Cleo
  | Ridley
  | Moss

inductive parent_of : Person → Person → Prop
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss

def ancestor_of : Person → Person → Prop :=
  clos_trans parent_of

example : ancestor_of .Sage .Moss := by
  unfold ancestor_of
  apply clos_trans.t_trans (y := .Cleo)
  · apply clos_trans.t_step
    apply parent_of.po_SC
  · apply clos_trans.t_step
    apply parent_of.po_CM

inductive clos_refl_trans
  {X: Type}
  (R: X → X → Prop)
  : X → X → Prop where
  | rt_step
    {x y : X}
    (h : R x y)
    : clos_refl_trans R x y
  | rt_refl
    {x : X}
    : clos_refl_trans R x x
  | rt_trans
    {x y z : X}
    (h1 : clos_refl_trans R x y)
    (h2 : clos_refl_trans R y z)
    : clos_refl_trans R x z

def cs (n m : Nat) : Prop := csf n = m

def cms n m := clos_refl_trans cs n m


