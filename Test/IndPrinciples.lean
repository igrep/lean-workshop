/- 
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat)
-/
#check (Nat.rec :
  ∀ {P : Nat → Prop},
  P 0 →
  (∀ (n : Nat), P n → P n.succ) →
  ∀ (n : Nat), P n)

theorem mul_0_r' : ∀ n : Nat,
  0 * n = 0 := by
  apply Nat.rec
  · rfl
  · intro n IH
    show (0 * n) + 0 = 0
    rw [IH]

theorem plus_one_r' : ∀ n : Nat,
  1 + n = n.succ := by
  apply Nat.rec
  · rfl
  · intro n IH
    show (1 + n).succ = n.succ.succ
    rw [IH]


inductive time : Type where
  | day
  | night

#check (time.rec :
    ∀ {P : time → Prop},
    P time.day →
    P time.night →
    ∀ (t : time), P t)

inductive rgb : Type :=
  | red
  | green
  | blue

#check (rgb.rec :
    ∀ {P : rgb → Prop},
    P rgb.red →
    P rgb.green →
    P rgb.blue →
    ∀ (c : rgb), P c)


inductive natlist : Type where
  | nnil
  | ncons (n : Nat) (l : natlist)

#check (natlist.rec :
    ∀ {P : natlist → Prop},
    P natlist.nnil →
    (∀ (n : Nat) (l : natlist), P l → P (natlist.ncons n l)) →
    ∀ (l : natlist), P l)

inductive natlist' : Type where
  | nnil'
  | nsnoc (l : natlist') (n : Nat)

#check (natlist'.rec :
    ∀ {P : natlist' → Prop},
    P natlist'.nnil' →
    (∀ (l : natlist') (n : Nat), P l → P (natlist'.nsnoc l n)) →
    ∀ (l : natlist'), P l)


inductive booltree : Type where
  | bt_empty
  | bt_leaf (b : Bool)
  | bt_branch (b : Bool) (t1 t2 : booltree)

#check (booltree.rec :
    ∀ {P : booltree → Prop},
    P booltree.bt_empty →
    (∀ (b : Bool), P (booltree.bt_leaf b)) →
    (∀ (b : Bool) (t1 t2 : booltree), P t1 → P t2 → P (booltree.bt_branch b t1 t2)) →
    ∀ (t : booltree), P t)

def booltree_property_type : Type := booltree → Prop

def base_case (P : booltree_property_type) : Prop :=
  P booltree.bt_empty

def leaf_case (P : booltree_property_type) : Prop :=
  ∀ (b : Bool), P (booltree.bt_leaf b)

def branch_case (P : booltree_property_type) : Prop :=
  ∀ (b : Bool) (t1 t2 : booltree), P t1 → P t2 → P (booltree.bt_branch b t1 t2)

def  booltree_ind_type :=
  ∀ (P : booltree_property_type),
    base_case P →
    leaf_case P →
    branch_case P →
    ∀ (b : booltree), P b

theorem booltree_ind_type_correct : booltree_ind_type := by
  exact @booltree.rec


inductive Toy : Type where
  | con1 (b : Bool)
  | con2 (n : Nat) (t : Toy)

def Toy_ind : Prop :=
  ∀ {P : Toy → Prop},
    (∀ b : Bool, P (Toy.con1 b)) →
    (∀ (n : Nat) (t : Toy), P t → P (Toy.con2 n t)) →
    ∀ t : Toy, P t

theorem Toy_correct : ∃ (f : Bool → Toy) (g : Nat → Toy → Toy),
  ∀ P : Toy → Prop,
    (∀ b : Bool, P (f b)) →
    (∀ (n : Nat) (t : Toy), P t → P (g n t)) →
    ∀ t : Toy, P t := by
  exists Toy.con1
  exists Toy.con2
  exact @Toy.rec


inductive tree (X : Type) : Type where
  | leaf (x : X)
  | node (t1 t2 : tree X)

#check (tree.rec :
  ∀ {X : Type} {P : tree X → Prop},
  (∀ (x : X), P (tree.leaf x)) →
  (∀ (t1 t2 : tree X), P t1 → P t2 → P (tree.node t1 t2)) →
  ∀ (t : tree X), P t)


/-
mytype_ind :
  ∀ (X : Type) (P : mytype X → Prop),
    (∀ x : X, P (mytype.constr1 X x)) →
    (∀ n : Nat, P (mytype.constr2 X n)) →
    (∀ m : mytype X, P m →
       ∀ n : Nat, P (mytype.constr3 X m n)) →
    ∀ m : mytype X, P m
-/
inductive mytype (X : Type) : Type where
  | constr1 (x : X)
  | constr2 (n : Nat)
  | constr3 (m : mytype X) (n : Nat)

/-
foo_ind :
  ∀ (X Y : Type) (P : foo X Y → Prop),
    (∀ x : X, P (foo.bar X Y x)) →
    (∀ y : Y, P (foo.baz X Y y)) →
    (∀ f1 : Nat → foo X Y,
      (∀ n : Nat, P (f1 n)) → P (foo.quux X Y f1)) →
    ∀ f2 : foo X Y, P f2
-/
inductive foo (X Y : Type) : Type where
  | bar (x : X)
  | baz (y : Y)
  | quux (f : Nat → foo X Y)


inductive foo' (X : Type) : Type where
  | C1 (l : List X) (f : foo' X)
  | C2

#check (foo'.rec :
  ∀ {X : Type} {P : foo' X → Prop},
  (∀ (l : List X) (f : foo' X), P f → P (foo'.C1 l f)) →
  (P foo'.C2) →
  ∀ f : foo' X, P f)
