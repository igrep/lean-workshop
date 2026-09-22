import Test.IndProp

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


def P_m0r (n : Nat) : Prop :=
  n * 0 = 0

def P_m0r' : Nat → Prop :=
  fun n => n * 0 = 0

theorem mul_0_r'' : ∀ n : Nat,
  P_m0r n := by
  apply Nat.rec
  · rfl
  · intro n IHn
    unfold P_m0r at IHn
    unfold P_m0r
    apply IHn

theorem add_assoc' : ∀ n m p : Nat,
  n + (m + p) = (n + m) + p := by
  intro n m p
  induction p
  case zero =>
    rfl
  case succ p' IH =>
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [IH]
    rw [Nat.add_succ]

def add_assoc'_ex_P (n m p : Nat) : Prop :=
  n + (m + p) = (n + m) + p

theorem add_assoc'_ex : ∀ n m p : Nat,
  add_assoc'_ex_P n m p := by
  intro n m p
  apply Nat.rec
  · unfold add_assoc'_ex_P
    rfl
  · intro p' IH
    unfold add_assoc'_ex_P at IH
    unfold add_assoc'_ex_P
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [IH]
    rw [Nat.add_succ]


theorem add_comm' : ∀ n m : Nat,
  n + m = m + n := by
  intro n m
  induction n
  case zero =>
    rw [Nat.zero_add]
    rfl
  case succ n IH =>
    rw [Nat.succ_add]
    rw [IH]
    rw [Nat.add_succ]

def add_comm'_ex_P (n m : Nat) : Prop :=
  n + m = m + n

theorem add_comm'_ex : ∀ n m : Nat,
  add_comm'_ex_P n m := by
  intro n m
  apply Nat.rec
  · unfold add_comm'_ex_P
    rw [Nat.zero_add]
    rfl
  · intro m' IH
    unfold add_comm'_ex_P at IH
    unfold add_comm'_ex_P
    rw [Nat.add_succ]
    rw [IH]
    rw [Nat.succ_add]

#print ev
#check ev.rec
#check (ev.rec :
  ∀ {P : (a : Nat) → ev a → Prop},
  P 0 ev.zero →
  (∀ {n : Nat}, (h : ev n) → P n h → P n.succ.succ h.succ) →
  ∀ {n : Nat}, (t : ev n) → P n t)

theorem ev_ev' : ∀ n, ev n → ev' n := by
  apply ev.rec
  · apply ev'.ev'_0
  · intro n h IH
    apply ev'.ev'_sum
    · exact IH
    · exact ev'.ev'_2


inductive le1 : Nat → Nat → Prop where
  | le1_n : ∀ n, le1 n n
  | le1_S : ∀ n m, (le1 n m) → (le1 n m.succ)

inductive le2 (n : Nat) : Nat → Prop where
  | le2_n : le2 n n
  | le2_S m (H : le2 n m) : le2 n m.succ

set_option pp.proofs true
set_option pp.explicit true
/-
le1.rec :
  ∀ {n : Nat} {motive : (a : Nat) → le1 n a → Prop},
    motive n (le1.le1_n n) →
      (∀ (m : Nat) (a : le1 n m), motive m a → motive m.succ (le1.le1_S n m a)) →
        ∀ {a : Nat} (t : le1 n a), motive a t : Prop
-/
#check le1.rec
/-
le2.rec :
  ∀ {n : Nat} {motive : (a : Nat) → le2 n a → Prop},
    motive n (@le2.le2_n n) →
      (∀ (m : Nat) (H : le2 n m), motive m H → motive m.succ (@le2.le2_S n m H)) →
        ∀ {a : Nat} (t : le2 n a), motive a t : Prop
-/
#check le2.rec
