#synth LawfulBEq String
#print LawfulBEq

def total_map (α : Type) := String → α

def t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v)

def t_update
  {A : Type} (m : total_map A) (x : String) (v : A) :=
  fun x' => if x = x' then v else m x'

def examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true

notation "__" " !-> " v => t_empty v

example : total_map Bool := __ !-> false

notation x "!->" v ";" m => t_update m x v

def examplemap' :=
  "bar" !-> true;
  "foo" !-> true;
  __ !-> false

#eval examplemap' "aaaa"
#eval examplemap' "bar"
#eval examplemap' "foo"

theorem t_apply_empty : ∀ (A : Type) (x : String) (v : A),
  (__ !-> v) x = v := by
  intro A x v
  rfl

theorem t_update_eq : ∀ (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v := by
  intro A m x v
  simp [t_update]

theorem t_update_neq : ∀ (A : Type) (m : total_map A) x1 x2 v,
  x1 ≠ x2 →
  (x1 !-> v ; m) x2 = m x2 := by
  intro A m x1 x2 v h_neq
  simp [t_update, h_neq]

theorem t_update_same : ∀ (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m := by
  intro A m x
  unfold t_update
  funext y
  split
  · subst x
    rfl
  · rfl
