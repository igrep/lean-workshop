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

theorem t_update_shadow : ∀ (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m) := by
  intro A m x v1 v2
  funext y
  unfold t_update
  split
  · rfl
  · rfl


theorem t_update_same : ∀ (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m := by
  intro A m x
  unfold t_update
  funext y
  split
  · subst x
    rfl
  · rfl

theorem t_update_permute
  : ∀ (A : Type) (m : total_map A) v1 v2 x1 x2,
  x2 ≠ x1 →
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m) := by
  intro A m v1 v2 x1 x2 h_neq
  funext y
  by_cases hx1 : x1 = y
  · subst hx1
    simp [t_update]
    intro h'
    subst h'
    nomatch h_neq
  · by_cases hx2 : x2 = y
    · subst hx2
      simp [t_update]
      intro h'
      subst h'
      nomatch h_neq
    · simp [t_update, hx1, hx2]
      done

def partial_map (A : Type) := total_map (Option A)

def empty {A : Type} : partial_map A :=
  t_empty .none

def update
  {A : Type}
  (m : partial_map A)
  (x : String) (v : A) :=
  (x !-> .some v ; m)

notation x "⊢>" v => update empty x v

notation x "⊢>" v ";" m => update m x v

def examplepmap :=
  "Church" ⊢> true ; "Turing" ⊢> false

#eval examplepmap "Church"
#eval examplepmap "Turing"
#eval examplepmap "Me"

theorem apply_empty : ∀ (A : Type) (x : String),
  @empty A x = .none := by
  intro A x
  unfold empty
  rw [t_apply_empty]

theorem update_eq : ∀ (A : Type) (m : partial_map A) x v,
  (x ⊢> v ; m) x = .some v := by
  intro A m x v
  unfold update
  rw [t_update_eq]

theorem update_neq : ∀ (A : Type) (m : partial_map A) x1 x2 v,
  x2 ≠ x1 →
  (x2 ⊢> v ; m) x1 = m x1 := by
  intro A m x1 x2 v h_neq
  unfold update
  rw [t_update_neq]
  · exact h_neq

theorem update_shadow : ∀ (A : Type) (m : partial_map A) x v1 v2,
  (x ⊢> v2 ; x ⊢> v1 ; m) = (x ⊢> v2 ; m) := by
  intro A m x v1 v2
  unfold update
  rw [t_update_shadow]

theorem update_same : ∀ (A : Type) (m : partial_map A) x v,
  m x = .some v →
  (x ⊢> v ; m) = m := by
  intro A m x v h
  unfold update
  rw [← h]
  apply t_update_same

theorem update_permute : ∀
  (A : Type)
  (m : partial_map A)
  x1 x2 v1 v2,
  x2 ≠ x1 →
  (x1 ⊢> v1 ; x2 ⊢> v2 ; m)
  =
  (x2 ⊢> v2 ; x1 ⊢> v1 ; m) := by
  intro A m x1 x2 v1 v2 h_neq
  unfold update
  apply t_update_permute
  exact h_neq

def includedin {A : Type} (m m' : partial_map A) :=
  ∀ x v, m x = .some v → m' x = .some v

theorem includedin_update : ∀
  (A : Type)
  (m m' : partial_map A)
  (x : String)
  (vx : A),
  includedin m m' →
  includedin (x ⊢> vx ; m) (x ⊢> vx ; m') := by
  intro A m m' x vx h_incl
  intro y vy
  by_cases hxy : x = y
  · subst hxy
    rw [update_eq]
    intro h
    rw [← h]
    simp [update_eq]
  · rw [update_neq]
    · rw [update_neq]
      · apply h_incl
      · apply hxy
    · apply hxy
