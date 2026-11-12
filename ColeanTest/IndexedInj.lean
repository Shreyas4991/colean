import Colean.MutualCmd

/-! # Test: injectivity and disjointness where the result index mentions the arguments

As Lean's `inductive` does for `T.c.inj`, `T.c_inj` shares between the two sides the arguments
that occur in the result index, or in the type of an argument occurring there, and is stated on
the others. `T.c_ne_d` is stated where the result indices of the two constructors unify: the
arguments of one are those of the other where the unifier needs it. There is none when the
indices cannot meet (`Z 0` and `Z (n + 1)`), nor when unification does not find where they do
(`P 0` and `P (n * 2)`). -/

namespace IndexedInjTest

noncomputable section

/-! ### `data` and `codata`: an index of two arguments -/

data Z : Nat → Type
  | leaf : Z 0
  | join (n m : Nat) (l : Z n) (r : Z m) : Z (max n m + 1)
  | node {n : Nat} (l r : Z n) : Z (n + 1)

/-- info: @Z.node_inj : ∀ {n : ℕ} (l r l' r' : Z n), l.node r = l'.node r' ↔ l = l' ∧ r = r' -/
#guard_msgs in #check @Z.node_inj
/--
info: Z.join_inj : ∀ (n m : ℕ) (l : Z n) (r : Z m) (l' : Z n) (r' : Z m), Z.join n m l r = Z.join n m l' r' ↔ l = l' ∧ r = r'
-/
#guard_msgs in #check @Z.join_inj
/--
info: Z.node_ne_join : ∀ (n m : ℕ) (l : Z n) (r : Z m) (l' r' : Z (max n m)), l'.node r' ≠ Z.join n m l r
-/
#guard_msgs in #check @Z.node_ne_join
/--
info: Z.join_ne_node : ∀ (n m : ℕ) (l : Z n) (r : Z m) (l' r' : Z (max n m)), Z.join n m l r ≠ l'.node r'
-/
#guard_msgs in #check @Z.join_ne_node
/-- error: Unknown constant `IndexedInjTest.Z.leaf_ne_node` -/
#guard_msgs in #check @Z.leaf_ne_node

example {n : Nat} (l r l' r' : Z n) (h : Z.node l r = Z.node l' r') : l = l' := by
  simp only [Z.node_inj] at h
  exact h.1

example (n m : Nat) (l l' : Z n) (r r' : Z m) :
    Z.join n m l r = Z.join n m l' r' ↔ r = r' ∧ l = l' := by
  rw [Z.join_inj, and_comm]

example {n m : Nat} (l : Z n) (r : Z m) (l' r' : Z (max n m)) :
    Z.node l' r' ≠ Z.join n m l r := by
  simp

example {n m : Nat} (l : Z n) (r : Z m) (l' r' : Z (max n m))
    (h : Z.join n m l r = Z.node l' r') : False := by
  simp at h

codata CZ : Nat → Type
  | leaf : CZ 0
  | join (n m : Nat) (l : CZ n) (r : CZ m) : CZ (max n m + 1)
  | node {n : Nat} (l r : CZ n) : CZ (n + 1)

/-- info: @CZ.node_inj : ∀ {n : ℕ} (l r l' r' : CZ n), l.node r = l'.node r' ↔ l = l' ∧ r = r' -/
#guard_msgs in #check @CZ.node_inj
/--
info: CZ.join_inj : ∀ (n m : ℕ) (l : CZ n) (r : CZ m) (l' : CZ n) (r' : CZ m),
  CZ.join n m l r = CZ.join n m l' r' ↔ l = l' ∧ r = r'
-/
#guard_msgs in #check @CZ.join_inj
/--
info: CZ.node_ne_join : ∀ (n m : ℕ) (l : CZ n) (r : CZ m) (l' r' : CZ (max n m)), l'.node r' ≠ CZ.join n m l r
-/
#guard_msgs in #check @CZ.node_ne_join
/--
info: CZ.join_ne_node : ∀ (n m : ℕ) (l : CZ n) (r : CZ m) (l' r' : CZ (max n m)), CZ.join n m l r ≠ l'.node r'
-/
#guard_msgs in #check @CZ.join_ne_node

example {n : Nat} (l r l' r' : CZ n) (h : CZ.node l r = CZ.node l' r') : r = r' :=
  ((CZ.node_inj l r l' r').1 h).2

example (n m : Nat) (l l' : CZ n) (r r' : CZ m) (h : CZ.join n m l r = CZ.join n m l' r') :
    l = l' := by
  rw [CZ.join_inj] at h
  exact h.1

example {n m : Nat} (l : CZ n) (r : CZ m) (l' r' : CZ (max n m)) :
    CZ.join n m l r ≠ CZ.node l' r' := by
  simp

/-! ### `Vec` -/

data Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

/--
info: @Vec.cons_inj : ∀ {α : Type} {n : ℕ} (a : α) (v : Vec α n) (a' : α) (v' : Vec α n),
  Vec.cons a v = Vec.cons a' v' ↔ a = a' ∧ v = v'
-/
#guard_msgs in #check @Vec.cons_inj
/-- error: Unknown constant `IndexedInjTest.Vec.nil_ne_cons` -/
#guard_msgs in #check @Vec.nil_ne_cons

example {α : Type} {n : Nat} (a a' : α) (v v' : Vec α n) (h : Vec.cons a v = Vec.cons a' v') :
    v = v' := by
  rw [Vec.cons_inj] at h
  exact h.2

/-! ### Two indices

Nothing is left of `base` once its index is shared: no injectivity, as for `inductive`. -/

data M : Nat → Bool → Type
  | base (b : Bool) : M 0 b
  | step {n : Nat} {b : Bool} (t : M n b) : M (n + 1) b
  | flip {n : Nat} (t : M n true) (u : M n false) : M (n + 1) false

/-- error: Unknown constant `IndexedInjTest.M.base_inj` -/
#guard_msgs in #check @M.base_inj
/-- info: @M.step_inj : ∀ {n : ℕ} {b : Bool} (t t' : M n b), t.step = t'.step ↔ t = t' -/
#guard_msgs in #check @M.step_inj
/--
info: @M.flip_inj : ∀ {n : ℕ} (t : M n true) (u : M n false) (t' : M n true) (u' : M n false),
  t.flip u = t'.flip u' ↔ t = t' ∧ u = u'
-/
#guard_msgs in #check @M.flip_inj
/-- info: @M.step_ne_flip : ∀ {n : ℕ} (t : M n true) (u t' : M n false), t'.step ≠ t.flip u -/
#guard_msgs in #check @M.step_ne_flip
/-- info: @M.flip_ne_step : ∀ {n : ℕ} (t : M n true) (u t' : M n false), t.flip u ≠ t'.step -/
#guard_msgs in #check @M.flip_ne_step
/-- error: Unknown constant `IndexedInjTest.M.base_ne_step` -/
#guard_msgs in #check @M.base_ne_step

example {n : Nat} (t t' : M n true) (h : M.step t = M.step t') : t = t' := by
  simpa using h

example {n : Nat} (t : M n true) (u u' : M n false) : M.flip t u ≠ M.step u' := by
  simp

/-! ### A result index that is not a pattern -/

data P : Nat → Type
  | zero : P 0
  | dbl (n : Nat) (t : P n) : P (n * 2)
  | dbl' (n : Nat) (t u : P n) : P (n * 2)

/-- info: P.dbl_inj : ∀ (n : ℕ) (t t' : P n), P.dbl n t = P.dbl n t' ↔ t = t' -/
#guard_msgs in #check @P.dbl_inj
/--
info: P.dbl'_inj : ∀ (n : ℕ) (t u t' u' : P n), P.dbl' n t u = P.dbl' n t' u' ↔ t = t' ∧ u = u'
-/
#guard_msgs in #check @P.dbl'_inj
/-- info: P.dbl_ne_dbl' : ∀ (n : ℕ) (t t' u' : P n), P.dbl n t ≠ P.dbl' n t' u' -/
#guard_msgs in #check @P.dbl_ne_dbl'
/-- error: Unknown constant `IndexedInjTest.P.zero_ne_dbl` -/
#guard_msgs in #check @P.zero_ne_dbl

example (n : Nat) (t t' : P n) (h : P.dbl n t = P.dbl n t') : t = t' :=
  (P.dbl_inj n t t').1 h

example (n : Nat) (t u u' : P n) : P.dbl' n t u ≠ P.dbl n u' := by
  simp

/-! ### A block with indices -/

mutual
data Ev : Nat → Type
  | zero : Ev 0
  | succ {n : Nat} (o : Od n) : Ev (n + 1)
data Od : Nat → Type
  | succ {n : Nat} (e : Ev n) : Od (n + 1)
  | twice {n : Nat} (o : Od n) : Od (n + 2)
end

/-- info: @Ev.succ_inj : ∀ {n : ℕ} (o o' : Od n), Ev.succ o = Ev.succ o' ↔ o = o' -/
#guard_msgs in #check @Ev.succ_inj
/-- info: @Od.twice_inj : ∀ {n : ℕ} (o o' : Od n), o.twice = o'.twice ↔ o = o' -/
#guard_msgs in #check @Od.twice_inj
/-- info: @Od.succ_ne_twice : ∀ {n : ℕ} (o : Od n) (e' : Ev (n + 1)), Od.succ e' ≠ o.twice -/
#guard_msgs in #check @Od.succ_ne_twice

example {n : Nat} (e e' : Ev n) (h : Od.succ e = Od.succ e') : e = e' := by
  simpa using h

example {n : Nat} (o : Od n) (e : Ev (n + 1)) : Od.twice o ≠ Od.succ e := by
  simp

/-! ### An argument whose type mentions one that is not shared

The equations of `v` and `t` are heterogeneous, as in `injEq`. -/

data H : Nat → Type
  | mk (k : Nat) (v : Fin k) (t : H k) : H 0
  | nil : H 0

/--
info: H.mk_inj : ∀ (k : ℕ) (v : Fin k) (t : H k) (k' : ℕ) (v' : Fin k') (t' : H k'),
  H.mk k v t = H.mk k' v' t' ↔ k = k' ∧ v ≍ v' ∧ t ≍ t'
-/
#guard_msgs in #check @H.mk_inj
/-- info: H.mk_ne_nil : ∀ (k : ℕ) (v : Fin k) (t : H k), H.mk k v t ≠ H.nil -/
#guard_msgs in #check @H.mk_ne_nil

end

end IndexedInjTest
