import Colean.MutualCmd

/-! # Test: result indices that are not patterns

A constructor's result index may be any term, `P (n * 2)` or `Pa (!b)`, as with `inductive`. The
model eliminates its positions in general position, so nothing has to invert `*` or `!`. As with
`inductive`, `cases` on a value at such an index (`p : P (n * 2)`) still fails: the uses below
are at variable indices. -/

namespace ResultIndexTest

noncomputable section

/-! ### `n * 2` -/

codata P : Nat → Type
  | mk (n : Nat) (t : P n) : P (n * 2)

#check @P.mk
#check @P.B.mk_t

/-- Only `P 0` is inhabited: its element unfolds to itself. -/
def P.zero : P 0 :=
  P.corec (S := fun i => PLift (i = 0)) (fun | _, ⟨rfl⟩ => .mk 0 ⟨rfl⟩) ⟨rfl⟩

theorem P.dtor_zero : P.zero.dtor = .mk 0 P.zero := by
  simp [P.zero, P.dtor_corec]

/-- The constructor's argument, by case analysis at a variable index. -/
def P.arg {i : Nat} (p : P i) : Nat := P.casesOn (motive := fun _ _ => Nat) p fun n _ => n

@[simp] theorem P.arg_mk (n : Nat) (t : P n) : (P.mk n t).arg = n := by
  simp [P.arg]

example {i : Nat} (p : P i) : p.arg * 2 = i := by
  cases p with
  | mk n t => simp

/-! ### Several recursive arguments, a constructor without, and disjoint constructors -/

data D : Nat → Type
  | leaf (n : Nat) : D (n * 2)
  | mk (n : Nat) (l : D n) (r : D (n + 1)) : D (n * 3)
  | two (l : D 1) (r : D 2) : D 5
  | three (l : D 1) : D 5

#check @D.two_inj
#check @D.two_ne_three

/-- The number of leaves, by the fold. -/
def D.leaves {i : Nat} (d : D i) : Nat :=
  D.fold (S := fun _ => Nat) (fun _ y => match y with
    | .leaf _ => 1
    | .mk _ l r => l + r
    | .two l r => l + r
    | .three l => l) d

@[simp] theorem D.leaves_leaf (n : Nat) : (D.leaf n).leaves = 1 := by
  simp [D.leaves]

@[simp] theorem D.leaves_mk (n : Nat) (l : D n) (r : D (n + 1)) :
    (D.mk n l r).leaves = l.leaves + r.leaves := by
  simp [D.leaves]

/-- Every tree has a leaf, by induction. -/
theorem D.leaves_pos {i : Nat} (d : D i) : 0 < d.leaves := by
  induction d with
  | leaf n => simp
  | mk n l r ihl ihr => simp; omega
  | two l r ihl ihr => simp [D.leaves] at *; omega
  | three l ih => simpa [D.leaves] using ih

/-- The depth, by the recursor. -/
def D.depth {i : Nat} (d : D i) : Nat :=
  D.rec (motive := fun _ _ => Nat) (fun _ => 0) (fun _ _ _ a b => max a b + 1)
    (fun _ _ a b => max a b + 1) (fun _ a => a + 1) d

example (n : Nat) (l : D n) (r : D (n + 1)) :
    (D.mk n l r).depth = max l.depth r.depth + 1 := by
  rw [D.depth, D.rec_mk]
  rfl

example (l r : D 1) (h : D.three l = D.three r) : l = r := (D.three_inj l r).1 h

/-! ### Several indices -/

codata Q : Nat → Bool → Type
  | stop : Q 0 true
  | mk (n : Nat) (b : Bool) (t : Q n (!b)) : Q (n * 2) (!b)

-- An index of dependent type.
codata V : (n : Nat) → Fin (n + 1) → Type
  | mk (n : Nat) (t : V n 0) : V (n * 2) 0

-- An index fixed by every constructor, promoted to a parameter, before one that is not a
-- pattern.
codata T2 : Nat → Nat → Type
  | mk (m n : Nat) (t : T2 m n) : T2 m (n * 2)

example (q : Q 0 true) : Q 0 true := .mk 0 false q

/-! ### Nested arguments -/

/-- A nested layer at a fixed index of the family is a plain one. -/
theorem map_ofOcc_list {X Y : Nat → Type} (f : ∀ j, X j → Y j) (i : Nat) (l : List (X i)) :
    (Codata.IOcc.ofOcc (Codata.Occ.ofIso List) i).map (Codata.IOcc.ofOcc (Codata.Occ.ofIso List) i)
      f l = l.map (f i) :=
  Codata.Occ.map_list (f i) l

theorem map_ofOcc_option {X Y : Nat → Type} (f : ∀ j, X j → Y j) (i : Nat) (o : Option (X i)) :
    (Codata.IOcc.ofOcc (Codata.Occ.ofIso Option) i).map
      (Codata.IOcc.ofOcc (Codata.Occ.ofIso Option) i) f o = o.map (f i) :=
  Codata.Occ.map_option (f i) o

codata R : Nat → Type
  | mk (n : Nat) (ts : List (R n)) : R (n * 2)

/-- The tree at `0` whose children are itself, `k` times. -/
def R.fan (k : Nat) : R 0 :=
  R.corec (S := fun i => PLift (i = 0))
    (fun | _, ⟨rfl⟩ => .mk 0 (List.replicate k ⟨rfl⟩)) ⟨rfl⟩

theorem R.dtor_fan (k : Nat) : (R.fan k).dtor = .mk 0 (List.replicate k (R.fan k)) := by
  simp [R.fan, R.dtor_corec]

data DR : Nat → Type
  | mk (n : Nat) (ts : List (DR n)) (o : Option (DR (n + 1))) : DR (n * 2)

/-- The number of nodes, by the fold through both nested arguments. -/
def DR.size {i : Nat} (d : DR i) : Nat :=
  DR.fold (S := fun _ => Nat) (fun _ y => match y with
    | .mk _ ts o => ts.sum + (o.getD 0) + 1) d

@[simp] theorem DR.size_mk (n : Nat) (ts : List (DR n)) (o : Option (DR (n + 1))) :
    (DR.mk n ts o).size = (ts.map DR.size).sum + ((o.map DR.size).getD 0) + 1 := by
  rw [DR.size, DR.fold_mk, map_ofOcc_list, map_ofOcc_option]
  rfl

/-! ### Recursive arguments under a function -/

codata Fn : Nat → Type
  | mk (n : Nat) (f : (k : Nat) → Fn (k * n)) : Fn (n * 2)

data DFn : Nat → Type
  | leaf : DFn 0
  | mk (n : Nat) (f : Fin n → DFn n) : DFn (n * 2)

def DFn.width {i : Nat} (d : DFn i) : Nat :=
  DFn.rec (motive := fun _ _ => Nat) 1 (fun _ _ ih => (List.ofFn ih).sum) d

example (n : Nat) (f : Fin n → DFn n) :
    (DFn.mk n f).width = (List.ofFn fun k => (f k).width).sum := by
  rw [DFn.width, DFn.rec_mk]
  rfl

/-! ### Indices depending on a parameter -/

codata W (k : Nat) : Nat → Type
  | mk (n : Nat) (t : W k n) : W k (n + k)

/-- At `k = 0` every index is inhabited. -/
def W.loop (i : Nat) : W 0 i := W.corec (S := fun _ => Unit) (fun i _ => .mk i ()) ()

theorem W.dtor_loop (i : Nat) : (W.loop i).dtor = .mk i (W.loop i) := by
  simp [W.loop, W.dtor_corec]

data DW (k : Nat) : Nat → Type
  | nil : DW k k
  | mk (n : Nat) (t : DW k n) : DW k (n + k)

def DW.steps {k i : Nat} (d : DW k i) : Nat :=
  DW.fold (S := fun _ => Nat) (fun _ y => match y with
    | .nil => 0
    | .mk _ s => s + 1) d

@[simp] theorem DW.steps_mk {k : Nat} (n : Nat) (t : DW k n) :
    (DW.mk n t).steps = t.steps + 1 := by
  simp [DW.steps]

/-- The index is the parameter plus a multiple of it. -/
theorem DW.index {k i : Nat} (d : DW k i) : i = k + d.steps * k := by
  induction d with
  | nil => simp [DW.steps]
  | mk n t ih => simp [ih, Nat.succ_mul]; omega

/-! ### `!b` -/

data Pa : Bool → Type
  | nil : Pa true
  | mk {b : Bool} (q : Pa b) : Pa (!b)

def Pa.len {b : Bool} (p : Pa b) : Nat :=
  Pa.fold (S := fun _ => Nat) (fun _ y => match y with
    | .nil => 0
    | .mk k => k + 1) p

@[simp] theorem Pa.len_nil : Pa.nil.len = 0 := by
  simp [Pa.len]

@[simp] theorem Pa.len_mk {b : Bool} (q : Pa b) : (Pa.mk q).len = q.len + 1 := by
  simp [Pa.len]

/-- The index is the parity of the length. -/
theorem Pa.index {b : Bool} (p : Pa b) : p.len % 2 = if b then 0 else 1 := by
  induction p with
  | nil => simp
  | @mk b q ih => cases b <;> simp_all <;> omega

codata CPa : Bool → Type
  | nil : CPa true
  | mk {b : Bool} (q : CPa b) : CPa (!b)

/-- The infinite alternation. -/
def CPa.alt (b : Bool) : CPa b :=
  CPa.corec (S := fun _ => Unit) (fun b _ => match b with
    | true => .mk (b := false) ()
    | false => .mk (b := true) ()) ()

theorem CPa.dtor_alt_false : (CPa.alt false).dtor = .mk (CPa.alt true) := by
  simp [CPa.alt, CPa.dtor_corec]

/-! ### Fields of every kind together

Plain, nested and under a function, at two indices; a proof and a dependent field in the data. -/

codata Big : Nat → Bool → Type
  | mk (n : Nat) (b : Bool) (ts : List (Big n b)) (f : Nat → Big (n + 1) (!b))
      (t : Big n (!b)) : Big (n * 2) (b && true)
  | stop (n : Nat) : Big (n * 3) false

codata Pos : Nat → Type
  | mk (n : Nat) (h : 0 < n) (k : Fin n) (t : Pos k.val) : Pos (n * 2)

data DPos : Nat → Type
  | nil : DPos 0
  | mk (n : Nat) (k : Fin n) (t : DPos k.val) (u : DPos n) : DPos (n * 2)

/-! ### A mutual block: its index is `Blk.Ix`, a constructor per type -/

mutual
data Ma : Bool → Type
  | nil : Ma true
  | mk {b : Bool} (q : Ma b) : Ma (!b)
  | of {n : Nat} (q : Mb n) : Ma (n == 0)
data Mb : Nat → Type
  | mk (n : Nat) {b : Bool} (p : Ma b) : Mb (n * 2)
end

#check @Ma.rec
#check @Mb.rec

/-- The depth over the block, by the per-type recursor. -/
def Ma.depth {b : Bool} (a : Ma b) : Nat :=
  Ma.rec (motive_2 := fun _ _ => Nat) 0 (fun _ k => k + 1) (fun _ k => k + 1)
    (fun _ _ _ k => k + 1) a

example {b : Bool} (q : Ma b) : (Ma.mk q).depth = q.depth + 1 := by
  rw [Ma.depth, Ma.rec_mk]
  rfl

mutual
codata Ca : Bool → Type
  | nil : Ca true
  | mk {b : Bool} (q : Cb b) : Ca (!b)
codata Cb : Bool → Type
  | mk {b : Bool} (p : Ca b) : Cb (!b)
end

/-- Ends as soon as it can: a step per type, matching on its index. -/
def caStep : ∀ b, Unit → Ca.F (fun _ => Unit) (fun _ => Unit) b
  | true, _ => .nil
  | false, _ => .Ca_mk (b := true) ()

def cbStep : ∀ b, Unit → Cb.F (fun _ => Unit) (fun _ => Unit) b
  | true, _ => .Cb_mk (b := false) ()
  | false, _ => .Cb_mk (b := true) ()

def Ca.short (b : Bool) : Ca b := Ca.corec caStep cbStep ()
def Cb.short (b : Bool) : Cb b := Cb.corec caStep cbStep ()

theorem Ca.dtor_short_false : (Ca.short false).dtor = .Ca_mk (b := true) (Cb.short true) := by
  simp [Ca.short, Cb.short, caStep]

end

end ResultIndexTest
