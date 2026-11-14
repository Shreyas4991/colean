import Colean.MutualCmd

/-!
# What `inductive` gives, and what `data` and `codata` give

Lean's `inductive` (and `structure`) generate a fixed set of declarations, and a number of tactics
and commands work on any inductive type. This file goes through them one by one and shows, next
to each, what `data` gives, and `codata` where it makes sense: the generated name, or that it is
missing, with a short note (needed or not, how hard, what stands in the way). Part I to Part VI
follow the API of `inductive` and `structure`; Part VII is what a user of `codata` expects
beyond Lean; Part VIII ends with a table of the missing items by priority.

Two facts explain most of the gaps. A declared type is a subtype of an encoding (`#print DList`),
and its constructors are definitions (`#print DList.cons`): so whatever in Lean needs a kernel
inductive type, or constructors in the sense of the kernel, does not see them (`match`,
`rcases` patterns, `injection`, structural recursion). And the encoding is classical,
so everything is noncomputable: `#eval`, `decide`, `rfl` on the recursor and the derived
instances that compute are out of reach.

How the file is checked: everything compiles. What does not work is shown by `fail_if_success`
for a tactic, or by `#guard_msgs` with a part of the error message for a command, with a comment.
Declarations proposed for generation are written here by hand under their proposed names; once
they are generated, those declarations must go.

Status: items 1, 2 and 7 of the table at the end are implemented (`RelHelp.lean`, whose
proposals they are): the one-step lemmas of `F.Rel` (but for `T.Poly.rel_cᵢ_cⱼ`),
`T.dtor_injective`, `T.dtor_inj` and `T.dtor_eq_cᵢ_iff`, and `T.coinduct`, `T.F.Rel.mono`,
`T.F.rel_refl`, generated under these names; the hand-written `DList.dtor_eq_cons_iff` of
section 13 is gone.
-/

universe u v

namespace ApiGap

noncomputable section

open Codata

/-- The reference: Lean's own lists. -/
inductive LList (α : Type u)
  | nil
  | cons (head : α) (tail : LList α)

/-- The same declaration as `data`. -/
data DList (α : Type u)
  | nil
  | cons (head : α) (tail : DList α)

/-- And as `codata`: possibly infinite lists. -/
codata CoList (α : Type u)
  | nil
  | cons (head : α) (tail : CoList α)

-- What a declaration is: a subtype of an encoding, with constructors as definitions.
#print DList
#print DList.cons

/-! ## Part I: eliminators -/

/-! ### 1. `rec`

Lean: `LList.rec : motive nil → (∀ head tail, motive tail → motive (cons head tail)) → ∀ t,
motive t`, computing by `rfl` (iota reduction).

Colean: `DList.rec`, the same statement, an `induction_eliminator`; its computation rules are
the theorems `DList.rec_nil`, `DList.rec_cons` (`simp`), not `rfl`. `codata` has no recursor, and
should not: its eliminator is `casesOn`, its principle is `bisim`. -/

#check @LList.rec
#check @DList.rec
#check @DList.rec_cons

example (f : DList.F Nat Nat → Nat) : DList.fold f .nil = f .nil := by
  fail_if_success rfl
  simp

/-! ### 2. `recOn`

Lean: `LList.recOn : ∀ t, motive nil → … → motive t`, `rec` with the major premise first.

Colean: missing. Trivial to add (a definition by `rec`), and unused by tactics: low priority, for
completeness of the names only. -/

#check @LList.recOn
/-- error: Unknown constant -/
#guard_msgs (substring := true) in
#check @DList.recOn

/-! ### 3. `casesOn`

Lean: `LList.casesOn`. Colean: `DList.casesOn`, `CoList.casesOn`, the `cases_eliminator` of both
kinds, with the rules `casesOn_c` (`simp`). Present. -/

#check @LList.casesOn
#check @DList.casesOn
#check @CoList.casesOn
#check @CoList.casesOn_cons

/-! ### 4. `below`, `brecOn`: structural recursion

Lean: `LList.below`, `LList.brecOn`, used by the equation compiler for structural recursion.

Colean: missing, and structural recursion is not possible at all: the equation compiler needs a
kernel inductive type. Use `rec`, `fold`, or well-founded recursion (section 13). Blocked by
Lean ([lean4#2716](https://github.com/leanprover/lean4/issues/2716), custom recursors). -/

#check @LList.brecOn

/-! ### 5. `ctorElim`, `c.elim`

Lean (recent): `LList.ctorElim`, `LList.ctorElimType` and one eliminator per constructor,
`LList.cons.elim : ∀ t, t.ctorIdx = 1 → (∀ head tail, motive (cons head tail)) → motive t`.

Colean: missing. They are definable from `casesOn` and `ctorIdx` (section 9). Little used by
users; low priority. -/

#check @LList.cons.elim

/-! ### 6. Nested types: auxiliary motives against membership

Lean's recursor of a nested inductive has one motive per nested occurrence (`motive_2` for the
lists of trees). Colean's has one motive, with the induction hypothesis by membership: `∀ t,
PolyIso.Mem (fun X => List X) t cs → motive t`, which `simp` turns into `t ∈ cs`. Different, and
usually more convenient; recursion on the list itself is done inside the minor premise, by `List`'s
own recursor. Nothing to add. -/

inductive LRose
  | node (a : Nat) (cs : List LRose)

data DRose
  | node (a : Nat) (cs : List DRose)

#check @LRose.rec
#check @DRose.rec

/-! ### 7. Mutual blocks: a recursor per type

Lean: `Even.rec` with a motive per type of the block. Colean: `Even.rec` too, with a motive per
type (`MutualTour.lean`, sections 2 and 7). Present. Plain `induction` on a type of a block is
refused, as Lean refuses it for a mutual inductive (being added at the time of writing). -/

namespace Mutual

mutual
inductive LEven
  | zero
  | succ (o : LOdd)
inductive LOdd
  | succ (e : LEven)
end

mutual
data Even
  | zero
  | succ (o : Odd)
data Odd
  | succ (e : Even)
end

#check @LEven.rec
#check @Even.rec

end Mutual

/-! ## Part II: constructors -/

/-! ### 8. Injectivity and disjointness: `injEq`, `inj`, `noConfusion`

Lean: `LList.cons.inj : cons a l = cons b m → a = b ∧ l = m`, `LList.cons.injEq` (`simp`, an
equation of propositions), and `LList.noConfusion` with `LList.noConfusionType`, through which
`injection`, `cases` on an equation and `simp` (`reduceCtorEq`) see that constructors are
injective and disjoint.

Colean: `DList.cons_inj` (an iff, `simp`, `HEq` for an argument whose type depends on an earlier
one, as `injEq`), and `DList.cons_ne_nil`, `DList.nil_ne_cons` (`simp`). `simp` uses them as
Lean's. Missing: the names `DList.cons.inj` and `DList.cons.injEq`, trivial aliases (users and
Mathlib habits look for them), and `noConfusion`, which could be defined through `T.F.noConfusion`
on `dtor` but would not make the tactics of section 11 work: they look for kernel constructors. -/

#check @LList.cons.inj
#check @LList.cons.injEq
#check @LList.noConfusion
#check @DList.cons_inj
#check @DList.cons_ne_nil
#check @CoList.cons_inj

data Dep
  | mk (n : Nat) (v : Fin n) (rest : Dep)
  | stop

-- A dependent argument: `HEq`, as Lean's `injEq`.
#check @Dep.mk_inj

example (a b : Nat) (l m : DList Nat) (h : DList.cons a l = DList.cons b m) : a = b := by
  simp at h
  exact h.1

example (a : Nat) (l : DList Nat) : DList.cons a l ≠ DList.nil := by
  simp

/-! ### 9. `ctorIdx`

Lean: `LList.ctorIdx : LList α → Nat`. Colean: missing; the functor has it (`DList.F.ctorIdx`).
Proposed: `T.ctorIdx t := t.dtor.ctorIdx`, with `T.ctorIdx_cᵢ` (`simp`). Trivial; low priority. -/

#check @LList.ctorIdx
#check @DList.F.ctorIdx

def DList.ctorIdx {α : Type u} (t : DList α) : Nat := t.dtor.ctorIdx

@[simp] theorem DList.ctorIdx_cons {α : Type u} (a : α) (t : DList α) :
    (DList.cons a t).ctorIdx = 1 := by
  simp only [DList.ctorIdx, DList.dtor_cons]
  rfl

/-! ### 10. Writing constructors

Present: dot notation with an expected type (`.cons a .nil`), named arguments
(`DList.cons (head := 1) (tail := .nil)`), generalized field notation (`t.dtor`, `t.casesOn`).
Missing for a type with one constructor: the anonymous constructor `⟨a, t⟩` and the structure
instance `{ head := a, tail := t }`, which see the subtype of the encoding instead (Part VI). -/

example : DList Nat := .cons 1 .nil
example : DList Nat := DList.cons (head := 1) (tail := .nil)

/-! ## Part III: tactics -/

/-! ### 11. Tactics that work and tactics that do not

Working: `cases` and `induction` (through the eliminators of the type), also at an index that is
not a variable (impossible cases are dropped), `simp` with the constructor lemmas, `subst`,
`generalize`, and everything on the functor (`match t.dtor with`, `cases t.dtor`).

Not working, all because the type is not a kernel inductive: `rcases`/`obtain` patterns and
`match` (both see the encoding), `injection`, `cases` on an equation of constructors,
`contradiction` and `nomatch` on such an equation. `simp at h` replaces the last four. Blocked by
Lean (custom recursors, lean4#2716); `rcases` and `match` could at least fail with a clean message
if the types were irreducible for them, which is worth trying. -/

example (l : DList Nat) : l = .nil ∨ ∃ a t, l = .cons a t := by
  cases l with
  | nil => simp
  | cons a t => simp

example (l : DList Nat) : DList.fold (fun _ => 0) l = 0 := by
  induction l with
  | nil => simp
  | cons _ _ _ => simp

data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)

-- At an index that is not a variable, the impossible case `nil` is dropped, as with `inductive`.
example {α : Type u} {n : Nat} (v : Vec α (n + 1)) : ∃ a w, v = .cons a w := by
  cases v with
  | cons a w => exact ⟨a, w, rfl⟩

-- `rcases` patterns see the subtype of the encoding: the alternatives `_ | ⟨…⟩` are tried on its
-- value, a function, and fail with a message about the encoding.
example (l : DList Nat) : True := by
  fail_if_success rcases l with _ | ⟨_, _⟩
  cases l <;> trivial

example (s : CoList Nat) : True := by
  obtain ⟨raw, wf⟩ := s
  -- `raw : Raw (CoList.sig ℕ).Idx (CoList.sig ℕ).Lbl` and `wf : IsWf () raw`: the encoding.
  trivial

-- `match` on a value: the constructor is unfolded down to the encoding, and the pattern is
-- refused with the encoding in the message. A match on `dtor` is the way.
/-- error: Invalid pattern(s) -/
#guard_msgs (substring := true) in
def DList.isNil₀ {α : Type u} (l : DList α) : Bool :=
  match l with
  | .nil => true
  | .cons _ t => false

def DList.isNil {α : Type u} (l : DList α) : Bool :=
  match l.dtor with
  | .nil => true
  | .cons _ _ => false

-- `injection` succeeds, and gives an equation of encodings.
example (a b : Nat) (l m : DList Nat) (h : DList.cons a l = DList.cons b m) : a = b := by
  have h' := h
  injection h' with h''
  -- `h'' : Signature.encode () (… (DList.toC (DList.F.cons a l))) = Signature.encode () (…)`.
  exact ((DList.cons_inj _ _ _ _).mp h).1

-- `cases` and `contradiction` on an equation of constructors fail; `simp` succeeds.
example (a : Nat) (l : DList Nat) (h : DList.cons a l = DList.nil) : False := by
  fail_if_success cases h
  fail_if_success contradiction
  simp at h

/-- error: Missing cases -/
#guard_msgs (substring := true) in
example (a : Nat) (l : DList Nat) (h : DList.cons a l = DList.nil) : False := nomatch h

/-! ### 12. Inductive and coinductive predicates on declared types

Lean's `inductive` and `coinductive` predicates over values of a declared type work, and so does
`cases` on such a hypothesis at a variable. At a constructor of the declared type, `cases` has to
unify two constructor applications, which needs `noConfusion` of a kernel inductive: it fails.
The way around is `generalize` and an equation, then `simp`. -/

inductive CoList.Finite {α : Type u} : CoList α → Prop
  | nil : CoList.Finite .nil
  | cons (a : α) (s : CoList α) : CoList.Finite s → CoList.Finite (.cons a s)

coinductive CoList.Infinite {α : Type u} : CoList α → Prop
  | cons (a : α) (s : CoList α) : CoList.Infinite s → CoList.Infinite (.cons a s)

#check @CoList.Infinite.coinduct

example (a : Nat) (s : CoList Nat) (h : (CoList.cons a s).Finite) : s.Finite := by
  fail_if_success cases h
  generalize e : CoList.cons a s = t at h
  cases h with
  | nil => simp at e
  | cons b s' h' =>
    obtain ⟨rfl, rfl⟩ := (CoList.cons_inj _ _ _ _).mp e
    exact h'

/-! ## Part IV: recursion -/

/-! ### 13. Well-founded recursion: `sizeOf`, `SizeOf`, `sizeOf_spec`, `termination_by`

Lean: an instance `SizeOf LList` (`LList._sizeOf_inst`) with `LList.cons.sizeOf_spec :
sizeOf (cons a t) = 1 + sizeOf a + sizeOf t` (`simp`), so that `termination_by` and the default
`decreasing_tactic` work.

Colean: missing. Every type then has Lean's default instance, `sizeOf t = 0`, and any
well-founded definition by `sizeOf` fails. Proposed for `data`: the instance by `fold` and the
rules `T.cᵢ.sizeOf_spec`, as Lean's; with the equation `T.dtor_eq_cᵢ_iff : t.dtor = F.cᵢ xs ↔ t =
cᵢ xs` (generated, `simp`), a recursion through `match h : t.dtor with` terminates by
`decreasing_by simp_all`.
Through a nested argument the rule needs `sizeOf` of the leaf at the mapped contents (`List`: a
lemma `sizeOf (l.map f) = sizeOf l` when `sizeOf ∘ f = sizeOf`). Medium effort; important for
`data`. An alternative is a `WellFoundedRelation` instance by the immediate-child relation, the
one `T.rec` is built on. -/

#check @LList.cons.sizeOf_spec

example (l : DList Nat) : sizeOf l = 0 := rfl

-- Without an instance, the recursive call cannot be shown to decrease.
/-- error: failed to prove termination -/
#guard_msgs (substring := true) in
def DList.len₀ {α : Type u} (l : DList α) : Nat :=
  match h : l.dtor with
  | .nil => 0
  | .cons _ t => t.len₀ + 1
termination_by l

-- The proposal, by hand: an instance by `fold` and its rule; the destructor equation
-- `DList.dtor_eq_cons_iff` is generated.
instance DList.instSizeOf {α : Type u} [SizeOf α] : SizeOf (DList α) :=
  ⟨DList.fold fun | .nil => 1 | .cons a n => 1 + sizeOf a + n⟩

@[simp] theorem DList.nil.sizeOf_spec {α : Type u} [SizeOf α] :
    sizeOf (DList.nil : DList α) = 1 := by
  show DList.fold _ _ = _
  simp

@[simp] theorem DList.cons.sizeOf_spec {α : Type u} [SizeOf α] (a : α) (t : DList α) :
    sizeOf (DList.cons a t) = 1 + sizeOf a + sizeOf t := by
  show DList.fold _ _ = _
  simp
  rfl

#check @DList.dtor_eq_cons_iff

def DList.len {α : Type u} (l : DList α) : Nat :=
  match h : l.dtor with
  | .nil => 0
  | .cons _ t => t.len + 1
termination_by l
decreasing_by simp_all

/-! ### 14. `partial`, `partial_fixpoint`, and what stands for `rfl`

Lean's `partial def` needs compiled code and an `Inhabited` or `Nonempty` result: with
noncomputable types it is refused. `partial_fixpoint` works for a `codata` type with
`with_ccpo` (`CCPOTour.lean`), and for `data` only into a type with an order (`Option`). The
equation lemmas of a function by `fold` are the user's: `simp [f]` and the generated `fold_cᵢ`. -/

/-- error: 'noncomputable partial' is not allowed -/
#guard_msgs (substring := true) in
noncomputable partial def loop (n : Nat) : DList Nat := loop n

/-! ## Part V: instances, `deriving`, computation -/

/-! ### 15. `Nonempty`, `Inhabited`

Lean derives neither by itself: `deriving Nonempty, Inhabited`. Colean rejects `deriving`, and
generates neither. Proposed: generate `Nonempty` (a `Prop`, no computation involved) and a
noncomputable `Inhabited` when a constructor can be built from inhabited data. For `data` the
constructor needs no recursive argument (or only through a leaf with an empty value, `[]`); for
`codata` any constructor does, the recursive arguments by `corec`: `Str α` is inhabited when `α`
is, unlike Lean's inductive streams. Low effort, medium importance (Mathlib-style `[Nonempty T]`
assumptions, `Classical.arbitrary`). -/

inductive LList₂ (α : Type u)
  | nil
  | cons (head : α) (tail : LList₂ α)
  deriving Nonempty

#check (inferInstance : Nonempty (LList₂ Nat))

/-- error: `deriving` is not supported by `data` -/
#guard_msgs in
data DList₂ (α : Type u)
  | nil
  | cons (head : α) (tail : DList₂ α)
  deriving Nonempty

/-- error: failed to synthesize -/
#guard_msgs (substring := true) in
#synth Nonempty (DList Nat)

-- The proposal, by hand.
instance DList.instNonempty {α : Type u} : Nonempty (DList α) := ⟨.nil⟩
instance DList.instInhabited {α : Type u} : Inhabited (DList α) := ⟨.nil⟩

/-! ### 16. `deriving DecidableEq`, `Repr`, `BEq`, `Hashable`, `Ord`; `#eval`, `decide`

All missing, and all need computation: blocked by the classical encoding. A noncomputable
`DecidableEq` by `Classical.decEq` would type-check but make `decide` no better. Out of scope
while everything is noncomputable (README, Limitations). -/

/-- error: Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance -/
#guard_msgs (substring := true) in
#eval (DList.nil : DList Nat)

example : (DList.nil : DList Nat) ≠ .cons 1 .nil := by
  fail_if_success decide
  simp

/-! ### 17. Sorts and universes

Lean's `inductive` may be a `Prop`, and a family may live in any universe large enough for its
constructors. Colean defines types only (`data P : Prop` is an error) and a family lives at least
in the universe of its indices (`contract.md`). Both come from the encoding; low importance. -/

/-- error: `P` is declared with sort `Prop` but defined with sort `Type` -/
#guard_msgs (substring := true) in
data P : Prop
  | intro

/-! ## Part VI: structures, and types with one constructor -/

/-! ### 18. Projections, `.1`, `⟨⟩`, `{ … }`, `with`, `ext`, eta

Lean's `structure Pt where x : Nat; y : Nat` gives the projections `Pt.x`, `Pt.y` (primitive,
so `p.1`, `p.2` too), the anonymous constructor and the structure instance notation, the update
`{ p with x := 0 }`, `Pt.mk.injEq`, with `@[ext]` the lemmas `Pt.ext` and `Pt.ext_iff`, and eta by
definition (`⟨p.x, p.y⟩ = p` is `rfl`).

Colean, for a `data` or `codata` with one constructor: none of these. The owner plans projections
for such types; Part VII sketches them for `codata`, and the same works for `data`. The notations
`⟨⟩`, `{ … }`, `.1` and `with` are Lean's, for kernel inductive types with one constructor, and
cannot be had for a definition; `⟨⟩` and `{ … }` today even see the subtype of the encoding. -/

@[ext] structure Pt where
  x : Nat
  y : Nat

#check @Pt.ext_iff
example (p : Pt) : (⟨p.x, p.y⟩ : Pt) = p := rfl

data DPt
  | mk (x : Nat) (y : Nat)

example : DPt := by
  fail_if_success exact ⟨1, 2⟩
  fail_if_success exact { x := 1, y := 2 }
  exact .mk 1 2

/-! ## Part VII: `codata` beyond Lean -/

/-! ### 19. What is there

The interface of a final coalgebra: `corec` with `dtor_corec` (`simp`) and `corec_eq`, uniqueness
`corec_unique`, coinduction `bisim` with the lifting `F.Rel`, Lambek's lemma (`ctor_dtor`,
`dtor_ctor`), the constructors with their lemmas, `casesOn`, and `partial_fixpoint` through
`with_ccpo`. And, from the proposals of `RelHelp.lean`: equality by the destructor
(`dtor_injective`, `dtor_inj`, `dtor_eq_cᵢ_iff`), one step of `F.Rel` by `simp`
(`F.rel_cᵢ_cⱼ`, and the relations of the occurrence structures, `Occ.rel_*`), and coinduction up
to equality (`coinduct`, with `F.Rel.mono` and `F.rel_refl`). -/

#check @CoList.corec
#check @CoList.dtor_corec
#check @CoList.corec_unique
#check @CoList.bisim
#check @CoList.dtor_inj
#check @CoList.F.rel_cons_cons
#check @CoList.coinduct

/-! ### 20. What is missing

* `T.Poly.rel_cᵢ_cⱼ`, the relation of a declared type as a leaf on its constructors
  (`RelHelp.lean`, section 11); the rest of `RelHelp.lean` is implemented (section 19).
* No `@[ext]` lemma for `codata`: `ext` applies extensionality lemmas again to the new goals, so a
  lemma whose premise is an equation of the same type unfolds a stream a hundred levels deep
  (its default depth). `T.ext_iff` without the attribute, and `ext1` where needed (section 21).
* Projections for a type with one constructor, below. -/

/-! ### 21. Projections for `codata` with one constructor: a sketch

For `codata Str | cons (head : α) (tail : Str α)`, the command would generate:

* the projections `Str.head`, `Str.tail`, a match on `dtor` (`casesOn` works as well);
* `Str.head_cons`, `Str.tail_cons` (`simp`), and `Str.dtor_eq : s.dtor = .cons s.head s.tail`;
* eta, `Str.cons_head_tail : .cons s.head s.tail = s` (`simp`), and `Str.ext_iff : s = s' ↔
  s.head = s'.head ∧ s.tail = s'.tail`, not `@[ext]`;
* coinduction by the projections, `Str.bisim'`: a relation whose related pairs have equal heads
  and related tails is equality. It is `bisim` with the generated `F.rel_cons_cons`;
* corecursion by the projections (copatterns), `Str.unfold hd tl` with `head_unfold`,
  `tail_unfold` (`simp`).

All definitions and lemmas are per type, from the existing interface, with no new theory. A
constructor in arrow form, without argument names, gets no projections; a projection named like a
generated declaration collides, as constructors already can (left alone by the owner's decision). -/

namespace Costructure

codata Str (α : Type u)
  | cons (head : α) (tail : Str α)

def Str.head {α : Type u} (s : Str α) : α := match s.dtor with | .cons a _ => a
def Str.tail {α : Type u} (s : Str α) : Str α := match s.dtor with | .cons _ t => t

@[simp] theorem Str.head_cons {α : Type u} (a : α) (s : Str α) : (Str.cons a s).head = a := by
  simp [Str.head]

@[simp] theorem Str.tail_cons {α : Type u} (a : α) (s : Str α) : (Str.cons a s).tail = s := by
  simp [Str.tail]

theorem Str.dtor_eq {α : Type u} (s : Str α) : s.dtor = .cons s.head s.tail := by
  cases s
  simp

@[simp] theorem Str.cons_head_tail {α : Type u} (s : Str α) : Str.cons s.head s.tail = s := by
  cases s
  simp

theorem Str.ext {α : Type u} {s s' : Str α} (h₁ : s.head = s'.head) (h₂ : s.tail = s'.tail) :
    s = s' := by
  rw [← Str.cons_head_tail s, ← Str.cons_head_tail s', h₁, h₂]

theorem Str.ext_iff {α : Type u} {s s' : Str α} : s = s' ↔ s.head = s'.head ∧ s.tail = s'.tail :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => Str.ext h.1 h.2⟩

theorem Str.bisim' {α : Type u} (R : Str α → Str α → Prop)
    (H : ∀ x y, R x y → x.head = y.head ∧ R x.tail y.tail) {x y : Str α} (h : R x y) : x = y := by
  refine Str.bisim R (fun x y hxy => ?_) h
  rw [Str.dtor_eq x, Str.dtor_eq y, (H x y hxy).1]
  exact .cons _ _ _ (H x y hxy).2

/-- Corecursion by the projections: the head and the next state. -/
def Str.unfold {α : Type u} {S : Type v} (hd : S → α) (tl : S → S) : S → Str α :=
  Str.corec fun s => .cons (hd s) (tl s)

@[simp] theorem Str.head_unfold {α : Type u} {S : Type v} (hd : S → α) (tl : S → S) (s : S) :
    (Str.unfold hd tl s).head = hd s := by
  simp [Str.unfold, Str.head, Str.dtor_corec]

@[simp] theorem Str.tail_unfold {α : Type u} {S : Type v} (hd : S → α) (tl : S → S) (s : S) :
    (Str.unfold hd tl s).tail = Str.unfold hd tl (tl s) := by
  simp [Str.unfold, Str.tail, Str.dtor_corec]

/-- The map, by the projections. -/
def Str.map {α β : Type u} (g : α → β) (s : Str α) : Str β :=
  Str.unfold (fun s => g s.head) Str.tail s

-- Coinduction by the projections, with `simp` on the projections: no `F.Rel` in sight.
example {α β γ : Type u} (f : α → β) (g : β → γ) (s : Str α) :
    (s.map f).map g = s.map (g ∘ f) := by
  refine Str.bisim' (fun x y => ∃ s, x = (s.map f).map g ∧ y = s.map (g ∘ f)) (fun x y => ?_)
    ⟨s, rfl, rfl⟩
  rintro ⟨s, rfl, rfl⟩
  simp only [Str.map, Str.head_unfold, Str.tail_unfold, Function.comp_apply, true_and]
  exact ⟨s.tail, rfl, rfl⟩

/-! With `@[ext]`, `ext` unfolds a stream as deep as it may, a hundred levels by default: one goal
per head, then the rest. Here at depth two. So `Str.ext` is not tagged; `ext1` with the attribute
takes one step, or `Str.ext_iff` is used directly. -/

section

attribute [local ext] Str.ext

example (s s' : Str Nat) (h₁ : s.head = s'.head) (h₂ : s.tail.head = s'.tail.head)
    (h₃ : s.tail.tail = s'.tail.tail) : s = s' := by
  ext : 2
  exacts [h₁, h₂, h₃]

end

end Costructure

/-! ## Part VIII: summary

### Overview

| Item | `inductive` / `structure` | `data` | `codata` | Note |
|---|---|---|---|---|
| recursor | `T.rec`, iota by `rfl` | `T.rec`, rules `T.rec_cᵢ` (`simp`) | none (`corec`, `bisim`) | rules are theorems |
| `recOn` | `T.recOn` | missing | missing | trivial |
| case analysis | `T.casesOn` | `T.casesOn`, `T.casesOn_cᵢ` | the same | present |
| structural recursion | `T.below`, `T.brecOn` | missing | n/a | blocked by Lean |
| per-constructor eliminators | `T.ctorElim`, `T.cᵢ.elim` | missing | missing | little used |
| nested recursor | auxiliary motives | one motive, membership hypotheses | n/a | by design |
| mutual recursors | a motive per type | `Tₘ.rec`, a motive per type | n/a | present |
| injectivity | `T.cᵢ.inj`, `T.cᵢ.injEq` | `T.cᵢ_inj` (iff, `simp`) | the same | Lean's names missing |
| disjointness | `noConfusion`, `reduceCtorEq` | `T.cᵢ_ne_cⱼ` (`simp`) | the same | present |
| `noConfusionType`, `noConfusion` | yes | missing | missing | would not help tactics |
| `ctorIdx` | `T.ctorIdx` | missing (`T.F.ctorIdx`) | missing | trivial |
| `SizeOf`, `T.cᵢ.sizeOf_spec` | yes | missing: `sizeOf = 0` | n/a | breaks `termination_by` |
| `cases`, `induction` | yes | yes, by the eliminators | `cases` | present |
| `rcases`/`obtain` patterns, `match` | yes | no, they see the encoding | no | Lean; `match t.dtor` |
| `injection`, `cases`/`nomatch`/`contradiction` on `cᵢ … = cⱼ …` | yes | no | no | Lean; `simp at h` |
| `cases` on a predicate at a constructor index | yes | no | no | Lean; `generalize`, `simp` |
| `decide`, `rfl` on eliminators, `#eval` | yes | no | no | classical encoding |
| `termination_by` | by `sizeOf` | fails | n/a | needs `SizeOf` |
| `partial def` | yes | refused (noncomputable) | refused | `partial_fixpoint` instead |
| `partial_fixpoint` | into an order | into an order | `with_ccpo` | present for `codata` |
| `deriving` | yes | refused | refused | |
| `Nonempty`, `Inhabited` | by `deriving` | missing | missing | easy |
| `DecidableEq`, `Repr`, `BEq`, `Hashable`, `Ord` | by `deriving` | missing | missing | computation |
| `Prop`-valued | yes | refused | refused | encoding |
| projections, `.1`, `.2` | `structure` | missing | missing | projections proposed (Part VII) |
| `⟨…⟩`, `{ … }`, `{ s with … }` | `structure` | no, they see the subtype | no | Lean |
| `ext`, `ext_iff` | `@[ext] structure` | missing | missing, not `@[ext]` | proposed (Part VII) |
| eta | by definition | `T.ctor_dtor` | the same, and `cons_head_tail` proposed | |
| dot notation, named arguments | yes | yes | yes | present |
| members of a nested argument | n/a | `PolyIso.Mem`, `simp` to `∈` | the same | present |
| predicates | `inductive`, `coinductive` | work over values | work over values | see `cases` above |
| `dtor` injective, `F.Rel` steps | n/a | `T.dtor_inj`, `T.dtor_eq_cᵢ_iff` | the same, `F.rel_cᵢ_cⱼ`, `coinduct` | present (`RelHelp.lean`) |

### Missing, by priority

| # | Missing | Importance | Effort | Blocker |
|---|---|---|---|---|
| 1 | One step of `F.Rel` by `simp`: `T.F.rel_cᵢ_cⱼ`, `Occ.rel_*` (done); `T.Poly.rel_cᵢ_cⱼ` (`RelHelp.lean`, not yet) | high | low | none |
| 2 | `T.dtor_injective`, `T.dtor_inj`, `T.dtor_eq_cᵢ_iff` (done) | high | low | none |
| 3 | Projections for a type with one constructor, with `cᵢ_head_tail` eta, `ext_iff`, coinduction and corecursion by the projections (Part VII) | high (planned) | low to medium | none; names may collide with generated ones, as constructors already can |
| 4 | `SizeOf` instance and `T.cᵢ.sizeOf_spec` for `data`, so that `termination_by` works | high for `data` | medium (nested arguments need a rule per leaf) | none |
| 5 | `Nonempty` and noncomputable `Inhabited` instances | medium | low | none |
| 6 | Messages that do not show the encoding (`match`, `rcases`, `⟨…⟩`, `injection`) | medium | medium: make the types opaque to elaboration, then check the generated proofs | the generated proofs may rely on unfolding |
| 7 | `T.coinduct` (up to equality), `T.F.Rel.mono`, `T.F.rel_refl` (done) | medium | low | none |
| 8 | Lean's names: `T.cᵢ.inj`, `T.cᵢ.injEq`, `T.recOn`, `T.ctorIdx` with `T.ctorIdx_cᵢ` | low to medium | trivial | none |
| 9 | `match`, `rcases` patterns, `injection`, `cases` on constructor equations and on predicates at constructor indices, structural recursion, `below`, `brecOn` | high | none possible here | Lean: kernel inductives only (lean4#2716); `simp at h`, `match t.dtor`, `rec`, `generalize` meanwhile |
| 10 | `#eval`, `decide`, `rfl` on eliminators, `deriving DecidableEq`/`Repr`/`BEq`/`Hashable`/`Ord`, `partial def` | medium | high | the classical encoding; out of scope for now |
| 11 | `T.ctorElim`, `T.cᵢ.elim`, `T.noConfusion` | low | low | none, but little use |
| 12 | `data … : Prop`; a family below the universe of its indices | low | high | the encoding |
-/

end

end ApiGap
