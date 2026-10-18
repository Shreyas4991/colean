import Colean.CodataCmd

/-! Interaction trees: implicit binders, and branching that depends on the constructor's data
(`k : X → ITree E R` with `X` a field of `Vis`). The corecursor is noncomputable here. -/

namespace CodataTest

codata ITree (E : Type → Type) (R : Type)
  | Ret (r : R)
  | Tau (t : ITree E R)
  | Vis {X : Type} (e : E X) (k : X → ITree E R)

#check @ITree.Vis
#check @ITree.corec
#check @ITree.B.Vis_k
#check @ITree.F.Rel.Vis
#check @ITree.bisim

noncomputable section

variable {E : Type → Type} {R S : Type}

/-- The silently diverging tree. -/
def ITree.spin : ITree E R := ITree.corec (fun _ => .Tau ()) ()

theorem ITree.spin_eq : (ITree.spin : ITree E R) = .Tau .spin := ITree.corec_eq _ _

/-- Trigger an event and return its answer. -/
def ITree.trigger {X : Type} (e : E X) : ITree E X := .Vis e .Ret

/-- One step of `bind`: in state `.inl t` we are still running `t`, in state `.inr u` we are
copying the continuation `u`. On a `Ret r` of `t` the first layer of `f r` is produced right
away, so no `Tau` is inserted. -/
def ITree.bindStep (f : R → ITree E S) :
    ITree E R ⊕ ITree E S → ITree.F E S (ITree E R ⊕ ITree E S)
  | .inl t =>
    match t.dtor with
    | .Ret r => (f r).dtor.map .inr
    | .Tau u => .Tau (.inl u)
    | .Vis e k => .Vis e fun a => .inl (k a)
  | .inr u => u.dtor.map .inr

/-- Monadic bind, by corecursion: run `t`, then run `f r` on its result. -/
def ITree.bind (t : ITree E R) (f : R → ITree E S) : ITree E S :=
  ITree.corec (ITree.bindStep f) (.inl t)

/-- Copying the continuation is the identity. -/
theorem ITree.corec_bindStep_inr (f : R → ITree E S) (u : ITree E S) :
    ITree.corec (ITree.bindStep f) (.inr u) = u := by
  refine ITree.bisim (fun x y => x = ITree.corec (ITree.bindStep f) (.inr y)) ?_ rfl
  rintro _ y rfl
  rw [ITree.dtor_corec, ITree.bindStep, ← ITree.F.map_comp]
  conv => rhs; rw [← ITree.F.map_id y.dtor]
  exact ITree.F.rel_map _ _ _ _ fun _ => rfl

theorem ITree.dtor_bind (t : ITree E R) (f : R → ITree E S) :
    (ITree.bind t f).dtor = match t.dtor with
      | .Ret r => (f r).dtor
      | .Tau u => .Tau (ITree.bind u f)
      | .Vis e k => .Vis e fun a => ITree.bind (k a) f := by
  rw [ITree.bind, ITree.dtor_corec, ITree.bindStep]
  split
  · rw [← ITree.F.map_comp]
    conv => rhs; rw [← ITree.F.map_id (f _).dtor]
    congr 1
    funext u
    exact ITree.corec_bindStep_inr f u
  · rfl
  · rfl

@[simp] theorem ITree.bind_Ret (r : R) (f : R → ITree E S) : ITree.bind (.Ret r) f = f r := by
  rw [← ITree.ctor_dtor (ITree.bind _ f), ITree.dtor_bind, ITree.dtor_Ret, ITree.ctor_dtor]

theorem ITree.bind_Tau (t : ITree E R) (f : R → ITree E S) :
    (ITree.bind (.Tau t) f).dtor = .Tau (ITree.bind t f) := by
  rw [ITree.dtor_bind, ITree.dtor_Tau]

theorem ITree.bind_Vis {X : Type} (e : E X) (k : X → ITree E R) (f : R → ITree E S) :
    (ITree.bind (.Vis e k) f).dtor = .Vis e fun a => ITree.bind (k a) f := by
  rw [ITree.dtor_bind, ITree.dtor_Vis]

@[simp] theorem ITree.bind_Tau_eq (t : ITree E R) (f : R → ITree E S) :
    ITree.bind (.Tau t) f = .Tau (ITree.bind t f) := by
  rw [← ITree.ctor_dtor (ITree.bind _ f), ITree.bind_Tau, ← ITree.dtor_Tau, ITree.ctor_dtor]

@[simp] theorem ITree.bind_Vis_eq {X : Type} (e : E X) (k : X → ITree E R) (f : R → ITree E S) :
    ITree.bind (.Vis e k) f = .Vis e fun a => ITree.bind (k a) f := by
  rw [← ITree.ctor_dtor (ITree.bind _ f), ITree.bind_Vis, ← ITree.dtor_Vis, ITree.ctor_dtor]

theorem ITree.bind_ret (t : ITree E R) : ITree.bind t .Ret = t := by
  refine ITree.bisim (fun x y => x = ITree.bind y .Ret) ?_ rfl
  rintro _ y rfl
  rw [ITree.dtor_bind]
  rcases y.dtor with r | u | ⟨e, k⟩
  · dsimp only; rw [ITree.dtor_Ret]; exact .Ret r
  · exact .Tau _ _ rfl
  · exact .Vis e _ _ fun _ => rfl

theorem ITree.bind_assoc {T : Type} (t : ITree E R) (f : R → ITree E S) (g : S → ITree E T) :
    ITree.bind (ITree.bind t f) g = ITree.bind t fun r => ITree.bind (f r) g := by
  refine ITree.bisim (fun x y => x = y ∨ ∃ t : ITree E R,
    x = ITree.bind (ITree.bind t f) g ∧ y = ITree.bind t fun r => ITree.bind (f r) g) ?_
    (.inr ⟨t, rfl, rfl⟩)
  rintro x y (rfl | ⟨t, rfl, rfl⟩)
  · rw [← ITree.F.map_id x.dtor]
    exact ITree.F.rel_map _ _ _ _ fun _ => Or.inl rfl
  rw [ITree.dtor_bind (ITree.bind t f), ITree.dtor_bind t, ITree.dtor_bind t]
  rcases t.dtor with r | u | ⟨e, k⟩
  · dsimp only
    rw [← ITree.dtor_bind, ← ITree.F.map_id (ITree.bind (f r) g).dtor]
    exact ITree.F.rel_map _ _ _ _ fun _ => Or.inl rfl
  · exact .Tau _ _ (.inr ⟨u, rfl, rfl⟩)
  · exact .Vis e _ _ fun a => .inr ⟨k a, rfl, rfl⟩

/-! ### The monad -/

/-- `ITree E` is a lawful monad. Since `bind` does not insert a `Tau` after a `Ret`, the monad
laws hold up to strong bisimulation, which is equality here. -/
instance : Monad (ITree E) where
  pure := ITree.Ret
  bind := ITree.bind

instance : LawfulMonad (ITree E) := LawfulMonad.mk'
  (id_map := ITree.bind_ret)
  (pure_bind := ITree.bind_Ret)
  (bind_assoc := ITree.bind_assoc)

@[simp] theorem ITree.bind_def (t : ITree E R) (f : R → ITree E S) : t >>= f = ITree.bind t f :=
  rfl

@[simp] theorem ITree.pure_def (r : R) : (pure r : ITree E R) = ITree.Ret r := rfl

/-- The first step of `trigger e >>= f`: the event, then the continuation. -/
theorem ITree.bind_trigger {X : Type} (e : E X) (f : X → ITree E R) :
    (ITree.trigger e >>= f).dtor = .Vis e fun x => ITree.bind (.Ret x) f :=
  ITree.bind_Vis _ _ _

/-- Events of a small imperative language. -/
inductive IOE : Type → Type
  | read : IOE Nat
  | write (n : Nat) : IOE Unit

/-- Read a number and return its successor, in `do` notation. -/
def succRead : ITree IOE Nat := do
  let n ← ITree.trigger .read
  pure (n + 1)

/-- Read twice, write the sum, return it. -/
def sumRead : ITree IOE Nat := do
  let n ← ITree.trigger .read
  let m ← ITree.trigger .read
  ITree.trigger (.write (n + m))
  pure (n + m)

theorem succRead_dtor :
    succRead.dtor = .Vis IOE.read fun n => ITree.bind (.Ret n) fun n => pure (n + 1) :=
  ITree.bind_trigger _ _

theorem sumRead_dtor :
    sumRead.dtor = .Vis IOE.read fun n => ITree.bind (.Ret n) fun n => (do
      let m ← ITree.trigger .read
      ITree.trigger (.write (n + m))
      pure (n + m)) :=
  ITree.bind_trigger _ _

/-- With the monad laws holding on the nose, `do` blocks compute to plain trees. -/
example : succRead = .Vis IOE.read fun n => .Ret (n + 1) := by
  simp [succRead, ITree.trigger]

/-- Case analysis on an interaction tree, with the implicit binder in the `Vis` case. -/
example (t : ITree E R) : t = .spin ∨ t ≠ .spin := by
  cases t with
  | Ret r => exact Or.inr (by rw [ITree.spin_eq]; simp)
  | Tau u => exact Classical.em _
  | Vis e k => exact Or.inr (by rw [ITree.spin_eq]; simp)

end

end CodataTest
