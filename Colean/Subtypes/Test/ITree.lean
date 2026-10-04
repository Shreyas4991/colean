import Colean.Subtypes.CodataCmd

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

noncomputable section

variable {E : Type → Type} {R S : Type}

/-- The silently diverging tree. -/
def ITree.spin : ITree E R := ITree.corec (fun _ => .Tau ()) ()

theorem ITree.spin_eq : (ITree.spin : ITree E R) = .Tau .spin := ITree.corec_eq _ _

/-- Trigger an event and return its answer. -/
def ITree.trigger {X : Type} (e : E X) : ITree E X := .Vis e .Ret

/-- Monadic bind, by corecursion: run `t`, then run `f r` on its result. -/
def ITree.bind (t : ITree E R) (f : R → ITree E S) : ITree E S :=
  ITree.corec (fun (x : ITree E R ⊕ ITree E S) => match x with
    | .inl t =>
      match t.dtor with
      | .Ret r => .Tau (.inr (f r))
      | .Tau u => .Tau (.inl u)
      | .Vis e k => .Vis e fun a => .inl (k a)
    | .inr u =>
      match u.dtor with
      | .Ret s => .Ret s
      | .Tau v => .Tau (.inr v)
      | .Vis e k => .Vis e fun a => .inr (k a)) (.inl t)

theorem ITree.bind_Tau (t : ITree E R) (f : R → ITree E S) :
    (ITree.bind (.Tau t) f).dtor = .Tau (ITree.bind t f) := by
  simp [ITree.bind, ITree.dtor_corec]

theorem ITree.bind_Vis {X : Type} (e : E X) (k : X → ITree E R) (f : R → ITree E S) :
    (ITree.bind (.Vis e k) f).dtor = .Vis e fun a => ITree.bind (k a) f := by
  simp [ITree.bind, ITree.dtor_corec]

/-! ### The monad -/

/-- `ITree E` is a monad. The monad laws hold only up to weak bisimulation (`bind` inserts a
`Tau` after a `Ret`), as in the Coq library, so there is no `LawfulMonad` instance. -/
instance : Monad (ITree E) where
  pure := ITree.Ret
  bind := ITree.bind

@[simp] theorem ITree.bind_def (t : ITree E R) (f : R → ITree E S) : t >>= f = ITree.bind t f :=
  rfl

@[simp] theorem ITree.pure_def (r : R) : (pure r : ITree E R) = ITree.Ret r := rfl

/-- The first step of `trigger e >>= f`: the event, then the continuation. -/
theorem ITree.bind_trigger {X : Type} (e : E X) (f : X → ITree E R) :
    (ITree.trigger e >>= f).dtor = .Vis e fun x => ITree.bind (.Ret x) f := by
  simp [ITree.trigger, ITree.bind, ITree.dtor_corec]

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

/-- Case analysis on an interaction tree, with the implicit binder in the `Vis` case. -/
example (t : ITree E R) : t = .spin ∨ t ≠ .spin := by
  cases t with
  | Ret r => exact Or.inr (by rw [ITree.spin_eq]; simp)
  | Tau u => exact Classical.em _
  | Vis e k => exact Or.inr (by rw [ITree.spin_eq]; simp)

end

end CodataTest
