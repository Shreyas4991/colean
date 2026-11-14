import Colean

noncomputable section

/-! The examples of `README.md`, checked. -/

namespace ReadmeCorec

-- Coinductive types

/-- Infinite lists -/
codata Stream (α : Type)
  | cons (head : α) (tail : Stream α)

def Stream.map {α β : Type} (f : α → β) : Stream α → Stream β :=
  -- `corec` defines a corecursive function
  Stream.corec fun s : Stream α =>
    -- to pattern match, first apply the destructor `dtor`
    match s.dtor with
    | .cons h t => .cons (f h) t

-- Coinduction: bisimilar streams are equal
theorem Stream.map_comp {α β γ : Type} (f : α → β) (g : β → γ) (s : Stream α) : 
    s.map (g ∘ f) = (s.map f).map g := by
  refine Stream.bisim (fun lhs rhs => ∃ s, lhs = s.map (g ∘ f) ∧ rhs = (s.map f).map g)
    ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨s, rfl, rfl⟩
  -- coinductive step
  cases s with | cons h t => -- `cases` works with `codata`
  simp [map]
  use t

-- An easier way to define corecursive functions is to use Lean's `partial_fixpoint`:

/-- Potentially infinite lists -/
-- `with_ccpo` creates a CCPO structure, which `partial_fixpoint` uses
@[with_ccpo (bot := nil)] -- `bot` chooses the bottom `⊥` of the CCPO; it can be omitted here
codata CoList (α : Type)
  | nil
  | cons (head : α) (tail : CoList α)

def nats (n : Nat) : CoList Nat :=
  .cons n (nats (n + 1))
partial_fixpoint

def CoList.filter {α : Type} (p : α → Bool) (s : CoList α) : CoList α :=
  match s.dtor with
  | .nil => .nil
  | .cons h t => if p h then .cons h (t.filter p) else t.filter p
partial_fixpoint

example : (nats 0).filter (· % 2 == 0) = .cons 0 ((nats 2).filter (· % 2 == 0)) := by
  repeat
    rw [CoList.filter, nats]; simp

-- One can define indexed families:

/-- Infinite walk starting from `n` -/
codata Walk : Int → Type
  | up {n : Int} (tail : Walk (n + 1)) : Walk n
  | down {n : Int} (tail : Walk (n - 1)) : Walk n

-- The step may depend on the index: always head back to `0`.
def Walk.toZero {n : Int} : Walk n :=
  .corec (s := ()) fun (n : Int) (_ : Unit) =>
    if n < 0 then .up () else .down ()

/-- A helper for the next definition -/
def Walk.cast {m n : Int} (h : m = n) (w : Walk m) : Walk n := h ▸ w

-- The state may depend on the index: a walk from `-i` is the state at `i`.
def Walk.mirror {n : Int} (w : Walk n) : Walk (-n) :=
  .corec (S := fun i => Walk (-i))
    (fun _ w => match w.dtor with
      | .up t => .down (t.cast (by lia))
      | .down t => .up (t.cast (by lia)))
    (w.cast (by lia))

-- Mutually dependent types:
mutual
/-- Trees of any depth and any breadth. -/
codata Tree (α : Type)
  | node (a : α) (children : Forest α)
/-- Sequences of trees, possibly infinite. -/
codata Forest (α : Type)
  | nil
  | cons (t : Tree α) (f : Forest α)
end

-- Corecursion with one state and one step per type: the infinite binary tree.
-- A forest's state counts the trees still to come.
def Tree.binary {α : Type} (a : α) : Tree α :=
  -- .node a (.cons binary (.cons binary nil))
  Tree.corec (fun () => .node a (2 : Fin 3)) (fun | 0 => .nil | 1 => .cons () 0 | 2 => .cons () 1) ()

theorem Tree.binary_eq {α : Type} (a : α) : 
    binary a = .node a (.cons (binary a) <| .cons (binary a) <| .nil) := by
  conv => lhs; rw [binary, Tree.corec_eq]
  simp [Forest.corec_eq]
  rfl

-- And nest through other types:

/-- Nondeterministic computations: a result, or a finite choice of ways to continue. -/
codata NDet (α : Type)
  | ret (a : α)
  | choose (next : List (NDet α)) -- nesting through `List`

def NDet.coin : NDet Bool := .choose [.ret false, .ret true]

/-- Flip coins until one shows `true`, counting the flips: stop now, or flip again. -/
def NDet.flips : NDet Nat :=
  NDet.corec (S := Nat ⊕ Nat) (s := .inr 0) (fun
    | .inl n => .ret n
    | .inr n => .choose [.inl (n + 1), .inr (n + 1)]) 

-- One can nest through a predefined set of standard Lean types (`Prod`, `Sum`, `List`, `Option`,
-- etc.) and through types defined with `codata` and `data` (see below).

-- Inductive types can be defined with `data`:

data LogicalFormula
  | const (b : Bool)
  | and (x y : LogicalFormula)
  | or (x y : LogicalFormula)
  | not (x : LogicalFormula)

-- They can also be in a `mutual` block and used in nesting. 
-- Finally, we can mix `data` and `codata` in a `mixed_mutual` block:

mixed_mutual
/-- Stream processors: they keep producing outputs forever... -/
codata SP (I O : Type)
  | step (s : Step I O)
/-- ...and read finitely many inputs before each output. -/
data Step (I O : Type)
  | get (k : I → Step I O)
  | put (o : O) (next : SP I O)
end

/-- Read two inputs, output their sum, forever. -/
def SP.pairSums : SP Nat Nat :=
  .corec (S := Unit) (s := ()) fun _ => .step (.get fun a => .get fun b => .put (a + b) ()) 

-- It is important to note that `mixed_mutual`, unlike a uniform `mutual`, depends on the order of
-- the types. Types are defined bottom-up, each treating the types above it as placeholders. So
-- `data Step` only makes the reads up to the next `put` finite, while `codata SP` lets the
-- processor as a whole run forever. In the reverse order, `SP I O` would be empty: the whole
-- processor would have to be finite, but nothing ever ends it.

end ReadmeCorec
