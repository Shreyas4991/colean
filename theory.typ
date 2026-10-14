// The theory behind `codata` and `data`.  Build with:  typst compile theory.typ

#set page(paper: "a4", margin: 2.5cm, numbering: "1")
#set text(size: 11pt, lang: "en")
#set par(justify: true)
#set heading(numbering: "1.")
#show heading: set block(above: 1.6em, below: 0.9em)
#show raw.where(block: false): set text(size: 0.92em)
#show raw.where(block: true): set block(inset: 0.6em, fill: luma(245), radius: 3pt, width: 100%)

// Upright names used in formulas.
#let Type = math.sans("Type")
#let Fam = math.op("Fam")
#let Shape = math.op("Shape")
#let idx = math.op("idx")
#let All = math.op("All")
#let Rel = math.op("Rel")
#let ctor = math.op("ctor")
#let dtor = math.op("dtor")
#let fold = math.op("fold")
#let corec = math.op("corec")
#let rec = math.op("rec")
#let Raw = math.op("Raw")
#let List = math.op("List")
#let Option = math.op("Option")
#let Fin = math.op("Fin")
#let encode = math.op("encode")
#let IsWf = math.op("IsWf")
#let IsFin = math.op("IsFin")
#let toC = math.op("toC")
#let ofC = math.op("ofC")
#let Sh = math.op("Sh")
#let Pos = math.op("Pos")
#let pidx = math.op("pidx")
#let Blk = math.op("Blk")
#let Which = math.op("Which")
#let Tree = math.op("Tree")
#let Forest = math.op("Forest")
#let Rose = math.op("Rose")
#let Trace = math.op("Trace")
#let Menu = math.op("Menu")
#let Proc = math.op("Proc")
#let Entry = math.op("Entry")
#let Dir = math.op("Dir")
#let Stream = math.op("Stream")
#let Vec = math.op("Vec")
#let cons = math.op("cons")
#let nil = math.op("nil")
#let Fs = ($F_sigma$).body
#let sh = math.italic("sh")

#align(center)[
  #text(size: 17pt, weight: "bold")[The theory behind `codata` and `data`]
]
#v(0.8em)

What the commands build, mathematically: every inductive or coinductive family, nested type
and mutual block is one construction, a subtype of a single general type cut out by a
fixpoint of a predicate. "Inductive" and "coinductive" mean initial algebra and final
coalgebra throughout. Elaboration, generated names and proof scripts are left out; the
contracts are in `contract.md`.


= Signatures and their fixpoints

Every inductive or coinductive family is defined by a signature, which is extracted from its
declaration: the constructor list, read as below, gives the signature, and the family is the
least or the greatest fixpoint of the signature's functor. Everything else, the constructors,
the recursor or corecursor, induction or coinduction, is derived from the fixpoint.

*Families.* Fix an index type $I : Type$. A family over $I$ is $X : I -> Type$,
a map of families is $forall i, thin X thin i -> Y thin i$; families and their maps form the category
$Fam thin I$. A plain type is a family over $1$.

*Signatures.* A signature $sigma$ over $I$ consists of

- shapes $Shape : I -> Type$: at each index, the constructors producing that index
  together with their non-recursive data;
- positions $B : forall i, thin Shape thin i -> Type$: for each shape, its recursive
  arguments;
- an index $idx : B thin i thin s -> I$: the index of the recursive argument at each position.

Its functor on families

$ Fs thin X thin i = Sigma_(s : Shape thin i) thin Pi_(b : B thin i thin s) thin X thin (idx thin b) $

sends a family $X$ to one layer of the type with $X$ at the recursive positions: at index
$i$, a constructor with its data and, for every recursive argument, a value of $X$ at the
argument's index. It is an indexed polynomial functor, an indexed container. Reading a
constructor list: a shape at index $i$ is a constructor with result index $i$ together with
its non-recursive data; a recursive argument $t : T thin j$ contributes one position of index
$j$, an argument $f : (a : A) -> T thin (j thin a)$ contributes $A$-many positions of index $j thin a$; an
argument nested through a container is reduced in §3. Every strictly positive constructor
list is of this form.

Two conventions:

+ A type without indices is a family over $I = 1$: one index, and every shape and position
  at it.
+ Several indices, $T : (i_1 : I_1) -> I_2 thin i_1 -> Type$, are merged into a single
  index by a dependent product, $I = Sigma_(i_1 : I_1) thin I_2 thin i_1$; the family is read over it,
  and the declarations with the separate indices are the curried forms.

== Examples

```lean
codata Stream (α : Type u)
  | cons (hd : α) (tl : Stream α)
```

$I = 1$. One constructor with data $alpha$, so $Shape = alpha$; it has one recursive argument,
so $B thin a = 1$, at the only index. Hence $Fs thin X = alpha times X$, with
$Fs thin f thin (a, x) = (a, f thin x)$, and $nu Fs$ is the streams, $nu Fs tilde.equiv (NN -> alpha)$. The
least fixpoint $mu Fs$ of the same signature is empty: a well-founded tree needs a shape
without positions.

```lean
data Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons {n : Nat} (a : α) (v : Vec α n) : Vec α (n + 1)
```

$I = NN$. At index $0$ there is one shape, $nil$; at index $n + 1$ the shapes are
$cons thin a$ for $a : alpha$: $Shape thin 0 = 1$, $Shape thin (n + 1) = alpha$. The shape $nil$ has no
positions, $cons thin a$ has one, of index $n$: $B thin 0 thin nil = 0$, $B thin (n + 1) thin (cons thin a) = 1$ with
$idx = n$. Hence $Fs thin X thin 0 = 1$ and $Fs thin X thin (n + 1) = alpha times X thin n$, and $mu Fs$ is the
vectors. Here $nu Fs = mu Fs$: the index decreases along every path, so every tree of the
signature is finite.

== The contract

This subsection defines the contract: what the commands promise about the family of a
signature, and what makes it the inductive or the coinductive family. §2 describes its
solution, the construction of a family satisfying the contract.

*The action on maps.* A map of families $f : forall i, thin X thin i -> Y thin i$ is applied to a
layer at every recursive position, the shape being kept:

$ Fs thin f : forall i, thin Fs thin X thin i -> Fs thin Y thin i, wide Fs thin f thin ⟨s, c⟩ = ⟨s, thin b |-> f thin (idx thin b) thin (c thin b)⟩. $

For streams, $Fs thin f thin (a, x) = (a, f thin x)$; for vectors at index $n + 1$,
$Fs thin f thin (a, x) = (a, f thin n thin x)$. This action satisfies the functor laws,
$Fs thin id = id$ and $Fs thin (g compose f) = Fs thin g compose Fs thin f$, so $Fs$ is a functor on
$Fam thin I$.

*Liftings.* From the action on maps alone, any functor on families lifts predicates and
relations on the families to predicates and relations on the layers. A predicate
$P : forall i, thin X thin i -> "Prop"$ is lifted to the predicate $All thin P$ on layers of $X$:
$All thin P thin y$ holds when $y$ is the image of a layer whose recursive components carry proofs
of $P$,

$ All thin P thin y :<==> exists z : Fs thin {x | P thin x} thin i, quad Fs thin pi_1 thin z = y, $

where ${x | P thin x}$ is the subtype family $i |-> {x : X thin i | P thin i thin x}$ and $pi_1$ its projection
to $X$. For a polynomial functor this says that every recursive component of $y$ satisfies
$P$: $All thin P thin ⟨s, c⟩ <==> forall b, thin P thin (idx thin b) thin (c thin b)$. For streams,
$All thin P thin (a, x) <==> P thin x$: the tail satisfies $P$.

A relation $R : forall i, thin X thin i -> Y thin i -> "Prop"$ is lifted to a relation between layers
of $X$ and layers of $Y$: $Rel thin R thin a thin b$ holds when $a$ and $b$ are the two images of a layer
whose recursive components are $R$-related pairs,

$ Rel thin R thin a thin b :<==> exists z : Fs thin {(x, y) | R thin x thin y} thin i, quad Fs thin pi_1 thin z = a and Fs thin pi_2 thin z = b, $

with ${(x, y) | R thin x thin y}$ the subtype family $i |-> {p : X thin i times Y thin i | R thin i thin p_1 thin p_2}$ and
$pi_1$, $pi_2$ its projections to $X$ and $Y$. For a polynomial functor
the pair of projections $Fs thin (X times Y) -> Fs thin X times Fs thin Y$ is injective, with image the
pairs of layers with the same shape, so two layers are related when they have the same shape
and related components: $Rel thin R thin ⟨s, c⟩ thin ⟨s', c'⟩ <==> s = s' and forall b, thin R thin (c thin b) thin (c' thin b)$.
For streams, $Rel thin R thin (a, x) thin (a', x') <==> a = a' and R thin x thin x'$: equal heads and related
tails.

*The contract of an inductive family.* The inductive family of $sigma$ is an initial algebra
of $Fs$: a family $T$ with $ctor : Fs thin T -> T$ such that every algebra $a : Fs thin S -> S$
receives exactly one map $fold thin a : T -> S$ with $fold thin a compose ctor = a compose Fs thin (fold thin a)$.
The command promises:

+ the constructor $ctor : forall i, thin Fs thin T thin i -> T thin i$;
+ the fold $fold : (forall i, thin Fs thin S thin i -> S thin i) -> forall i, thin T thin i -> S thin i$;
+ its computation rule, for $y : Fs thin T thin i$, $fold thin a thin (ctor thin y) = a thin i thin (Fs thin (fold thin a) thin y)$;
+ induction: for every $P : forall i, thin T thin i -> "Prop"$,
  $ (forall i thin (y : Fs thin T thin i), thin All thin P thin y -> P thin i thin (ctor thin y)) -> forall i thin (t : T thin i), thin P thin i thin t. $

Existence of $fold$ is items 2 and 3, and induction is equivalent to its uniqueness:
uniqueness follows from induction on the predicate "the two maps agree at $t$", and induction
follows from uniqueness applied to the subtype family ${t | P thin t}$, which is an algebra when
the hypothesis of induction holds. So the contract says exactly that $T$ is an initial
algebra.

*The contract of a coinductive family.* Dually, the coinductive family of $sigma$ is a final
coalgebra: a family $T$ with $dtor : T -> Fs thin T$ such that every coalgebra
$c : S -> Fs thin S$ receives exactly one map $corec thin c : S -> T$ with
$dtor compose corec thin c = Fs thin (corec thin c) compose c$. The command promises:

+ the destructor $dtor : forall i, thin T thin i -> Fs thin T thin i$;
+ the corecursor $corec : (forall i, thin S thin i -> Fs thin S thin i) -> forall i, thin S thin i -> T thin i$;
+ its computation rule, for $s : S thin i$, $dtor thin (corec thin c thin s) = Fs thin (corec thin c) thin (c thin i thin s)$;
+ coinduction: for every $R : forall i, thin T thin i -> T thin i -> "Prop"$,
  $ (forall i thin (x thin y : T thin i), thin R thin i thin x thin y -> Rel thin R thin (dtor thin x) thin (dtor thin y)) -> forall i thin (x thin y : T thin i), thin R thin i thin x thin y -> x = y. $

A relation satisfying the hypothesis of coinduction is a bisimulation: related elements have
related layers. Coinduction is equivalent to the uniqueness of $corec$: a bisimulation is a
coalgebra on the relation whose two projections are coalgebra morphisms into $T$, hence equal
by uniqueness; conversely, given two coalgebra morphisms out of $S$, the relation "images of
one state" is a bisimulation. So the contract says exactly that $T$ is a final coalgebra.

*Derived structure.* Everything else follows from the contracts alone. Lambek's lemma gives
the inverse of the structure map: $dtor := fold thin (Fs thin ctor)$ for the inductive family, with
$ctor compose dtor = id$ by induction and $dtor compose ctor = id$ by the computation rule;
$ctor := corec thin (Fs thin dtor)$ for the coinductive family, with $ctor compose dtor = id$ by
coinduction and $dtor compose ctor = id$ by the computation rule. Hence $ctor$ is injective,
case analysis on $T$ is case analysis on the layer $dtor thin t$, and any two families satisfying
the contract are isomorphic, by the fold or the corecursor in both directions. The dependent
recursor of the inductive family, with a motive $P : forall i, thin T thin i -> "Sort"$ and the
value of $P$ at every recursive component as induction hypothesis, follows too: fold into the
family $Sigma_t thin P thin t$ and transport along the uniqueness of the first projection; the
commands provide it as the eliminator of the `induction` tactic. The two liftings are fixed
by the action on maps rather than chosen, so induction and coinduction are exactly the
principles of $Fs$: the contract is tight.


= All fixpoints as subtypes of one type

In this section we show how to construct types satisfying the contracts listed in the
previous section. The idea: both families of a signature are modelled as subtypes of one
type of trees, $Raw$, cut out by a predicate; the predicate of the coinductive family is
defined with Lean's `coinductive_fixpoint`, the one of the inductive family with
`inductive_fixpoint`, and the contracts are proved once, for all signatures.

*The $Raw$ type.* $Raw thin I thin L := List thin I -> Option thin L$ is the type of trees branching
over $I$ with labels in $L$, presented by the label at every path (`none` where there is no
node). It is a final coalgebra of $X |-> (Option thin L) times (I -> X)$: a tree is its root label
together with an $I$-indexed family of children, every coalgebra unfolds into it by recursion
on paths, and two trees related by a bisimulation, a relation that matches roots and is
preserved by taking children, are equal, by induction on paths. This is the only place where
trees are inspected.

*Encoding a signature.* For a signature $sigma$ take the labels $L_sigma := Sigma_i thin Shape thin i$,
an index with a shape, and the erased labels $L^0_sigma := Sigma_i thin Shape_0 thin i$, where
$Shape_0$ are the erased shapes of §3: the shapes without the values of a type parameter
(without a parameter, $Shape_0 = Shape$ and $L^0_sigma = L_sigma$). The branching type is
$I_sigma := Sigma_(l : L^0_sigma) thin B thin l_1 thin l_2$, an erased label together with one of
its positions: the branching of a tree does not depend on the values of a parameter, which is
what makes a declared type a container in its parameter. One layer $encode thin i thin ⟨s, c⟩$
is the tree with root $(i, s)$, the child $c thin b$ at the branch $((i, s), b)$ and the empty
tree at every other branch. The empty children make $encode$ injective, and finding them
requires deciding the equality of labels: the constructors are classical, which we accept.

*The predicates and the types.* Let

$ IsWf thin i thin t <==> exists s thin c, quad t = encode thin i thin ⟨s, c⟩ and forall b, thin IsWf thin (idx thin b) thin (c thin b) $

as the greatest fixpoint of this equation on predicates over $I times Raw$, and $IsFin$ the
same equation as a least fixpoint (Lean's `coinductive_fixpoint` and `inductive_fixpoint`).
Then

$ nu Fs thin i := { t : Raw thin I_sigma thin L_sigma | IsWf thin i thin t } wide mu Fs thin i := { t : Raw thin I_sigma thin L_sigma | IsFin thin i thin t } $

and $mu Fs subset.eq nu Fs$. Both predicates are fixpoints of the one-layer operator, which
gives $dtor$ (the root shape and the children, at their indices) and $ctor$ ($encode$) with
their two laws, uniformly. For the coinductive family, $corec$ is the corecursion of $Raw$ on
the coalgebra $Option thin (Sigma_i thin S thin i) -> (Option thin L_sigma) times (I_sigma -> Option thin (Sigma_i thin S thin i))$,
with `none` unfolding to the empty tree, and coinduction is the bisimulation principle of
$Raw$ read back into the subtype: a relation on the subtype that is preserved by $dtor$
matches roots and children. For the inductive family, $rec$ is well-founded recursion on the
relation "is an immediate child of", whose well-foundedness is the induction principle of the
least fixpoint $IsFin$; $fold$ and induction follow, and the computation rules of $rec$ hold
propositionally, the price of the encoding.

The user-facing functor $F$ (the constructor list as an inductive type) is isomorphic to
$Fs$ by $toC$/$ofC$, and the contracts are transported along the isomorphism. So one general
type and two native fixpoints of predicates give every family of §1, once and for all
signatures.


= Nested types, and fixpoints as containers

*Containers.* A container is a functor $G : Type -> Type$ with a natural
isomorphism

$ G thin X tilde.equiv Sigma_(sh : Sh) thin Pos thin sh -> X $

a polynomial functor in one variable: a value of $G thin X$ is a shape and a value of $X$ at
each of its positions. An indexed container acts on families,
$G thin X tilde.equiv Sigma_(sh) thin Pi_(q : Pos thin sh) thin X thin (pidx thin sh thin q)$, every position
carrying an index. $List$ (shapes $NN$, positions $Fin thin n$), $Option$, $A times (-)$ are
containers; containers compose (a shape of the composite is a shape with a shape at each
position, a position is a position with a position there).

*Nested occurrences reduce to signatures.* A constructor argument $x : G thin (T thin j)$ is, through
the isomorphism, a shape $sh : Sh$ as extra non-recursive data together with $Pos thin sh$-many
recursive positions of index $j$ ($pidx thin sh thin q$ for an indexed container). So a constructor
list with occurrences nested through containers is again a signature: this is the reduction
of nested types to indexed families, specialised to containers, where it is exact since only
the positions of $G$ are needed. The functor $F$ keeps $G thin X$ as a field, `F.map` acts inside
$G$ by the container's map, and $Rel$ relates nested fields with the same shape and pointwise
related contents.

*Fixpoints are containers in a parameter.* Let $T thin alpha := mu F_(sigma alpha)$ or
$nu F_(sigma alpha)$, where the parameter $alpha$ occurs in the shapes only at positions:
$Shape_alpha thin i tilde.equiv Sigma_(s_0 : Shape_0 thin i) thin P thin s_0 -> alpha$, with erased
shapes $Shape_0$ and parameter positions $P$ (a field of type $alpha$, a field $A -> alpha$, a
field $G thin alpha$ through a container). Then

$ T thin alpha tilde.equiv Sigma_(t_0 : T_0) thin Pos thin t_0 -> alpha $

where $T_0$ is the fixpoint of the erased signature (the trees without the values) and a
position of $t_0$ is a node of $t_0$ together with a parameter position of its erased shape.
The isomorphism erases the values of a tree and reattaches values at the positions of an
erased tree, pathwise on $Raw$, and the two are inverse by extensionality on paths. This is
the classical fact that the W-type, or M-type, of a polynomial functor in several variables
is polynomial in the remaining variables (Mathlib's `MvPFunctor.wp` and `mp`); for a family
parameter $X : J -> Type$ the same holds with an indexed container. So containers are
closed under $mu$ and $nu$ in a parameter, and a type declared with a parameter may be nested
through by later declarations: $Rose thin alpha := nu T. thin alpha times Forest thin T$ with
$Forest$ the declared finite lists, and by composition $Trace thin alpha thin (Menu thin alpha thin (Proc thin alpha))$
in §4. The relator on a declared container is computed on its constructors
($Rel thin R thin (cons thin t thin f) thin (cons thin t' thin f')$ from $R thin t thin t'$ and $Rel thin R thin f thin f'$), which is what a
coinduction through a nested inductive part uses.


= Mutual blocks

*Uniform blocks.* A block $T_1, dots, T_n : I -> Type$, all inductive or all
coinductive, with constructors mentioning each other, is one family
$Blk : Which times I -> Type$ over the enumeration $Which = {1, dots, n}$ of the types
(with different index types one would take $Sigma_m thin I_m$), whose signature at $(m, i)$ is that
of $T_m$ at $i$, a recursive argument $t : T_(m') thin j$ being a position of index $(m', j)$. Then
$T_m := Blk thin (m, -)$, and mutual recursion, corecursion, induction and coinduction are those
of the family, with a state or motive over the whole block. Everything follows from §1–2;
the per-type constructors and case analysis are notation.

*Mixed blocks are nested fixpoints.* Let the block be a system

$ X = F thin X thin Y quad "inductive" wide Y = G thin X thin Y quad "coinductive" $

with $F$, $G$ signatures in two families, every occurrence of $X$ or $Y$ a position. A
solution is a pair satisfying both equations up to isomorphism. The system has several
solutions; two of them have closed forms, each built by two nested one-variable fixpoints,
which is what §1–3 provide:

- coinductive outer: $X(Y) := mu X. thin F thin X thin Y$, a container in $Y$ by §3;
  $Y := nu Y. thin G thin (X(Y)) thin Y$, a coinductive type nesting through $X(-)$; finally
  $X := X(Y)$;
- inductive outer: $Y(X) := nu Y. thin G thin X thin Y$, a container in $X$;
  $X := mu X. thin F thin X thin (Y(X))$; $Y := Y(X)$.

The inner fixpoint is a declaration with an extra parameter, the outer one nests through it.

*They differ.* Take $Tree = A times Forest$, $Forest = 1 + Tree times Forest$.

- $nu$ outer: $Forest thin T = mu F. thin 1 + T times F = List thin T$, then
  $Tree = nu T. thin A times List thin T$: trees with finitely many children at every node and
  paths of unbounded, possibly infinite, length; $Forest = List thin Tree$.
- $mu$ outer: $Tree thin F = nu T. thin A times F = A times F$ (the greatest fixpoint of a
  constant functor is the constant), then $Forest = mu F. thin 1 + (A times F) times F$, a
  finite structure; $Tree = A times Forest$, finite.

Both pairs satisfy both equations. In general the inductive-outer solution embeds in the
coinductive-outer one, $mu X. thin nu Y subset.eq nu Y. thin mu X$; the coinductive-outer
solution allows infinite descent through the inductive type provided each pass through it is
finite (finitely many children per node, infinitely many levels), the inductive-outer one
allows infinite descent only through the coinductive type. The two coincide exactly when the
system has no cycle passing through both kinds, and in that case the two declarations can be
made one after the other. Another instance: directories as lists of entries and entries as
name, contents and next version; $Entry$ outer allows an entry to contain itself, $Dir$ outer
makes the nesting of directories well-founded and only the version chains infinite. So a
mixed block has to state its nesting order, and the textual order does: the first
declaration is outermost.

*Runs.* By Bekič's lemma nested fixpoints of the same kind coincide with the simultaneous
one, $mu X. thin mu Y. thin F thin X thin Y tilde.equiv (mu (X, Y). thin F thin X thin Y)_1$ and likewise
for $nu$, so consecutive declarations of the same kind form a run whose internal order is
immaterial, and a block is a sequence of runs $R_1 supset R_2 supset dots.c supset R_k$,
outermost first: each run is a uniform block with the outer runs as parameters, nesting
through the inner runs. A reference from a run to a run further inside is nested through the
composite of the intermediate containers ($Trace thin alpha thin (Menu thin alpha thin (Proc thin alpha))$). A
reference to a run further outside requires the runs in between to be containers jointly in
several parameters, positions of several sorts; the theory is the same, its implementation
is pending.

*Proof principles compose.* Coinduction on an outer type relates one layer per step, and a
layer holds inner inductive values as data whose positions carry the outer type: the relator
$Rel$ on the container asks for the same shape and related contents, so coinduction sees
through the inductive part one finite layer at a time. Induction on an inner type treats the
outer types as parameters, opaque. An induction inside a coinductive step is parametric in
the outer relation; a coinduction inside an inductive step is a closed statement about the
outer type.


#heading(numbering: none)[Appendix: the layer functors]

The functors the commands accept, formally. Fix an index type $I$; families are
$X : I -> Type$. A *field* is one of

- a constant $A$;
- a recursive argument $X thin j$, or one under a telescope, $(a : A) -> X thin (j thin a)$;
- a nested recursive argument $G thin (X thin j)$ for a container $G$, or
  $G thin (p |-> X thin (j thin p))$ for an indexed container $G$;

and a *layer functor* is a sum, over the constructors producing an index $i$, of a $Sigma$ over
the non-recursive data of a product of fields:

$ F thin X thin i = sum_(c : "ctors" thin i) thin Sigma_(d : D_c) thin Phi_(c, 1)(d, X) times dots.c times Phi_(c, n_c)(d, X), $

where the field types $Phi_(c, k)$ may depend on the data $d$ (the domains $A$, the indices $j$
and the containers may mention it) but the recursive family $X$ occurs only as shown. This is
the reading of a constructor list in §1, with nested arguments allowed.

*Every field is a container.* Each field form is naturally isomorphic to
$Sigma_(sh : Sh) thin Pi_(q : Pos thin sh) thin X thin (pidx thin sh thin q)$:

- a constant $A$: shapes $A$, no positions;
- $X thin j$: one shape, one position, of index $j$;
- $(a : A) -> X thin (j thin a)$: one shape, positions $A$, the position $a$ of index $j thin a$;
- $G thin (X thin j)$: the shapes and positions of $G$, every position of index $j$;
- $G thin (p |-> X thin (j thin p))$: the shapes and positions of $G$, the position $q$ of index $j thin (pidx thin sh thin q)$.

*Containers are closed under the assembly.* A product of containers is a container, with the
pairs of shapes and the sum of the positions; a $Sigma$ over data of containers is a container,
with shapes $Sigma_d$ of the shapes and the positions of the summand; a sum over constructors
likewise. Hence every layer functor is naturally isomorphic to a signature functor,

$ F thin X thin i tilde.equiv Fs thin X thin i = Sigma_(s : Shape thin i) thin Pi_(b : B thin i thin s) thin X thin (idx thin b), $

with $Shape thin i$ the constructors with their data and the shapes of their nested
containers, $B$ the sum of the positions of the fields, and $idx$ as listed. This is the
signature the command extracts, and its fixpoints are those of $F$, since a natural
isomorphism of functors carries algebras and coalgebras across.

*The fixpoint commands.* The nesting is gone before a fixpoint is taken: the predicate
$IsWf thin i thin t <==> exists s thin c, thin t = encode thin i thin ⟨s, c⟩ and forall b, thin IsWf thin (idx thin b) thin (c thin b)$
has the same form for every signature, nested or not, and `coinductive_fixpoint` and
`inductive_fixpoint` are applied to it only. The commands take the least or greatest fixpoint
of an operator on predicates that must be monotone, and prove monotonicity by a tactic that
recognises the recursive occurrence under $exists$, $forall$, $and$, $or$ and matches, which
is all the operator above uses.

The commands do support nesting in general: a recursive occurrence under a guarding operator
$G$ on predicates, such as $IsWf thin (G thin IsWf thin "ts")$ with $G thin P thin "ts" = forall t in "ts", P thin t$,
is accepted once a lemma stating that $G$ is monotone is registered with the tactic, through
the attribute `partial_fixpoint_monotone`, in the implication order for inductive predicates
and in the reverse implication order for coinductive ones. Monotonicity of the guard is the
predicate-level counterpart of the positivity of the guarding functor. The reduction to a
signature makes the requirement disappear, since the lifting through a container is a
$forall$ over its positions.
