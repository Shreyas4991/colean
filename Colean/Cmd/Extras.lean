import Colean.Cmd.Framework

/-!
# The command, step 2b: what is read off the model beyond the contract

*Spec.* Input: the model (signature, isomorphism, `T.ctor`). Output, all justified by the
encoding rather than by the contract (`architecture.md`, step 2b):

* the occurrence structure of the type in its parameter, `T.Sh`, `T.Pos`, (`T.posIdx`),
  `T.occ`, registered as a leaf `T.instOccLeaf`; and the constructor-level lemmas `T.map_cᵢ`,
  `T.rel_cᵢ`, proved by tactic on the encoding (through `T.ctor_eq_ctorC`);
* the dependent recursor `T.rec` into any `Sort`, from the model's well-founded recursion, with
  its computation rule `T.rec_ctor` (propositional).

Everything here is a candidate for derivation from the contract, or for generation on demand.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-! ### The occurrence structure in the parameter -/

/-- For every type of the declaration (and for the block family of a mutual block), its shapes
`T.Sh` (the erased trees), its positions `T.Pos` (a path to a node and a parameter position of
its erased shape), its structure `T.occ : Occ T.Sh T.Pos (fun α => T params α idx)` (an `IOcc`
with the positions' indices `T.posIdx` for a family parameter), from the generic
`PSignature.occ` (`coocc` for `codata`, `iocc`/`icoocc` for a family parameter), and its
registration as a leaf (`T.instOccLeaf`). -/
def genOcc (ctx : Ctx) : CommandElabM Unit := do
  let some pinfo := ctx.param | return
  let a := pinfo.a
  let aTy := pinfo.aTy
  let pExp₀ := ctx.pExp₀
  let pTerms₀ := ctx.pTerms₀
  let (S, e) ← ctx.sigSE
  let fam := ctx.sigId (if ctx.co then `Cotype else `Intype)
  let occFn := ctx.topId (`PSignature ++ (if pinfo.J.isSome then
      (if ctx.co then `icoocc else `iocc) else (if ctx.co then `coocc else `occ)))
  let gen (nmOf : String → Ident) (ixBExp : Array (TSyntax ``bracketedBinderF))
      (idxArgs : Array Term) (fullIdx : Array Term) (Tm : Term) (leaf : Bool) :
      CommandElabM Unit := do
    let pI ← ctx.pack fullIdx
    let Sh := nmOf "Sh"
    let Pos := nmOf "Pos"
    let occ := nmOf "occ"
    elabCommand (← `(abbrev $Sh:ident $[$pExp₀]* $[$ixBExp]* : Type _ :=
      $fam (Codata.PSignature.sig₀ $(ctx.psigp)) $pI))
    let Shp ← appT (← mkAppT Sh pTerms₀) idxArgs
    elabCommand (← `(abbrev $Pos:ident $[$pExp₀]* $[$ixBExp]* (sh : $Shp) : Type _ :=
      Codata.PSignature.Pos $(ctx.psigp) sh.1))
    let Posp ← appT (← mkAppT Pos pTerms₀) idxArgs
    let G ← `(fun ($a:ident : $aTy) => $Tm)
    let body ← `($occFn (ψ := $(ctx.psigp)) (fun ($a:ident : $aTy) => $S)
      (fun ($a:ident : $aTy) => $e) $pI)
    if let some J := pinfo.J then
      let PosIdx := nmOf "posIdx"
      elabCommand (← `(abbrev $PosIdx:ident $[$pExp₀]* $[$ixBExp]* (sh : $Shp) (x : $Posp sh) :
        $J := Codata.PSignature.Pos.idx x))
      let PosIdxp ← appT (← mkAppT PosIdx pTerms₀) idxArgs
      elabCommand (← `(def $occ:ident $[$pExp₀]* $[$ixBExp]* :
        Codata.IOcc $Shp $Posp $PosIdxp $G := $body))
      if leaf then
        let occp ← appT (← mkAppT occ pTerms₀) idxArgs
        elabCommand (← `(instance $(nmOf "instOccLeaf"):ident $[$pExp₀]* $[$ixBExp]* :
          Codata.IOccLeaf $G $Shp $Posp $PosIdxp := ⟨$occp⟩))
    else
      elabCommand (← `(def $occ:ident $[$pExp₀]* $[$ixBExp]* : Codata.Occ $Shp $Posp $G := $body))
      if leaf then
        let occp ← appT (← mkAppT occ pTerms₀) idxArgs
        elabCommand (← `(instance $(nmOf "instOccLeaf"):ident $[$pExp₀]* $[$ixBExp]* :
          Codata.OccLeaf $G $Shp $Posp := ⟨$occp⟩))
  for m in [0:ctx.types.size] do
    gen (ctx.tyId m) (← ctx.uIxBExp) ctx.uIArgs (ctx.fullArgs m) (← ctx.tyAtU m) true
  if ctx.isMutual then
    gen ctx.nm (← ctx.ixBExp) ctx.iArgs ctx.iArgs (← ctx.atI ctx.Tp) false

/-! ### The constructor on the container -/

/-- The framework's constructor is the model's `ctorC` through `toC` (`T.ctor_eq_ctorC`), for the
constructor-level lemmas of the occurrence structure. -/
def genCtorEqCtorC (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let ib ← ctx.ixB
  let iArgs := ctx.iArgs
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let cv ← mkConv ctx
  -- The constructor is the constructor on the container, through `toC` (for the
  -- constructor-level container lemmas).
  let Cot ← `($(ctx.sigId `Cotype) $(ctx.sigp))
  let pTerms := ctx.pTerms
  elabCommand (← `(theorem $(ctx.nm "ctor_eq_ctorC"):ident $[$pImp]* $[$ib]* (y : $FTi) :
      $(ctx.ctor) y = $(ctx.sigId `ctorC) (@$(ctx.toC) $pTerms* $Cot $iArgs* y) :=
    $(ctx.sigId `ctor_eq_ctorC_of) (σ := $(ctx.sigp)) $(cv.ofC) $(cv.toCT) $(cv.ofC_toCT)
      (fun {_} y => $(ctx.ctor) y) (fun {_} t => $(ctx.ctor_dtor) t) (i := $(cv.pI)) y))

/-! ### Constructor-level lemmas for the occurrence structure in the parameter

For a declaration with an occurrence structure in its parameter `α`, `T.map_ctorᵢ` computes
`Occ.map T.occ T.occ f` on a constructor application (`f` at the parameter positions, `map f`
at the recursive ones, `map (map f)` through nested arguments), and `T.rel_ctorᵢ` introduces
`Occ.Rel T.occ T.occ R` on two constructor applications from `R` at the parameter positions and
`Rel R` at the recursive ones; `IOcc` for a family parameter, and the second copy of the
parameter in its own universe. The first reduces to `PSignature.mapV_encode` (the map on the
trees of a constructor, `map_ctorI_val` and its variants) and the computation of `toC`,
`shapeTo` and `shapeOf` on the constructor, the nested arguments first written as `ofC` of
their layers so that `toC_ofC` applies; the second to the first, through the elimination of
`Rel` (`Occ.exists_map_of_rel`, `exists_fn_of_forall` under telescopes) and `Occ.rel_map`. -/

/-- The universe name of the `Type u` in a sort, when it is a plain name. -/
partial def typeLevelName? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Parser.Term.type then
    if stx.getNumArgs == 2 && stx[1].getNumArgs == 1 && stx[1][0].isIdent then
      some stx[1][0].getId
    else none
  else match stx with
    | .node _ _ args => args.findSome? typeLevelName?
    | _ => none

/-- `stx` with every `Type u` (a plain universe name) replaced by `Type u'`. -/
partial def replaceTypeLevel (stx : Syntax) (u : Ident) : Syntax :=
  if stx.isOfKind ``Parser.Term.type then
    if stx.getNumArgs == 2 && stx[1].getNumArgs == 1 && stx[1][0].isIdent then
      Syntax.node .none ``Parser.Term.type #[stx[0], Syntax.node .none nullKind #[u.raw]]
    else stx
  else match stx with
    | .node info k args => .node info k (args.map (replaceTypeLevel · u))
    | _ => stx

def genOccLemmas (ctx : Ctx) : CommandElabM Unit := do
  let some pinfo := ctx.param | return
  let a := pinfo.a
  let aTy := pinfo.aTy
  let isFam := pinfo.J.isSome
  -- The second copy of the parameter, in its own universe.
  let a' := prime a
  let aTy' : Term ← match typeLevelName? aTy.raw with
    | some u =>
      let u' := mkIdent (u.appendAfter "'")
      unless (← getScope).levelNames.contains u'.getId do
        elabCommand (← `(universe $u':ident))
      pure ⟨replaceTypeLevel aTy.raw u'⟩
    | none => pure aTy
  let pImp₀ := ctx.pImp₀
  let pTerms₀ := ctx.pTerms₀
  let occMap := occId isFam `map
  let occRel := occId isFam `Rel
  let occEx := occId isFam `exists_map_of_rel
  let occRelMap := occId isFam `rel_map
  let f : Ident := ⟨(← `(f)).raw⟩
  let R : Ident := ⟨(← `(R)).raw⟩
  let fTy ← if isFam then `(∀ j, $a j → $a' j) else `($a → $a')
  let RTy ← if isFam then `(∀ j, $a j → $a' j → Prop) else `($a → $a' → Prop)
  -- The parameter and the duplicated binders, renamed.
  let subst (dup : Array Name) (t : Term) : Term :=
    ⟨substIds t.raw fun n =>
      if n == a.getId then some a' else if dup.contains n then some (prime (mkIdent n)) else none⟩
  let mapCtorOf := ctx.topId (`PSignature ++ (if isFam then
      (if ctx.co then `map_ctorC_of else `map_ctorI_of)
    else (if ctx.co then `cmap_ctorC_of else `cmap_ctorI_of)))
  let rflPat := mkIdent `rfl
  let W ← if isFam then `(fun j => {p : $a j × $a' j // $R j p.1 p.2})
    else `({p : $a × $a' // $R p.1 p.2})
  let fst ← if isFam then `(fun _ p => p.1.1) else `(fun p => p.1.1)
  let snd ← if isFam then `(fun _ p => p.1.2) else `(fun p => p.1.2)
  let hR ← if isFam then `(fun _ p => p.2) else `(fun p => p.2)
  for c in ctx.ctors do
    let OT ← ctx.recOccOf c.idx
    let dup : Array Name := c.groups.foldl (init := #[]) fun acc g =>
      if g.kind.isData && g.pk.isNone then acc else acc ++ g.ids.map (·.getId)
    -- `map f` and `Rel R` on a recursive argument at the index `idx`.
    let recMap (idx : Array Term) (x : Term) : CommandElabM Term := do
      let O ← ctx.recOccOf idx
      `($occMap $O $O $f $x)
    let recRel (idx : Array Term) : CommandElabM Term := do
      let O ← ctx.recOccOf idx
      `($occRel $O $O $R)
    -- The same at a packed index variable `p`, for the positions of an indexed structure.
    let pId ← freshId "p"
    let pProjs ← ctx.projs (idT pId)
    let recMapP (x : Term) : CommandElabM Term := recMap pProjs x
    let recRelP : CommandElabM Term := recRel pProjs
    -- `map_c`.
    let mut args' : Array Term := #[]
    for g in c.groups do
      for x in g.ids do
        let t ← match g.kind with
          | .data => match g.pk with
            | .none => pure (idT x)
            | .val j => if isFam then `($f $j $x) else `($f $x)
            | .fn tele j =>
              let ys := teleIds tele
              if isFam then `(fun $[$ys:ident]* => $f $j ($x $ys*))
              else `(fun $[$ys:ident]* => $f ($x $ys*))
            | .occ info => `($occMap $(info.o) $(info.o) $f $x)
          | .pos idx => recMap idx (idT x)
          | .fn tele idx =>
            let ys := teleIds tele
            `(fun $[$ys:ident]* => $(← recMap idx (← `($x $ys*))))
          | .occ info =>
            let o := info.o
            if info.indexed then
              `(Codata.IOcc.map $o $o (fun $pId:ident t => $(← recMapP (← `(t)))) $x)
            else
              `(Codata.Occ.map $o $o (fun t => $(← recMap info.idx (← `(t)))) $x)
        args' := args'.push t
    let bs ← binders c
    let lhs ← `($occMap $OT $OT $f $(← ctx.tApp c))
    let rhs ← `(@$(ctx.tCtor c):ident $pTerms₀* $a' $args'*)
    -- The proof: the generic lemma, then the layer of the target shape and the children, both
    -- after unfolding `toC` and `shapeTo` everywhere (`dsimp`, so that the binder types agree)
    -- and rewriting the layers of the mapped structures: in the shapes for every nested
    -- argument, in the children for the recursive ones only. For the arguments nested in the
    -- parameter the erased shape changes with the argument (`(toC (map f as)).1` for
    -- `(toC as).1`) and the transport of a position along the equation of the erased shapes is
    -- reduced by a substitution, one lemma per recursive position (`key`).
    let mut steps : Array (TSyntax `tactic) := #[]
    steps := steps.push (← `(tactic| simp only [$(ctx.tCtor c):ident]))
    if ctx.co then
      steps := steps.push (← `(tactic| simp only [$(ctx.nm "ctor_eq_ctorC"):ident]))
    steps := steps.push (← `(tactic| refine $mapCtorOf (ψ := $(ctx.psigp)) $f _ _ ?_ ?_))
    let unfold ← `(tactic| dsimp only [$(ctx.toC):ident, $(ctx.shapeEquiv):ident, Equiv.coe_fn_mk, $(ctx.shapeTo):ident])
    let nestRw ← c.nested.mapM fun (x, info) => do
      let tcm := occId info.indexed `toC_map
      let rule ← `($tcm:ident $(info.o) $(info.o) (x := $x))
      `(tactic| rw [$rule:term])
    let pnestRw ← c.pnested.mapM fun (x, info) => do
      let tcm := occId info.indexed `toC_map
      let rule ← `($tcm:ident $(info.o) $(info.o) (x := $x))
      `(tactic| rw [$rule:term])
    let hsSteps := #[unfold] ++ nestRw ++ pnestRw ++ #[
      ← `(tactic| refine congrArg (Sigma.mk _) (funext fun p => ?_)),
      ← `(tactic| cases p <;> rfl)]
    -- The `key` lemmas: for the position `x`, with the shapes of the arguments nested in the
    -- parameter quantified on the target side.
    let mut keys : Array (TSyntax `tactic) := #[]
    let mut keyNames : Array Ident := #[]
    if !c.pnested.isEmpty then
      let dvals := c.allDataIds₀.map idT
      let xs ← ctx.nestShapeVals c
      let ns ← pnestShapeVals c
      let pI ← `(($(← ctx.pack c.idx) : $(ctx.Ixp)))
      for g in c.groups do
        if g.kind.isData then continue
        for x in g.ids do
          let qId : Ident := ⟨(← `(q)).raw⟩
          let extra : Array (TSyntax ``bracketedBinderF) ← match g.kind with
            | .fn tele _ => teleBinders tele
            | .occ info => do
              let tc := occId info.indexed `toC
              let Pos := info.Pos
              pure #[← `(bracketedBinderF| ($qId:ident : $Pos ($tc:ident $(info.o) $x:ident).1))]
            | _ => pure #[]
          let extraT : Array Term := match g.kind with
            | .fn tele _ => (teleIds tele).map idT
            | .occ .. => #[idT qId]
            | _ => #[]
          let ns' ← c.pnested.mapM fun (y, _) => freshId s!"n_{y.getId.toString}"
          let nbs ← (c.pnested.zip ns').mapM fun ((_, info), n') =>
            `(bracketedBinderF| ($n':ident : $(info.Sh)))
          let sh ← `(@$(ctx.shape₀Ctor c):ident $pTerms₀* $dvals* $xs* $ns*)
          let sh' ← `(@$(ctx.shape₀Ctor c):ident $pTerms₀* $dvals* $xs* $(ns'.map idT)*)
          let bx ← `(@$(ctx.bCtor c x):ident $pTerms₀* $dvals* $xs* $ns* $extraT*)
          let bx' ← `(@$(ctx.bCtor c x):ident $pTerms₀* $dvals* $xs* $(ns'.map idT)* $extraT*)
          let key ← freshId s!"key_{x.getId.toString}"
          keyNames := keyNames.push key
          let hId : Ident := ⟨(← `(h)).raw⟩
          let hB ← `(bracketedBinderF| ($hId:ident : $sh = $sh'))
          let allB := nbs ++ extra ++ #[hB]
          let extraIds : Array Ident := match g.kind with
            | .fn tele _ => teleIds tele
            | .occ .. => #[qId]
            | _ => #[]
          let allIds := ns' ++ extraIds ++ #[hId]
          keys := keys.push (← `(tactic| have $key:ident : ∀ $[$allB]*,
              Codata.PSignature.castP (ψ := $(ctx.psigp)) (i := $pI) $hId $bx = $bx' := by
            intro $[$allIds:ident]*
            cases $hId:ident
            rfl))
    let closers ← keyNames.mapM fun key => `(tactic| (rw [$key:ident]; rfl))
    let closeAll ← `(tactic| all_goals first | rfl $[| $closers:tactic]*)
    let hcSteps := #[unfold] ++ nestRw ++ keys ++ #[← `(tactic| intro h b), ← `(tactic| cases b), closeAll]
    steps := steps.push (← `(tactic| · $[$hsSteps:tactic]*))
    steps := steps.push (← `(tactic| · $[$hcSteps:tactic]*))
    let mapName := ctx.tName' c "map_" ""
    elabCommand (← `(theorem $mapName:ident $[$pImp₀]* {$a:ident : $aTy} {$a':ident : $aTy'}
        ($f:ident : $fTy) $[$bs]* : $lhs = $rhs := by $[$steps:tactic]*))
    -- `rel_c`: the binders (the ones using the parameter duplicated, with a hypothesis), the
    -- eliminations of the hypotheses into witnesses over the related pairs, and `rel_map` on
    -- the constructor applied to the witnesses.
    let mut rbs : Array (TSyntax ``bracketedBinderF) := #[]
    let mut elims : Array (TSyntax `tactic) := #[]
    let mut wargs : Array Term := #[]
    let mut ids' : Array Term := #[]
    for g in c.groups do
      if g.kind.isData && g.pk.isNone then
        rbs := rbs.push (← mkBinder g.implicit g.ids g.ty)
        wargs := wargs ++ g.ids.map idT
        ids' := ids' ++ g.ids.map idT
        continue
      rbs := rbs.push (← mkBinder g.implicit g.ids g.ty)
      rbs := rbs.push (← mkBinder g.implicit (g.ids.map prime) (subst dup g.ty))
      for x in g.ids do
        let x' := prime x
        ids' := ids'.push (idT x')
        let h := mkIdent (x.getId.appendAfter "_r")
        let w ← freshId s!"w_{x.getId.toString}"
        wargs := wargs.push (idT w)
        -- Under a telescope: `exists_fn_of_forall` at every binder, the images at the
        -- innermost.
        let underTele (ys : Array Ident) (base : Term) (fstSnd : Option (Term × Term × Term)) :
            CommandElabM Term := do
          let gIn ← mkAppT x (ys.pop.map idT)
          let gIn' ← mkAppT x' (ys.pop.map idT)
          let yIn := ys.back!
          let tm₀ : Term ← if let some (Wj, fs, sn) := fstSnd then
              `(Codata.exists_fn_of_forall (W := fun _ => $Wj) (g := $gIn) (g' := $gIn') $fs $sn
                (fun $yIn:ident => $base))
            else
              `(Codata.exists_fn_of_forall (g := $gIn) (g' := $gIn') _ _ (fun $yIn:ident => $base))
          let mut tm := tm₀
          for k in [1:ys.size] do
            let m := ys.size - 1 - k
            let outer := (ys.extract 0 m).map idT
            let gOut ← mkAppT x outer
            let gOut' ← mkAppT x' outer
            let y := ys[m]!
            tm ← `(Codata.exists_fn_of_forall (g := $gOut) (g' := $gOut') _ _ (fun $y:ident => $tm))
          return tm
        let recEx (idx : Array Term) (hh : Term) : CommandElabM Term := do
          let O ← ctx.recOccOf idx
          `($occEx $O $O $O $hh)
        let (hyp, elim) ← match g.kind, g.pk with
          | .data, .val j =>
            let hyp ← if isFam then `($R $j $x $x') else `($R $x $x')
            let Wj ← if isFam then `({p : $a $j × $a' $j // $R $j p.1 p.2}) else pure W
            let elim ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ :
              ∃ w : $Wj, w.1.1 = $x ∧ w.1.2 = $x' := ⟨⟨($x, $x'), $h⟩, $rflPat, $rflPat⟩)
            pure (hyp, elim)
          | .data, .fn tele j =>
            let tbs ← teleBinders tele
            let ys := teleIds tele
            let ysT := ys.map idT
            let hyp ← if isFam then `(∀ $[$tbs]*, $R $j ($x $ysT*) ($x' $ysT*))
              else `(∀ $[$tbs]*, $R ($x $ysT*) ($x' $ysT*))
            let base ← `(⟨⟨($x $ysT*, $x' $ysT*), $h $ysT*⟩, $rflPat, $rflPat⟩)
            let Wj ← if isFam then `({p : $a $j × $a' $j // $R $j p.1 p.2}) else pure W
            let term ← underTele ys base (some (Wj, ← `(fun _ p => p.1.1), ← `(fun _ p => p.1.2)))
            pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ := $term))
          | .data, .occ info =>
            let o := info.o
            let hyp ← `($occRel $o $o $R $x $x')
            pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ :=
              $occEx $o $o $o $h))
          | .pos idx, _ =>
            let hyp ← `($(← recRel idx) $x $x')
            pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ :=
              $(← recEx idx (idT h))))
          | .fn tele idx, _ =>
            let tbs ← teleBinders tele
            let ys := teleIds tele
            let ysT := ys.map idT
            let hyp ← `(∀ $[$tbs]*, $(← recRel idx) ($x $ysT*) ($x' $ysT*))
            let base ← recEx idx (← `($h $ysT*))
            let term ← underTele ys base none
            pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ := $term))
          | .occ info, _ =>
            let o := info.o
            if info.indexed then
              let hyp ← `(Codata.IOcc.Rel $o $o (fun $pId:ident => $(← recRelP)) $x $x')
              let hh ← freshId "h"
              pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ :=
                Codata.IOcc.exists_map_of_rel' $o $o $o _ _
                  (fun $pId:ident _ _ $hh:ident => $(← recEx pProjs (idT hh))) $h))
            else
              let hyp ← `(Codata.Occ.Rel $o $o $(← recRel info.idx) $x $x')
              let hh ← freshId "h"
              pure (hyp, ← `(tactic| obtain ⟨$w:ident, $rflPat:ident, $rflPat:ident⟩ :=
                Codata.Occ.exists_map_of_rel' $o $o $o _ _
                  (fun _ _ $hh:ident => $(← recEx info.idx (idT hh))) $h))
          | .data, .none => throwError "unreachable: a shared binder"
        rbs := rbs.push (← `(bracketedBinderF| ($h:ident : $hyp)))
        elims := elims.push elim
    let relName := ctx.tName' c "rel_" ""
    let hId : Ident := ⟨(← `(h)).raw⟩
    let capp' ← `(@$(ctx.tCtor c):ident $pTerms₀* $a' $ids'*)
    let cappW ← `(@$(ctx.tCtor c):ident $pTerms₀* $W $wargs*)
    let tail : Array (TSyntax `tactic) := #[
      ← `(tactic| have $hId:ident := $occRelMap $OT $OT $OT $R $fst $snd $cappW $hR),
      ← `(tactic| rwa [$mapName:ident, $mapName:ident] at $hId:ident)]
    let all := elims ++ tail
    elabCommand (← `(theorem $relName:ident $[$pImp₀]* {$a:ident : $aTy} {$a':ident : $aTy'}
        ($R:ident : $RTy) $[$rbs]* :
        $occRel $OT $OT $R $(← ctx.tApp c) $capp' := by $[$all:tactic]*))

/-- `x_ih`, the induction hypothesis for the argument `x`. -/
def ihId (x : Ident) : Ident := mkIdent (x.getId.appendAfter "_ih")

/-- The minor premises of `T.rec`: the constructor's binders, then an induction hypothesis per
recursive argument (`∀ ys, motive _ (k ys)` under a telescope, `∀ q, motive _ ((toC o x).2 q)`
for a nested argument). -/
def recMinors (ctx : Ctx) : CommandElabM (Array (TSyntax ``bracketedBinderF)) := do
  let motive := ctx.motiveId
  ctx.ctors.mapM fun c => do
    let bs ← binders c
    let capp ← ctx.tApp c
    let mc ← appT (idT motive) c.idx
    let mut ihs : Array (TSyntax ``bracketedBinderF) := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos idx =>
        for x in g.ids do
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : $(← appT (idT motive) (idx ++ #[idT x])))))
      | .fn tele idx =>
        let tbs ← teleBinders tele
        let ys := (teleIds tele).map idT
        for x in g.ids do
          let body ← appT (idT motive) (idx ++ #[← `($x $ys*)])
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : ∀ $[$tbs]*, $body)))
      | .occ info =>
        for x in g.ids do
          let toC := occId info.indexed `toC
          let o := info.o
          let idx ← if info.indexed then ctx.projs (← `($(info.pidx) ($toC $o $x).1 q))
            else pure info.idx
          let body ← appT (idT motive) (idx ++ #[← `(($toC $o $x).2 q)])
          ihs := ihs.push (← `(bracketedBinderF| ($(ihId x) : ∀ q, $body)))
    let allBs := bs ++ ihs
    let ty ← if allBs.isEmpty then `($mc $capp) else `(∀ $[$allBs]*, $mc $capp)
    `(bracketedBinderF| ($(c.fname) : $ty))

/-! ### The dependent recursor -/

/-- The recursor with one minor premise per constructor, the `fold` equations on the
constructors, and the computation rules. -/
def genRec (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let pTerms := ctx.pTerms
  let ib ← ctx.ixB
  let jB ← ctx.jB
  let iArg := ctx.iArg
  let motive := ctx.motiveId
  let mTy ← if ctx.idxed then `(∀ $[$jB]*, $(← appT ctx.Tp ctx.jArgs) → Sort _)
    else `($(ctx.Tp) → Sort _)
  let mI ← appT (idT motive) iArg
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Int ← ctx.famT
  let cv ← mkConv ctx
  let pArgs ← ctx.projs (← `(p))
  let minors ← recMinors ctx
  let minorIds := ctx.ctors.map fun c => idT c.fname
  -- `recAux`: the minor premises assembled into the hypothesis of the generic recursor, whose
  -- induction hypotheses are indexed by the positions of `toC`.
  let bId : Ident := ⟨(← `(b)).raw⟩
  let ihId' : Ident := ⟨(← `(ih)).raw⟩
  let idxB ← ctx.projs (← `(Codata.Signature.idx $(ctx.sigp) $bId))
  let mIdxB ← appT (idT motive) idxB
  let ihTy ← `(∀ $bId:ident, $mIdxB ((@$(ctx.toC) $pTerms* $Int $iArg* y).child $bId))
  let auxAlts : Array (TSyntax ``matchAlt) ← ctx.ctors.mapM fun c => do
    let mut ihArgs : Array Term := #[]
    for g in c.groups do
      match g.kind with
      | .data => pure ()
      | .pos _ =>
        for x in g.ids do
          ihArgs := ihArgs.push (← `($ihId' $(← ctx.bApp c x #[])))
      | .fn tele _ =>
        let ys := teleIds tele
        for x in g.ids do
          ihArgs := ihArgs.push
            (← `(fun $[$ys:ident]* => $ihId' $(← ctx.bApp c x (ys.map idT))))
      | .occ .. =>
        for x in g.ids do
          ihArgs := ihArgs.push (← `(fun q => $ihId' $(← ctx.bApp c x #[← `(q)])))
    let rhs ← mkAppT c.fname ((ctx.valArgs c).map idT ++ ihArgs)
    ctx.alt c #[← ctx.fPat c] (← `(fun $ihId':ident => $rhs))
  let discrsY := ctx.discrs (← `(y))
  elabCommand (← `(def $(ctx.recAux):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]*
      (y : $FTi) : $ihTy → $mI ($(ctx.ctor) y) := match $[$discrsY:term],* with $auxAlts:matchAlt*))
  let H ← `(fun p y ih => @$(ctx.recAux) $pTerms* $motive $minorIds* $pArgs* y ih)
  let motiveP ← ctx.uncurryN (idT motive) #[⟨(← `(t)).raw⟩]
  elabCommand (← `(@[elab_as_elim, induction_eliminator]
    def $(ctx.recId):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]* (t : $Ti) : $mI t :=
      $(ctx.sigId `rec_of) (σ := $(ctx.sigp)) (FT := $(cv.FTp)) (motive := $motiveP)
        (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.toC_ofC) $H t))
  -- Its computation rules.
  let recApp (ix : Array Term) (t : Term) : CommandElabM Term :=
    `(@$(ctx.recId) $pTerms* $motive $minorIds* $ix* $t)
  let ihFn ← `(fun $bId:ident =>
    $(← recApp idxB (← `((@$(ctx.toC) $pTerms* $Int $iArg* y).child $bId))))
  elabCommand (← `(theorem $(ctx.rec_ctor):ident $[$pImp]* {$motive : $mTy} $[$minors]* $[$ib]*
      (y : $FTi) : $(← recApp iArg (← `($(ctx.ctor) y))) =
        @$(ctx.recAux) $pTerms* $motive $minorIds* $iArg* y $ihFn :=
    $(ctx.sigId `rec_of_ctor) (σ := $(ctx.sigp)) (FT := $(cv.FTp)) (motive := $motiveP)
      (i := $(cv.pI)) $(cv.toCT) $(cv.ofC) $(cv.toC_ofC) $(cv.ofC_toCT) $H y))
end Codata
