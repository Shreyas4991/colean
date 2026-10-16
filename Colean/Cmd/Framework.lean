import Colean.Cmd.Model

/-!
# The command, step 3: instantiating the framework

*Spec.* Input: `T.contract` and the names in the context. Output: the declarations derived
from the contract alone, by instantiating `Framework.lean`: `T.ctor`, `T.dtor_ctor`,
`T.ctor_dtor`, `T.ctor_injective`, `T.corec_eq`, `T.corec_unique` for codata; `T.dtor`,
`T.dtor_ctor`, `T.ctor_dtor`, `T.ctor_injective`, `T.fold_eq`, `T.fold_unique` for data. Nothing
here looks at the constructor list, only at the curried/packed forms of the contract's fields
(`Conv`), and there are no tactic proofs.
-/

open Lean Elab Command Lean.Parser.Term

namespace Codata

open Ctx

/-- Derived from the coinductive contract. -/
def genDerived (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let Si ← ctx.atI (idT S)
  let cTy ← ctx.famFn (idT S) (← `($(ctx.Fp) $S))
  let cv ← mkConv ctx
  let jIds := ctx.jIds
  let x : Ident := ⟨(← `(x)).raw⟩
  let sId : Ident := ⟨(← `(s)).raw⟩
  let cur (f : Term) (extra : Array Ident) := ctx.curryN f extra
  let Hcur ← `(fun $[$jIds:ident]* x y h =>
    $(← appT (← `(H)) (#[← ctx.pack ctx.jArgs] ++ #[← `(x), ← `(y), ← `(h)])))
  elabCommand (← `(def $(ctx.ctor):ident $[$pImp]* $[$ib]* : $FTi → $Ti :=
    $(ctx.topId `Contract.ctor) $(ctx.contract) (i := $(cv.pI))))
  elabCommand (← `(theorem $(ctx.dtor_ctor):ident $[$pImp]* $[$ib]* (y : $FTi) :
      $(ctx.dtor) ($(ctx.ctor) y) = y :=
    $(ctx.topId `Contract.dtor_ctor) $(ctx.contract) (i := $(cv.pI)) y))
  elabCommand (← `(theorem $(ctx.ctor_dtor):ident $[$pImp]* $[$ib]* (t : $Ti) :
      $(ctx.ctor) ($(ctx.dtor) t) = t :=
    $(ctx.topId `Contract.ctor_dtor) $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.ctor_injective):ident $[$pImp]* $[$ib]* :
      Function.Injective ($(ctx.ctor) : $FTi → $Ti) :=
    $(ctx.topId `Contract.ctor_injective) $(ctx.contract) (i := $(cv.pI))))
  -- `corec_eq` and `corec_unique`, for states in any universe.
  let corecFn ← if ctx.k == 0 then `($(ctx.corec) c)
    else `(fun $[$(← ctx.holes)]* s => $(ctx.corec) c s)
  let cs ← appT (← `(c)) (iArgs ++ #[← `(s)])
  elabCommand (← `(theorem $(ctx.corec_eq):ident $[$pImp]* {$S : $xTy} (c : $cTy) $[$ib]*
      (s : $Si) : $(ctx.corec) c s = $(ctx.ctor) ($(ctx.Fmap) $corecFn $cs) :=
    $(ctx.topId `corec_eq_of) (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp)) (FT := $(cv.FTp))
      (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t) (fun {_} y => $(ctx.ctor) y)
      (fun c {_} s => $(ctx.corec) $(← cur (← `(c)) #[sId]) s) $(cv.map)
      (fun c {_} s => $(ctx.dtor_corec) $(← cur (← `(c)) #[sId]) s) (fun {_} t => $(ctx.ctor_dtor) t)
      $(cv.c) s))
  let hTy ← ctx.famFn (idT S) ctx.Tp
  let ixBExp ← ctx.ixBExp
  let hs ← appT (← `(h)) (iArgs ++ #[← `(s)])
  let hhTy ← `(∀ $[$ixBExp]* (s : $Si), $(ctx.dtor) $hs = $(ctx.Fmap) h $cs)
  elabCommand (← `(theorem $(ctx.corec_unique):ident $[$pImp]* {$S : $xTy} (c : $cTy) (h : $hTy)
      (hh : $hhTy) $[$ib]* (s : $Si) : $hs = $(ctx.corec) c s :=
    $(ctx.topId `corec_unique_of) (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (FT := $(cv.FTp)) (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t)
      (fun c {_} s => $(ctx.corec) $(← cur (← `(c)) #[sId]) s) $(cv.map) $(cv.Rel)
      (fun R H {_ _ _} h => $(ctx.bisim) $(← cur (← `(R)) #[]) $Hcur h)
      (fun c {_} s => $(ctx.dtor_corec) $(← cur (← `(c)) #[sId]) s)
      (fun R f g {_} a h => $(ctx.Frel_map) $(← cur (← `(R)) #[]) $(← cur (← `(f)) #[])
        $(← cur (← `(g)) #[]) a $(← cur (← `(h)) #[x]))
      $(cv.c) $(← ctx.uncurryN (← `(h)) #[sId]) $(← ctx.uncurryN (← `(hh)) #[sId]) s))


/-- Derived from the inductive contract. -/
def genDataDerived (ctx : Ctx) : CommandElabM Unit := do
  let pImp := ctx.pImp
  let xTy ← ctx.famTy
  let ib ← ctx.ixB
  let ixBExp ← ctx.ixBExp
  let iArgs := ctx.iArgs
  let S := ctx.Sid
  let Ti ← ctx.atI ctx.Tp
  let FTi ← ctx.atI (← `($(ctx.Fp) $(ctx.Tp)))
  let aTy ← ctx.famFn (← `($(ctx.Fp) $S)) (idT S)
  let cv ← mkConv ctx
  let pArgs ← ctx.projs (← `(p))
  let x : Ident := ⟨(← `(x)).raw⟩
  let z : Ident := ⟨(← `(z)).raw⟩
  let t : Ident := ⟨(← `(t)).raw⟩
  let y : Ident := ⟨(← `(y)).raw⟩
  -- The contract, at the packed index; each field converts a curried piece.
  let Fpk ← if ctx.packed then
      `(fun (X : $(ctx.Ixp) → Type _) (p : $(ctx.Ixp)) =>
        $(← appT (← `($(ctx.Fp) $(← ctx.curryFam (← `(X))))) pArgs))
    else pure ctx.Fp
  let cur (f : Term) (extra : Array Ident) := ctx.curryN f extra
  let mapP ← `(fun {_ _} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
  elabCommand (← `(def $(ctx.dtor):ident $[$pImp]* $[$ib]* (t : $Ti) : $FTi :=
    Data.Contract.dtor $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.dtor_ctor):ident $[$pImp]* $[$ib]* (y : $FTi) :
      $(ctx.dtor) ($(ctx.ctor) y) = y :=
    Data.Contract.dtor_ctor $(ctx.contract) (i := $(cv.pI)) y))
  elabCommand (← `(theorem $(ctx.ctor_dtor):ident $[$pImp]* $[$ib]* (t : $Ti) :
      $(ctx.ctor) ($(ctx.dtor) t) = t :=
    Data.Contract.ctor_dtor $(ctx.contract) (i := $(cv.pI)) t))
  elabCommand (← `(theorem $(ctx.ctor_injective):ident $[$pImp]* $[$ib]* :
      Function.Injective ($(ctx.ctor) : $FTi → $Ti) :=
    Data.Contract.ctor_injective $(ctx.contract) (i := $(cv.pI))))
  -- `fold_eq` and `fold_unique`, for families in any universe.
  let foldFn ← if ctx.k == 0 then `($(ctx.fold) a)
    else `(fun $[$(← ctx.holes)]* t => $(ctx.fold) a t)
  let adt ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) $foldFn ($(ctx.dtor) t))])
  elabCommand (← `(theorem $(ctx.fold_eq):ident $[$pImp]* {$S : $xTy} (a : $aTy) $[$ib]*
      (t : $Ti) : $(ctx.fold) a t = $adt :=
    Data.fold_eq_of (T := $(cv.Tpk)) (S := $(cv.Sp)) (FS := $(cv.FSp)) (FT := $(cv.FTp))
      (i := $(cv.pI)) (fun {_} t => $(ctx.dtor) t) (fun {_} y => $(ctx.ctor) y)
      (fun a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t) $(cv.map)
      (fun a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y) (fun {_} t => $(ctx.ctor_dtor) t)
      $(← ctx.uncurryN (← `(a)) #[z]) t))
  let hTy ← ctx.famFn ctx.Tp (idT S)
  let hy ← appT (← `(h)) (iArgs ++ #[← `($(ctx.ctor) y)])
  let ahy ← appT (← `(a)) (iArgs ++ #[← `($(ctx.Fmap) h y)])
  let hhTy ← `(∀ $[$ixBExp]* (y : $FTi), $hy = $ahy)
  let ht ← appT (← `(h)) (iArgs ++ #[← `(t)])
  elabCommand (← `(theorem $(ctx.fold_unique):ident $[$pImp]* {$S : $xTy} (a : $aTy) (h : $hTy)
      (hh : $hhTy) $[$ib]* (t : $Ti) : $ht = $(ctx.fold) a t :=
    Data.fold_unique_of (T := $(cv.Tpk)) (F := $Fpk) (S := $(cv.Sp)) (FS := $(cv.FSp))
      (i := $(cv.pI)) $mapP (fun {_} y => $(ctx.ctor) y) (Data.Contract.induction $(ctx.contract))
      (fun a {_} t => $(ctx.fold) $(← cur (← `(a)) #[z]) t)
      (fun {_} f {_} a => $(ctx.Fmap) $(← cur (← `(f)) #[x]) a)
      (fun a {_} y => $(ctx.fold_ctor) $(← cur (← `(a)) #[z]) y)
      (fun {_} g f {_} z => $(ctx.Fmap_comp) $(← cur (← `(g)) #[]) $(← cur (← `(f)) #[]) z)
      $(← ctx.uncurryN (← `(a)) #[z]) $(← ctx.uncurryN (← `(h)) #[t])
      $(← ctx.uncurryN (← `(hh)) #[y]) t))

end Codata
