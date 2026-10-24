import Proofread.Semantics
import Proofread.Report
import Proofread.Tactic

/-! # Readable Lean statements for compiled definitions and claims

`#proofread_semantics Foo` names every article definition as a Lean constant whose
value is its denotation written as ordinary Lean, and states every claim as a
proposition `Foo.claimK`. Each is tied to the compiled document by a theorem
proved with `Eq.refl`, so the kernel checks that the readable form *is* the
semantics of the article's text: `Foo.env` (the definitions), `Foo.holdsK`
(claim `K` holds iff `Foo.claimK`), `Foo.welldefI` (definition `I` is well
defined iff `Foo.wellDefinedI`). The translator is untrusted. -/
namespace Proofread
open Lean Elab Term Meta Command

/-- The Lean type of a term type: `ℝ`, `I`, `Prop` and function types. -/
def tyExpr : Ty → MetaM Expr
  | .real => pure (Lean.mkConst ``Real)
  | .unit => pure (mkApp2 (Lean.mkConst ``Set.Elem [Level.zero]) (Lean.mkConst ``Real) (Lean.mkConst ``unitInterval))
  | .prop => pure (mkSort Level.zero)
  | .fn a b => do mkArrow (← tyExpr a) (← tyExpr b)

def primConst : Prim → Option Name
  | .leb => some ``Prelude.leb
  | .distFn2 => some ``Prelude.distFn2
  | .dfUniformMarginals => some ``Prelude.dfUniformMarginals
  | .probMeasure2 => some ``Prelude.probMeasure2
  | .measUniformMarginals => some ``Prelude.measUniformMarginals
  | .measurableSet1 => some ``Prelude.measurableSet1
  | .measurableSet2 => some ``Prelude.measurableSet2
  | .integrable => some ``Prelude.integrable
  | .hasDerivWithin => some ``Prelude.hasDerivWithin
  | _ => none

def realLit (n : Nat) : TermElabM Expr := do
  let e ← Term.elabTerm (← `(($(Syntax.mkNumLit (toString n)) : ℝ))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- Translate a core term to a readable Lean expression (verified afterwards by `rfl`). -/
partial def readable (globs : Array Expr) (ls : List Expr) : Tm → TermElabM Expr
  | .glob i => pure (globs.getD i (Lean.mkConst `sorryAx))
  | .loc i => pure (ls.getD i (Lean.mkConst `sorryAx))
  | .prim p => do
    match primConst p with
    | some n => pure (Lean.mkConst n)
    | none => Meta.reduce (mkApp (Lean.mkConst ``Prim.denote) (toExpr p)) (explicitOnly := false)
  | .app (.app (.prim .rpow) x) y => do mkAppM ``HPow.hPow #[← readable globs ls x, ← readable globs ls y]
  | .app (.app (.prim .min) x) y => do mkAppM ``Min.min #[← readable globs ls x, ← readable globs ls y]
  | .app (.app (.prim .max) x) y => do mkAppM ``Max.max #[← readable globs ls x, ← readable globs ls y]
  | .app (.prim .borel) x => do mkAppM ``Measurable #[← readable globs ls x]
  | .app (.prim p) x => do
    match primConst p with
    | some n => pure (mkApp (Lean.mkConst n) (← readable globs ls x))
    | none => pure (mkApp (← readable globs ls (.prim p)) (← readable globs ls x))
  | .app f x => do
    let f' ← readable globs ls f
    let x' ← readable globs ls x
    pure (mkApp f' x').headBeta
  | .lam t _ b => do
    withLocalDeclD `x (← tyExpr t) fun v => do
      mkLambdaFVars #[v] (← readable globs (v :: ls) b)
  | .num n => realLit n
  | .ofUnit x => do mkAppM ``Subtype.val #[← readable globs ls x]
  | .toUnit x => do
    let x' ← readable globs ls x
    let stx ← `(Set.projIcc (0 : ℝ) 1 zero_le_one $(← exprToSyntax x'))
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .add x y => do mkAppM ``HAdd.hAdd #[← readable globs ls x, ← readable globs ls y]
  | .sub x y => do mkAppM ``HSub.hSub #[← readable globs ls x, ← readable globs ls y]
  | .mul x y => do mkAppM ``HMul.hMul #[← readable globs ls x, ← readable globs ls y]
  | .div x y => do mkAppM ``HDiv.hDiv #[← readable globs ls x, ← readable globs ls y]
  | .neg x => do mkAppM ``Neg.neg #[← readable globs ls x]
  | .abs x => do mkAppM ``abs #[← readable globs ls x]
  | .powNat x n => do mkAppM ``HPow.hPow #[← readable globs ls x, mkNatLit n]
  | .cases c v r => do
    let c' ← readable globs ls c
    let v' ← readable globs ls v
    let r' ← readable globs ls r
    let ty ← inferType v'
    pure (mkApp5 (Lean.mkConst ``ite [Level.succ Level.zero]) ty c'
      (mkApp (Lean.mkConst ``Classical.propDecidable) c') v' r')
  | .undef .real => realLit 0
  | .undef .prop => pure (Lean.mkConst ``False)
  | .undef t => do Meta.reduce (mkApp (Lean.mkConst ``Ty.default) (toExpr t)) (explicitOnly := false)
  | .eq x y => do mkEq (← readable globs ls x) (← readable globs ls y)
  | .lt x y => do mkAppM ``LT.lt #[← readable globs ls x, ← readable globs ls y]
  | .le x y => do mkAppM ``LE.le #[← readable globs ls x, ← readable globs ls y]
  | .tt => pure (Lean.mkConst ``True)
  | .not p => do pure (mkNot (← readable globs ls p))
  | .and p q => do pure (mkAnd (← readable globs ls p) (← readable globs ls q))
  | .or p q => do pure (mkOr (← readable globs ls p) (← readable globs ls q))
  | .iff p q => do pure (mkIff (← readable globs ls p) (← readable globs ls q))
  | .imp p q => do mkArrow (← readable globs ls p) (← readable globs ls q)
  | .all t b => do
    withLocalDeclD `x (← tyExpr t) fun v => do
      mkForallFVars #[v] (← readable globs (v :: ls) b)
  | .ex t b => do
    withLocalDeclD `x (← tyExpr t) fun v => do
      let body ← mkLambdaFVars #[v] (← readable globs (v :: ls) b)
      mkAppM ``Exists #[body]
  | .integral b => do
    withLocalDeclD `x (← tyExpr .unit) fun v => do
      let f ← mkLambdaFVars #[v] (← readable globs (v :: ls) b)
      let stx ← `(MeasureTheory.integral MeasureTheory.MeasureSpace.volume $(← exprToSyntax f))
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  | .guard _ e => readable globs ls e

/-- Recompile natively (the literal `Foo.doc` is certified by `Foo.compiled`). -/
def nativeDoc (rel : String) : CommandElabM Doc := do
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  let src : Packed := lines.map fun l => (l.length, packLine l)
  match compileArticle src with
  | some d => pure d
  | none => throwError "the article could not be compiled"

syntax (name := proofreadSemantics) "#proofread_semantics " ident str : command

@[command_elab proofreadSemantics] def elabProofreadSemantics : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  checkFresh ns rel
  let d ← nativeDoc rel
  -- definitions as readable constants
  let mut globs : Array Expr := #[]
  let mut vals : Array Expr := #[]
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let g := d.globs[i]!
    let name := ns ++ Name.mkSimple (defName d i)
    let (ty, val) ← liftTermElabM do
      let ty ← tyExpr g.ty
      let val ← readable globs [] v
      pure (ty, val)
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name, levelParams := [], type := ty, value := val,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    globs := globs.push (Lean.mkConst name)
    vals := vals.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.zero, Level.zero]) (Lean.mkConst ``Ty)
      (Lean.mkConst ``Ty.denote) (toExpr g.ty) (Lean.mkConst name))
  -- the environment of definition values
  let valTy := Lean.mkConst ``Val
  let gList := listExpr valTy vals.toList
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `G, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) valTy,
      value := gList, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let envLhs ← liftTermElabM do mkAppM ``Doc.env #[Lean.mkConst (ns ++ `doc)]
  let envRhs ← liftTermElabM do mkAppM ``Option.some #[Lean.mkConst (ns ++ `G)]
  let envTy ← liftTermElabM do inferType envLhs
  kernelRefl (ns ++ `env) envTy envLhs envRhs
  -- well-definedness of each definition
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let p ← liftTermElabM do readable globs [] v.defined
    let pn := ns ++ Name.mkSimple s!"wellDefined{i}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := pn, levelParams := [], type := mkSort Level.zero, value := p,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs ← liftTermElabM do mkAppM ``Doc.welldef #[Lean.mkConst (ns ++ `doc), Lean.mkConst (ns ++ `G), mkNatLit i]
    kernelRefl (ns ++ Name.mkSimple s!"welldef{i}") (mkSort Level.zero) lhs (Lean.mkConst pn)
  -- claims
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let (pd, pc) ← liftTermElabM do
      pure (← readable globs [] c.body.defined, ← readable globs [] c.body)
    let dn := ns ++ Name.mkSimple s!"meaningful{k}"
    let cn := ns ++ Name.mkSimple s!"claim{k}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := dn, levelParams := [], type := mkSort Level.zero, value := pd,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := cn, levelParams := [], type := mkSort Level.zero, value := pc,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs ← liftTermElabM do mkAppM ``Doc.holds #[Lean.mkConst (ns ++ `doc), Lean.mkConst (ns ++ `G), mkNatLit k]
    kernelRefl (ns ++ Name.mkSimple s!"holds{k}") (mkSort Level.zero) lhs
      (mkAnd (Lean.mkConst dn) (Lean.mkConst cn))
  -- sizes, premises and proof obligations
  let natE := Lean.mkConst ``Nat
  let docE := Lean.mkConst (ns ++ `doc)
  let lenTy := natE
  kernelRefl (ns ++ `definitionCount) lenTy
    (← liftTermElabM do mkAppM ``List.length #[← mkAppM ``Doc.values #[docE]]) (mkNatLit d.values.length)
  kernelRefl (ns ++ `claimCount) lenTy
    (← liftTermElabM do mkAppM ``List.length #[← mkAppM ``Doc.claims #[docE]]) (mkNatLit d.claims.length)
  let holdsProp (j : Nat) : Expr :=
    mkAnd (Lean.mkConst (ns ++ Name.mkSimple s!"meaningful{j}")) (Lean.mkConst (ns ++ Name.mkSimple s!"claim{j}"))
  for k in [0:d.claims.length] do
    let ps := d.claims[k]!.premises
    let pn := ns ++ Name.mkSimple s!"premises{k}"
    kernelRefl pn (mkApp (Lean.mkConst ``List [Level.zero]) natE)
      (mkApp2 (Lean.mkConst ``Doc.premisesOf) docE (mkNatLit k))
      (listExpr natE (ps.map mkNatLit))
    -- `obligationK`: the cited premises imply the claim (curried, in reading order)
    let ob := ps.foldr (fun j acc => Expr.forallE `h (holdsProp j) acc .default) (holdsProp k)
    let on := ns ++ Name.mkSimple s!"obligation{k}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := on, levelParams := [], type := mkSort Level.zero, value := ob,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let id (n : String) : Ident := mkIdent (ns ++ Name.mkSimple n)
    let args : Array Term ← ps.toArray.mapM fun j => do
      `((Eq.mp $(id s!"holds{j}") (hp $(Syntax.mkNumLit (toString j)) (by simp))))
    let thm ← `(command| theorem $(id s!"obligation{k}_sound") :
        $(id s!"obligation{k}") →
          (∀ j ∈ Doc.premisesOf $(mkIdent (ns ++ `doc)) $(Syntax.mkNumLit (toString k)),
            Doc.holds $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G)) j) →
          Doc.holds $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G)) $(Syntax.mkNumLit (toString k)) := by
        intro h hp
        rw [$(id s!"premises{k}"):ident] at hp
        rw [$(id s!"holds{k}"):ident]
        exact h $args*)
    elabCommand thm
  -- the report before verification, and the sentences that did not compile
  writeReport ns .anonymous rel d #[] #[] [] []
  logUncompiled rel d

end Proofread
