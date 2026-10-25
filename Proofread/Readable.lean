import Proofread.Semantics
import Proofread.Report
import Proofread.Tactic

/-! # Readable Lean statements for compiled definitions and claims

`#proofread_semantics Foo "article.tex" with M` names every article definition as
a Lean constant whose value is its denotation written as ordinary Lean, and
states every claim as a proposition `Foo.claimK`. `M` is the model of the
vocabulary the article was compiled with (default `Proofread.Model.empty`).
Each is tied to the compiled document by a theorem proved with `Eq.refl`, so the
kernel checks that the readable form *is* the semantics of the article's text:
`Foo.env` (the definitions), `Foo.holdsK` (claim `K` holds iff `Foo.claimK`),
`Foo.welldefI` (definition `I` is well defined iff `Foo.wellDefinedI`). The
translator is untrusted. -/
namespace Proofread
open Lean Elab Term Meta Command

/-- The Lean type of a term type: `ℝ`, `I`, `Prop`, function types, and the base
types of the model `M`. -/
partial def tyExpr (M : Expr) : Ty → MetaM Expr
  | .real => pure (Lean.mkConst ``Real)
  | .unit => pure (mkApp2 (Lean.mkConst ``Set.Elem [Level.zero]) (Lean.mkConst ``Real) (Lean.mkConst ``unitInterval))
  | .prop => pure (mkSort Level.zero)
  | .fn a b => do mkArrow (← tyExpr M a) (← tyExpr M b)
  | .base k => whnf (mkApp (mkApp (Lean.mkConst ``Model.base) M) (mkNatLit k))

/-- The Lean values of the model's constants, read from its definition. -/
partial def modelConsts (M : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) (fuel : Nat) : MetaM (Array Expr) := do
    if fuel == 0 then return acc
    let e ← whnf e
    if e.isAppOfArity ``List.cons 3 then
      let hd ← whnf (e.getArg! 1)
      let v := if hd.isAppOfArity ``Sigma.mk 4 then hd.getArg! 3 else mkProj ``Sigma 1 hd
      go (e.getArg! 2) (acc.push v.headBeta) (fuel - 1)
    else return acc
  go (mkApp (Lean.mkConst ``Model.consts) M) #[] 100000

def primConst : Prim → Option Name
  | .leb => some ``Prelude.leb
  | .measurableSet1 => some ``Prelude.measurableSet1
  | .measurableSet2 => some ``Prelude.measurableSet2
  | .integrable => some ``Prelude.integrable
  | .hasDerivWithin => some ``Prelude.hasDerivWithin
  | .intervalIntegral => some ``Prelude.intervalIntegral
  | .intervalIntegrable => some ``Prelude.intervalIntegrable
  | .compact2 => some ``Prelude.compact2
  | .convex2 => some ``Prelude.convex2
  | .symm2 => some ``Prelude.symm2
  | .continuousOn => some ``Prelude.continuousOn
  | .concaveOn => some ``Prelude.concaveOn
  | .strictMonoOn => some ``Prelude.strictMonoOn
  | _ => none

def realLit (n : Nat) : TermElabM Expr := do
  let e ← Term.elabTerm (← `(($(Syntax.mkNumLit (toString n)) : ℝ))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The translation context: the model, its constants, and the article's definitions. -/
structure RCtx where
  model : Expr
  consts : Array Expr
  globs : Array Expr

/-- Translate a core term to a readable Lean expression (verified afterwards by `rfl`). -/
partial def readable (R : RCtx) (ls : List Expr) : Tm → TermElabM Expr
  | .glob i => pure (R.globs.getD i (Lean.mkConst `sorryAx))
  | .loc i => pure (ls.getD i (Lean.mkConst `sorryAx))
  | .const i => pure (R.consts.getD i (Lean.mkConst `sorryAx))
  | .prim p => do
    match primConst p with
    | some n => pure (Lean.mkConst n)
    | none =>
      let e := mkApp2 (Lean.mkConst ``Prim.denote) (mkApp (Lean.mkConst ``Model.base) R.model) (toExpr p)
      Meta.reduce e (explicitOnly := false)
  | .app (.app (.prim .rpow) x) y => do mkAppM ``HPow.hPow #[← readable R ls x, ← readable R ls y]
  | .app (.app (.prim .min) x) y => do mkAppM ``Min.min #[← readable R ls x, ← readable R ls y]
  | .app (.app (.prim .max) x) y => do mkAppM ``Max.max #[← readable R ls x, ← readable R ls y]
  | .app (.prim .borel) x => do mkAppM ``Measurable #[← readable R ls x]
  | .app (.prim p) x => do
    match primConst p with
    | some n => pure (mkApp (Lean.mkConst n) (← readable R ls x))
    | none => pure (mkApp (← readable R ls (.prim p)) (← readable R ls x))
  | .app f x => do
    let f' ← readable R ls f
    let x' ← readable R ls x
    pure (mkApp f' x').headBeta
  | .lam t _ b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      mkLambdaFVars #[v] (← readable R (v :: ls) b)
  | .num n => realLit n
  | .ofUnit x => do mkAppM ``Subtype.val #[← readable R ls x]
  | .toUnit x => do
    let x' ← readable R ls x
    let stx ← `(Set.projIcc (0 : ℝ) 1 zero_le_one $(← exprToSyntax x'))
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  | .add x y => do mkAppM ``HAdd.hAdd #[← readable R ls x, ← readable R ls y]
  | .sub x y => do mkAppM ``HSub.hSub #[← readable R ls x, ← readable R ls y]
  | .mul x y => do mkAppM ``HMul.hMul #[← readable R ls x, ← readable R ls y]
  | .div x y => do mkAppM ``HDiv.hDiv #[← readable R ls x, ← readable R ls y]
  | .neg x => do mkAppM ``Neg.neg #[← readable R ls x]
  | .abs x => do mkAppM ``abs #[← readable R ls x]
  | .powNat x n => do mkAppM ``HPow.hPow #[← readable R ls x, mkNatLit n]
  | .cases c v r => do
    let c' ← readable R ls c
    let v' ← readable R ls v
    let r' ← readable R ls r
    let ty ← inferType v'
    pure (mkApp5 (Lean.mkConst ``ite [Level.succ Level.zero]) ty c'
      (mkApp (Lean.mkConst ``Classical.propDecidable) c') v' r')
  | .undef .real => realLit 0
  | .undef .prop => pure (Lean.mkConst ``False)
  | .undef (.fn a b) => do
    withLocalDeclD `x (← tyExpr R.model a) fun v => do
      mkLambdaFVars #[v] (← readable R (v :: ls) (.undef b))
  | .undef t => do
    let e := mkApp3 (Lean.mkConst ``Ty.default) (mkApp (Lean.mkConst ``Model.base) R.model)
      (mkApp (Lean.mkConst ``Model.default) R.model) (toExpr t)
    Meta.reduce e (explicitOnly := false)
  | .eq x y => do mkEq (← readable R ls x) (← readable R ls y)
  | .lt x y => do mkAppM ``LT.lt #[← readable R ls x, ← readable R ls y]
  | .le x y => do mkAppM ``LE.le #[← readable R ls x, ← readable R ls y]
  | .tt => pure (Lean.mkConst ``True)
  | .not p => do pure (mkNot (← readable R ls p))
  | .and p q => do pure (mkAnd (← readable R ls p) (← readable R ls q))
  | .or p q => do pure (mkOr (← readable R ls p) (← readable R ls q))
  | .iff p q => do pure (mkIff (← readable R ls p) (← readable R ls q))
  | .imp p q => do mkArrow (← readable R ls p) (← readable R ls q)
  | .all t b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      mkForallFVars #[v] (← readable R (v :: ls) b)
  | .ex t b => do
    withLocalDeclD `x (← tyExpr R.model t) fun v => do
      let body ← mkLambdaFVars #[v] (← readable R (v :: ls) b)
      mkAppM ``Exists #[body]
  | .integral b => do
    withLocalDeclD `x (← tyExpr R.model .unit) fun v => do
      let f ← mkLambdaFVars #[v] (← readable R (v :: ls) b)
      let stx ← `(MeasureTheory.integral MeasureTheory.MeasureSpace.volume $(← exprToSyntax f))
      let e ← Term.elabTerm stx none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  | .guard _ e => readable R ls e
  | .the t b => do
    let T ← tyExpr R.model t
    let dflt := mkApp3 (Lean.mkConst ``Ty.default) (mkApp (Lean.mkConst ``Model.base) R.model)
      (mkApp (Lean.mkConst ``Model.default) R.model) (toExpr t)
    let inst := mkApp2 (Lean.mkConst ``Nonempty.intro [Level.succ Level.zero]) T dflt
    withLocalDeclD `x T fun v => do
      let p ← mkLambdaFVars #[v] (← readable R (v :: ls) b)
      pure (mkApp3 (Lean.mkConst ``Classical.epsilon [Level.succ Level.zero]) T inst p)

/-- Recompile natively (the literal `Foo.doc` is certified by `Foo.compiled`). -/
def nativeDoc (ns : Name) (rel : String) : CommandElabM Doc := do
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  let V ← liftCoreM <| articleVocab ns
  match compileArticle V lines with
  | some d => pure d
  | none => throwError "the article could not be compiled"

syntax (name := proofreadSemantics) "#proofread_semantics " ident str (" with " ident)? : command

@[command_elab proofreadSemantics] def elabProofreadSemantics : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  let modelName ← match withClause stx[3] with
    | some v => liftCoreM <| realizeGlobalConstNoOverloadWithInfo v
    | none => pure ``Model.empty
  checkFresh ns rel
  let d ← nativeDoc ns rel
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `model, levelParams := [], type := Lean.mkConst ``Model, value := Lean.mkConst modelName,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let M := Lean.mkConst (ns ++ `model)
  let consts ← liftTermElabM <| modelConsts M
  -- definitions as readable constants
  let mut R : RCtx := ⟨M, consts, #[]⟩
  let mut vals : Array Expr := #[]
  let baseE := mkApp (Lean.mkConst ``Model.base) M
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let g := d.globs[i]!
    let name := ns ++ Name.mkSimple (defName d i)
    let (ty, val) ← liftTermElabM do
      let ty ← tyExpr M g.ty
      let val ← readable R [] v
      pure (ty, val)
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name, levelParams := [], type := ty, value := val,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    R := { R with globs := R.globs.push (Lean.mkConst name) }
    vals := vals.push (mkApp4 (Lean.mkConst ``Sigma.mk [Level.zero, Level.zero]) (Lean.mkConst ``Ty)
      (mkApp (Lean.mkConst ``Ty.denote) baseE) (toExpr g.ty) (Lean.mkConst name))
  -- the environment of definition values
  let valTy := mkApp (Lean.mkConst ``Val) baseE
  let gList := listExpr valTy vals.toList
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `G, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) valTy,
      value := gList, hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let docE := Lean.mkConst (ns ++ `doc)
  let gE := Lean.mkConst (ns ++ `G)
  let envLhs := mkApp2 (Lean.mkConst ``Doc.env) M docE
  let envRhs := mkApp2 (Lean.mkConst ``Option.some [Level.zero])
    (mkApp (Lean.mkConst ``List [Level.zero]) valTy) gE
  let envTy := mkApp (Lean.mkConst ``Option [Level.zero]) (mkApp (Lean.mkConst ``List [Level.zero]) valTy)
  kernelRefl (ns ++ `env) envTy envLhs envRhs
  -- well-definedness of each definition
  for i in [0:d.values.length] do
    let v := d.values[i]!
    let p ← liftTermElabM do readable R [] v.defined
    let pn := ns ++ Name.mkSimple s!"wellDefined{i}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := pn, levelParams := [], type := mkSort Level.zero, value := p,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs := mkApp4 (Lean.mkConst ``Doc.welldef) M docE gE (mkNatLit i)
    kernelRefl (ns ++ Name.mkSimple s!"welldef{i}") (mkSort Level.zero) lhs (Lean.mkConst pn)
  -- claims
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let (pd, pc) ← liftTermElabM do
      pure (← readable R [] c.body.defined, ← readable R [] c.body)
    let dn := ns ++ Name.mkSimple s!"meaningful{k}"
    let cn := ns ++ Name.mkSimple s!"claim{k}"
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := dn, levelParams := [], type := mkSort Level.zero, value := pd,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    liftCoreM <| addDecl <| Declaration.defnDecl
      { name := cn, levelParams := [], type := mkSort Level.zero, value := pc,
        hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe }
    let lhs := mkApp4 (Lean.mkConst ``Doc.holds) M docE gE (mkNatLit k)
    kernelRefl (ns ++ Name.mkSimple s!"holds{k}") (mkSort Level.zero) lhs
      (mkAnd (Lean.mkConst dn) (Lean.mkConst cn))
  -- sizes, premises and proof obligations
  let natE := Lean.mkConst ``Nat
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
            Doc.holds $(mkIdent (ns ++ `model)) $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G)) j) →
          Doc.holds $(mkIdent (ns ++ `model)) $(mkIdent (ns ++ `doc)) $(mkIdent (ns ++ `G))
            $(Syntax.mkNumLit (toString k)) := by
        intro h hp
        rw [$(id s!"premises{k}"):ident] at hp
        rw [$(id s!"holds{k}"):ident]
        exact h $args*)
    elabCommand thm
  -- the report before verification, and the sentences that did not compile
  writeReport ns .anonymous rel d #[] #[] [] []
  logUncompiled rel d

end Proofread
