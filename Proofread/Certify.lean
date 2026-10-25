import Proofread.Readable

/-! # Certifying an article

`#proofread_certify Foo "article.tex" using J` collects the justifications in
namespace `J`: `J.definedI : Foo.wellDefinedI` for every definition,
`J.proofK : Foo.obligationK` for the claims to verify and
`J.refuteK : Foo.meaningfulK ∧ ¬ Foo.claimK` for claims shown false. It then

* drops the proofs that use `sorry` (their claims stay unverified, so that an
  article can be certified while its proofs are being written), and the
  proofs of claims that cite a claim which is not verified;
* ranks the verified claims by their premises;
* audits each claim that the text derives (a proof sentence, or a statement
  closed by a compiled proof): its justification may use only Lean's and
  Mathlib's libraries, Proofread, the compiled article and helpers that are
  themselves audited, so a proof sentence cannot be justified by a result the
  sentence does not cite;
* has the kernel check `Foo.certificate : Certificate Foo.model Foo.doc Foo.G …` and
  derives `Foo.verifiedK : Foo.meaningfulK ∧ Foo.claimK` from it;
* writes `<article>.proofread.json`, the per-sentence status for readers and
  editors, and `<article>.proofread.tex`, the status of every labelled result for
  the margin marks of `proofread.sty`. -/
namespace Proofread
open Lean Elab Command Meta

/-- Module roots whose results any justification may use. -/
def permittedRoots : List Name :=
  [`Init, `Std, `Lean, `Mathlib, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
    `ImportGraph, `LeanSearchClient, `Proofread]

/-- Constants from modules outside the permitted ones that `c` uses, following
helpers defined in the justification modules. -/
partial def auditConst (env : Environment) (permitted isLocal : Name → Bool) (c : Name) :
    StateM (NameSet × Array (Name × Name)) Unit := do
  if (← get).1.contains c then return
  modify fun (s, b) => (s.insert c, b)
  match moduleOf env c with
  | some m =>
    if permitted m then return
    if !isLocal m then
      modify fun (s, b) => (s, b.push (c, m))
      return
  | none => pure ()
  match env.find? c with
  | some ci => for d in ci.getUsedConstantsAsSet do auditConst env permitted isLocal d
  | none => pure ()

/-- `(∀ j ∈ premisesOf d k, holds d G j) → holds d G k`, as stated in `Certificate`. -/
def stepType (mE docE gE : Expr) (k : Nat) : MetaM Expr := do
  let pre := mkApp2 (Lean.mkConst ``Doc.premisesOf) docE (mkNatLit k)
  let hyp ← withLocalDeclD `j (Lean.mkConst ``Nat) fun j => do
    let body ← mkArrow (← mkAppM ``Membership.mem #[pre, j]) (mkApp4 (Lean.mkConst ``Doc.holds) mE docE gE j)
    mkForallFVars #[j] body
  mkArrow hyp (mkApp4 (Lean.mkConst ``Doc.holds) mE docE gE (mkNatLit k))

syntax (name := proofreadCertify) "#proofread_certify " ident str " using " ident : command

@[command_elab proofreadCertify] def elabProofreadCertify : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  let jn := stx[4].getId
  checkFresh ns rel
  let d ← nativeDoc ns rel
  let env ← getEnv
  let nm (s : String) : Name := Name.mkSimple s
  -- justifications
  let usesSorry (n : Name) : CommandElabM Bool := do
    pure ((← liftCoreM <| Lean.collectAxioms n).contains ``sorryAx)
  let mut defined : Array Name := #[]
  for i in [0:d.values.length] do
    let n := jn ++ nm s!"defined{i}"
    match env.find? n with
    | some ci =>
      unless ci.type == Lean.mkConst (ns ++ nm s!"wellDefined{i}") do
        throwError "{n} must have type {ns ++ nm s!"wellDefined{i}"}"
      if ← usesSorry n then
        throwError "definition {i} ({defName d i}): its well-definedness proof {n} uses sorry"
      defined := defined.push n
    | none => throwError "definition {i} ({defName d i}) has no well-definedness proof {n}"
  let mut justified : Array (Option Name) := #[]
  let mut notes : Array String := Array.replicate d.claims.length ""
  for k in [0:d.claims.length] do
    let n := jn ++ nm s!"proof{k}"
    match env.find? n with
    | some ci =>
      unless ci.type == Lean.mkConst (ns ++ nm s!"obligation{k}") do
        throwError "{n} must have type {ns ++ nm s!"obligation{k}"}"
      if ← usesSorry n then
        notes := notes.set! k s!"its proof {n} uses sorry"
        justified := justified.push none
      else justified := justified.push (some n)
    | none => justified := justified.push none
  -- refutations: the claim is meaningful and false
  let mut refuted : Array (Option Name) := #[]
  for k in [0:d.claims.length] do
    let n := jn ++ nm s!"refute{k}"
    match env.find? n with
    | some ci =>
      let expected := mkAnd (Lean.mkConst (ns ++ nm s!"meaningful{k}")) (mkNot (Lean.mkConst (ns ++ nm s!"claim{k}")))
      unless ← liftTermElabM (Meta.isDefEq ci.type expected) do
        throwError "{n} must have type {ns ++ nm s!"meaningful{k}"} ∧ ¬ {ns ++ nm s!"claim{k}"}"
      if ← usesSorry n then
        notes := notes.set! k s!"its refutation {n} uses sorry"
        refuted := refuted.push none
      else
        let thm := ns ++ nm s!"refuted{k}"
        liftCoreM <| addDecl <| Declaration.thmDecl
          { name := thm, levelParams := [], type := expected, value := Lean.mkConst n }
        refuted := refuted.push (some thm)
        -- a proof of a refuted claim can only rest on false premises: it does not count
        justified := justified.set! k none
    | none => refuted := refuted.push none
  -- verified claims are closed under premises: a proof of a claim that cites an
  -- unverified one does not count
  let mut dropped := true
  while dropped do
    dropped := false
    for k in [0:d.claims.length] do
      if justified[k]!.isNone then continue
      if let some j := d.claims[k]!.premises.find? (justified[·]!.isNone) then
        justified := justified.set! k none
        notes := notes.set! k s!"it rests on claim {j}, which is {if refuted[j]!.isSome then "refuted" else "not verified"}"
        dropped := true
  for k in [0:d.claims.length] do
    if !notes[k]!.isEmpty then logInfo m!"claim {k} is not verified: {notes[k]!}"
    if refuted[k]!.isSome then logInfo m!"claim {k} is false: {refuted[k]!.get!}"
  -- ranks: the longest chain of premises below a claim (the premise graph must be acyclic)
  let mut rank : Array Nat := Array.replicate d.claims.length 0
  let mut changed := true
  let mut rounds := 0
  while changed do
    changed := false
    rounds := rounds + 1
    if rounds > d.claims.length + 1 then throwError "the premises of the claims form a cycle"
    for k in [0:d.claims.length] do
      let r := d.claims[k]!.premises.foldl (fun m j => max m (rank[j]! + 1)) 0
      if r != rank[k]! then
        rank := rank.set! k r
        changed := true
  let verified := (List.range d.claims.length).filter fun k => justified[k]!.isSome
  -- audit of claims derived in the text
  -- the compiled article, and the modules of its vocabulary and model
  let vocabMod := match env.find? (ns ++ `vocab) with
    | some (.defnInfo v) => v.value.getAppFn.constName?.bind (moduleOf env)
    | _ => none
  let modelMod := match env.find? (ns ++ `model) with
    | some (.defnInfo v) => v.value.getAppFn.constName?.bind (moduleOf env)
    | _ => none
  let articleMods := [moduleOf env (ns ++ `doc), moduleOf env (ns ++ `claim0), vocabMod, modelMod].filterMap id
  let localMods := (justified.toList.filterMap id ++ defined.toList).filterMap (moduleOf env)
  let permitted (m : Name) : Bool := articleMods.contains m || permittedRoots.any (·.isPrefixOf m)
  let isLocal (m : Name) : Bool := localMods.contains m
  let fromText (k : Nat) : Bool :=
    match d.claims[k]!.role with
    | .step _ => true
    | _ => !d.claims[k]!.premises.isEmpty
  for k in verified do
    if fromText k then
      let some n := justified[k]! | continue
      let (_, (_, bad)) := (auditConst env permitted isLocal n).run ({}, #[])
      unless bad.isEmpty do
        let shown := bad.toList.take 5 |>.map fun (c, m) => s!"{c} (from {m})"
        throwError "claim {k} is derived in the text from its citations, but its justification {n} uses {shown}"
  -- the certificate
  let natE := Lean.mkConst ``Nat
  let listNat (xs : List Nat) : Expr := listExpr natE (xs.map mkNatLit)
  let ranks := (List.range d.claims.length).map fun k => rank[k]!
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `verifiedClaims, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) natE,
      value := listNat verified, hints := .abbrev, safety := .safe }
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `claimRanks, levelParams := [], type := mkApp (Lean.mkConst ``List [Level.zero]) natE,
      value := listNat ranks, hints := .abbrev, safety := .safe }
  let docE := Lean.mkConst (ns ++ `doc)
  let gE := Lean.mkConst (ns ++ `G)
  let mE := Lean.mkConst (ns ++ `model)
  let verE := Lean.mkConst (ns ++ `verifiedClaims)
  let rankE := Lean.mkConst (ns ++ `claimRanks)
  kernelRefl (ns ++ `rankedOk) (Lean.mkConst ``Bool) (mkApp3 (Lean.mkConst ``Doc.ranked) docE verE rankE)
    (Lean.mkConst ``Bool.true)
  let conj (ps : List (Expr × Expr)) : Expr :=
    ps.foldr (fun (ty, pf) (accTy, accPf) =>
      (mkAnd ty accTy, mkApp4 (Lean.mkConst ``And.intro) ty accTy pf accPf))
      (Lean.mkConst ``True, Lean.mkConst ``True.intro) |>.2
  let welldefTy (i : Nat) : Expr := mkApp4 (Lean.mkConst ``Doc.welldef) mE docE gE (mkNatLit i)
  let holdsTy (k : Nat) : Expr := mkApp4 (Lean.mkConst ``Doc.holds) mE docE gE (mkNatLit k)
  let defsPfs := (List.range d.values.length).map fun i =>
    (welldefTy i, mkApp4 (Lean.mkConst ``Eq.mpr [Level.zero]) (welldefTy i)
      (Lean.mkConst (ns ++ nm s!"wellDefined{i}")) (Lean.mkConst (ns ++ nm s!"welldef{i}"))
      (Lean.mkConst defined[i]!))
  let mut stepPfs : List (Expr × Expr) := []
  for k in verified do
    let ty ← liftTermElabM <| stepType mE docE gE k
    stepPfs := stepPfs ++ [(ty, mkApp (Lean.mkConst (ns ++ nm s!"obligation{k}_sound"))
      (Lean.mkConst justified[k]!.get!))]
  let certTy := mkApp5 (Lean.mkConst ``Certificate) mE docE gE verE rankE
  let certPf := mkAppN (Lean.mkConst ``Certificate.ofLists)
    #[mE, docE, gE, verE, rankE, mkNatLit d.values.length, Lean.mkConst (ns ++ `definitionCount),
      Lean.mkConst (ns ++ `env), conj defsPfs, Lean.mkConst (ns ++ `rankedOk), conj stepPfs]
  liftCoreM <| addDecl <| Declaration.thmDecl
    { name := ns ++ `certificate, levelParams := [], type := certTy, value := certPf }
  -- every verified claim, as its readable statement
  for k in verified do
    let readable := mkAnd (Lean.mkConst (ns ++ nm s!"meaningful{k}")) (Lean.mkConst (ns ++ nm s!"claim{k}"))
    let mem ← liftTermElabM do
      let e ← mkAppM ``List.elem #[mkNatLit k, verE]
      let rfl ← mkEqRefl (Lean.mkConst ``Bool.true)
      mkAppOptM ``List.mem_of_elem_eq_true #[none, none, none, mkNatLit k, verE,
        some (← mkExpectedTypeHint rfl (← mkEq e (Lean.mkConst ``Bool.true)))]
    let sound := mkAppN (Lean.mkConst ``Certificate.sound) #[mE, docE, gE, verE, rankE,
      Lean.mkConst (ns ++ `certificate), mkNatLit k, mem]
    let pf := mkApp4 (Lean.mkConst ``Eq.mp [Level.zero]) (holdsTy k) readable
      (Lean.mkConst (ns ++ nm s!"holds{k}")) sound
    liftCoreM <| addDecl <| Declaration.thmDecl
      { name := ns ++ nm s!"verified{k}", levelParams := [], type := readable, value := pf }
  -- axioms
  let axs ← liftCoreM <| Lean.collectAxioms (ns ++ `certificate)
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let extra := axs.toList.filter (!standard.contains ·)
  unless extra.isEmpty do throwError "the certificate depends on nonstandard axioms {extra}"
  for r in refuted.toList.filterMap id do
    let extra := (← liftCoreM <| Lean.collectAxioms r).toList.filter (!standard.contains ·)
    unless extra.isEmpty do throwError "the refutation {r} depends on nonstandard axioms {extra}"
  -- report
  let status (k : Nat) : String :=
    if refuted[k]!.isSome then "refuted"
    else if justified[k]!.isNone then "unverified" else if fromText k then "text" else "companion"
  let refutation (k : Nat) : Option Name := refuted[k]!.map fun _ => jn ++ nm s!"refute{k}"
  let infos : Array ClaimInfo := (List.range d.claims.length).toArray.map fun k =>
    { status := status k, rank := rank[k]!,
      justification := ((justified[k]!.orElse fun _ => refutation k).map toString).getD "",
      module := (((justified[k]!.orElse fun _ => refutation k).bind (moduleOf env)).map toString).getD "",
      note := notes[k]! }
  let defInfos := defined.map fun n => (toString n, ((moduleOf env n).map toString).getD "")
  writeReport ns jn rel d infos defInfos verified axs.toList
  let count (st : String) := ((List.range d.claims.length).filter (status · == st)).length
  logInfo m!"{d.claims.length} claims: {count "text"} derived in the text from their citations, \
    {count "companion"} justified by companion proofs, {count "refuted"} refuted, \
    {count "unverified"} unverified; {d.values.length} definitions well defined. Axioms: {axs.toList}"

end Proofread
