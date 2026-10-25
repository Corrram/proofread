import Proofread.Elab

/-! # Compiling an article

`compileArticle` reads the complete source: preamble macros, the document body,
its sentences and environments. Every sentence is either compiled (definitions
and claims) or kept as prose with the reason it has no reading. A sentence is
compiled entirely or not at all. Citations become premises: a proof sentence may
use earlier sentences of its proof and the results cited so far in that proof.
A result whose proof compiled completely has the proof's sentences (and their
citations) as its premises: this is the closing step of the proof. -/
namespace Proofread
open Grammar Elab

structure ProofInfo where
  env : Nat
  proves : Codes
  steps : List Nat
  cites : List Nat
  complete : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Doc where
  globs : List Glob
  values : List Tm
  claims : List Claim
  sentences : List (Context × Nat × Nat)
  outcomes : List Outcome
  labels : List (Codes × List Nat)
  proofs : List ProofInfo
  /-- Names of definitions introduced by phrases rather than symbols. -/
  names : List (List Codes × Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Compile


def intervalPred (lo hi : Tm) : Tm := .lam .real .tt (Elab.interval lo hi (.loc 0))

/-- A closed constant bound (numerals and their negations). -/
def constTm : MT → Option Tm
  | .num n => some (.num n)
  | .neg (.num n) => some (.neg (.num n))
  | .frac (.num a) (.num b) => some (.div (.num a) (.num b))
  | _ => none

def isUnitSquare : Option MT → Bool
  | some (.sup (.interval (.num 0) (.num 1)) (.num 2)) => true
  | _ => false

def isUnitInterval : Option MT → Bool
  | some (.interval (.num 0) (.num 1)) => true
  | _ => false

def isPair : Option MT → Option (MT × MT)
  | some (.tuple [a, b]) => some (a, b)
  | _ => none

def wordsOf (cs : List Chunk) : List Codes := cs.filterMap fun c => match c with | .w w => some w | _ => none
def mathsOf (cs : List Chunk) : List (List MTok) := cs.filterMap fun c => match c with | .m t => some t | _ => none

def lookupWords (tbl : List (List Codes × Nat)) (ws : List Codes) : Option Nat := tbl.lookup ws

/-! ## Noun phrases

A noun phrase is read compositionally: prenominal modifiers of the vocabulary,
a head noun (a vocabulary noun, a class the article defined, or a variable with a
signature `$f:A\to B$`), at most one variable (possibly with a membership
`$C\in\CC$`), and postnominal modifiers of the vocabulary. Its meaning is the
conjunction of the predicates of its parts. Every chunk must be read. -/

/-- The name of a variable chunk: a letter or a command (`\gamma`). -/
def varName : List MTok → Option Codes
  | [.id v] => some v
  | [.cmd c] => some ([92] ++ c)
  | _ => none

/-- Match a vocabulary phrase at the start of `cs`. The variable slot matches a
variable chunk (returned) or nothing. -/
def matchPhrase : Phrase → List Chunk → Option (Option (List MTok) × List Chunk)
  | [], cs => some (none, cs)
  | .w w :: ps, .w v :: cs => if v == w then matchPhrase ps cs else none
  | .m t :: ps, .m u :: cs => if t == u then matchPhrase ps cs else none
  | .v :: ps, .m u :: cs =>
    -- a variable (with or without membership) fills the slot
    match matchPhrase ps cs with
    | some (none, r) => some (some u, r)
    | _ => matchPhrase ps (.m u :: cs)
  | .v :: ps, cs => matchPhrase ps cs
  | _, _ => none

/-- Words of a noun, matched against the article's noun table (longest first). -/
def matchWords (tbl : List (List Codes × Nat)) (cs : List Chunk) : Option (Nat × List Chunk) :=
  let ws := cs.takeWhile (fun c => match c with | .w _ => true | _ => false)
  let words := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
  let rec go : Nat → Option (Nat × List Chunk)
    | 0 => none
    | k + 1 =>
      match tbl.lookup (words.take (k + 1)) with
      | some i => some (i, cs.drop (k + 1))
      | none => go k
  go words.length

def conjPreds (ty : Ty) : List Tm → Option Tm
  | [] => none
  | [p] => some p
  | ps => some (.lam ty .tt (Elab.conjAll (ps.map fun p => Tm.app p (.loc 0))))

/-- An endpoint of an interval domain: a numeral, or a closed term (`g_*`). -/
def closedBound (m : MT) : M Tm := do
  match constTm m with
  | some t => pure t
  | none => match Elab.constMT m with
    | some t => pure t
    | none => do
      let (t, ty) ← Elab.term 100000 [] none m
      coerce t ty .real

/-- The type and predicate of a domain formula (`[0,1]`, `[-1,1]`, `\CC`). -/
def domainOf (calculus : Bool) (d : MT) : M (Ty × Option Tm) := do
  if isZeroOne d && !calculus then pure (.unit, none)
  else match d with
    | .interval lo hi => do
      let l ← closedBound lo
      let h ← closedBound hi
      pure (.real, some (intervalPred l h))
    | .ival lo hi lopen ropen => do
      let l ← closedBound lo
      let h ← closedBound hi
      pure (.real, some (.lam .real .tt (Elab.intervalTm l h lopen ropen (.loc 0))))
    | .tuple [lo, hi] => do
      let l ← liftO (Elab.constMT lo) E.unsupported
      let h ← liftO (Elab.constMT hi) E.unsupported
      pure (.real, some (.lam .real .tt (Elab.intervalTm l h true true (.loc 0))))
    | .id n => do
      -- the real numbers
      if n == w!"\\mathbb{R}" then pure (.real, none) else
      let (i, g) ← liftO (← lookupGlob n) E.undefined n
      match g.ty with
      | .fn a .prop => pure (a, some (.glob i))
      | _ => fail E.type n
    | _ => fail E.unsupported

/-- A variable chunk: its name, and the domain of a membership `$x\in A$`. -/
def varChunk (ts : List MTok) : M (Codes × Option (Ty × Option Tm)) := do
  match varName ts with
  | some v => pure (v, none)
  | none =>
    match Grammar.binderMath ts with
    | some ([v], dom) => do pure (v, some (← domainOf false dom))
    | _ => fail E.unsupported

/-- Read a noun phrase (without its determiner). -/
def nounPhrase (np : List Chunk) : M BindInfo := do
  let st ← get
  let V := st.vocab
  -- prenominal modifiers
  let rec pre : Nat → List Chunk → List Modifier → List Modifier × List Chunk
    | 0, cs, acc => (acc.reverse, cs)
    | f + 1, cs, acc =>
      match V.mods.findSome? (fun m => if m.prenominal then
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none) with
      | some (m, r) => pre f r (m :: acc)
      | none => (acc.reverse, cs)
  let (pms, r0) := pre 4 np []
  -- the head: an article class, a vocabulary noun, or a variable with a signature
  -- (the article's own classes take precedence over the vocabulary's nouns)
  let head : M (Ty × List Tm × Option (List MTok) × List Chunk) := do
    match matchWords st.nouns r0 with
    | some (i, r) => do
      let gty : Option Ty := (st.globs[i]?).map (·.ty)
      let a ← match gty with
        | some (.fn a .prop) => pure a
        | _ => fail E.type
      match r with
      | .m ts :: r' =>
        if (Math.parseSig ts).isSome then fail E.unsupported else pure (a, [.glob i], some ts, r')
      | _ => pure (a, [.glob i], none, r)
    | none =>
      match V.nouns.findSome? (fun n =>
          ((matchPhrase n.sing r0) <|> (matchPhrase n.plural r0)).map fun (v, r) => (n, v, r)) with
      | some (n, v, r) =>
        match v, r with
        -- `a copula $C$`: the variable follows a noun without a slot
        | none, .m ts :: r' =>
          if (Math.parseSig ts).isSome || !(n.sing.all fun p => p != .v) then pure (n.ty, [n.pred], v, r)
          else pure (n.ty, [n.pred], some ts, r')
        | _, _ => pure (n.ty, [n.pred], v, r)
      | none =>
        -- `$f:A\to B$`, optionally after the noun `map` or `function`
        let r1 := match r0 with
          | .w w :: r => if w == w!"map" || w == w!"function" || w == w!"maps" || w == w!"functions" then r else r0
          | _ => r0
        match r1 with
        | .m ts :: r => do
          let sg ← liftO (Math.parseSig ts) E.noun ((wordsOf np).flatten)
          match sg with
          | .sig (.id f) d c => do
            let (dt, dp) ← domainOf false d
            let (ct, cp) ← domainOf false c
            if dp.isSome || cp.isSome then fail E.unsupported
            pure (.fn dt ct, [], some [.id f], r)
          | _ => fail E.unsupported
        | _ => fail E.noun ((wordsOf np).flatten)
  let (ty, preds, var, r1) ← head
  for m in pms do
    if m.ty != ty then fail E.type
  -- postnominal modifiers
  let rec post : Nat → List Chunk → List Tm → M (List Tm × List Chunk)
    | 0, cs, acc => pure (acc.reverse, cs)
    | f + 1, cs, acc =>
      match V.mods.findSome? (fun m => if !m.prenominal && m.ty == ty then
          (matchPhrase m.phrase cs).bind fun (v, r) => if v.isNone then some (m, r) else none
        else none) with
      | some (m, r) => post f r (m.pred :: acc)
      | none => pure (acc.reverse, cs)
  let (qms, r2) ← post 4 r1 []
  if !r2.isEmpty then fail E.noun ((wordsOf np).flatten)
  let (name, member) ← match var with
    | some ts => do let (v, d) ← varChunk ts; pure (v, d)
    | none => pure ([], none)
  let memberPred ← match member with
    | some (t, p) => if t == ty then pure p.toList else fail E.type
    | none => pure []
  let all := (preds ++ pms.map (·.pred) ++ qms ++ memberPred).eraseDups
  pure ⟨name, ty, conjPreds ty all⟩

/-- Free identifiers of a formula (for `On I,`). -/
def freeIds : Nat → List Codes → MT → List Codes
  | 0, _, _ => []
  | f + 1, bound, m =>
    match m with
    | .id n => if bound.contains n || n == [42] then [] else [n]
    | .num _ => []
    -- the base of `e_b` is a symbol, not a variable
    | .sub (.id _) i => freeIds f bound i
    | .sub b i => freeIds f bound b ++ freeIds f bound i
    | .sup b e => freeIds f bound b ++ freeIds f bound e
    | .hat x | .neg x | .abs x => freeIds f bound x
    | .app h as => freeIds f bound h ++ (as.flatMap (freeIds f bound))
    | .add x y | .minus x y | .mul x y | .div x y | .frac x y => freeIds f bound x ++ freeIds f bound y
    | .minm xs | .maxm xs | .tuple xs | .conj xs => xs.flatMap (freeIds f bound)
    | .int _ _ b v => freeIds f (v :: bound) b
    | .interval a b => freeIds f bound a ++ freeIds f bound b
    | .chain x rs => freeIds f bound x ++ rs.flatMap (fun r => freeIds f bound r.2)
    | .mapsto p b => freeIds f (freeIds f [] p ++ bound) b
    | _ => []

def binderInfos : Bind → M (List BindInfo)
  | .every vs d => do
    let (ty, p) ← domainOf false d
    pure (vs.map fun v => ⟨v, ty, p⟩)
  | .noun np => do pure [← nounPhrase np]
  | .on _ => pure []
  | .ifCond φ => do
    -- the free variables of φ range over ℝ; φ is the domain of the last one
    let st ← get
    let free := ((freeIds 64 [] φ).filter fun n => !(st.globs.any fun g => g.key == n && !g.family)).eraseDups
    match free.reverse with
    | [] => fail E.unsupported
    | last :: _ =>
      let sc : Scope := free.reverse.map (·, Ty.real)
      let (p, pty) ← Elab.term 100000 sc none φ
      if pty != .prop then fail E.type
      pure (free.map fun v => (⟨v, .real, if v == last then some (.lam .real .tt p) else none⟩ : BindInfo))
  | .many bs => do
    let mut out := []
    for b in bs do
      match b with
      | .every vs d => do
        let (ty, p) ← domainOf false d
        out := out ++ vs.map fun v => ⟨v, ty, p⟩
      | _ => fail E.unsupported
    pure out

def scopeOf (bs : List BindInfo) : Scope := (bs.map fun b => (b.name, b.ty)).reverse

def wrap (bs : List BindInfo) (body : Tm) : Tm :=
  forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body

def clauseMaths : Clause → List MT
  | .fact f | .holds f => [f]
  | .deriv d _ c => [d, c]
  | .scoped f _ _ e => f :: e.toList
  | .everyNP _ b => [b]
  | .extremumOf _ v f _ a _ => v :: f.toList ++ a.toList
  | .increasing ms => ms
  | .ranges _ b => [b]
  | .extremaOver items f _ _ cond => items.map (·.2) ++ [f, cond]
  | .increases f a b => [f, a, b]
  | .sends m f g => [m, f, g]
  | .every _ d b => [d, b]
  | .equalityOn s => [s]
  | .equalityWhen φ => [φ]
  | .ifThen c cl => c :: clauseMaths cl
  | .adjectives s _ => [s]
  | _ => []

/-- The two sides `(smaller, larger)` of a single inequality. -/
def ineqSides : MT → Option (MT × MT)
  | .chain a [(r, b)] =>
    if r == .le || r == .lt then some (a, b)
    else if r == .ge || r == .gt then some (b, a)
    else none
  | _ => none

/-- The inequalities a claim about every element of a domain asserts: the formula, both
sides of `φ, equivalently ψ`, or the parts of a list. -/
def boundsOf : MT → List MT
  | .equiv x y => [x, y].filter (ineqSides · |>.isSome)
  | .conj xs => xs.filter (ineqSides · |>.isSome)
  | m => if (ineqSides m).isSome then [m] else []

/-- Does the clause speak about the latest inequality (`equality holds …`)? -/
def usesIneq : Clause → Bool
  | .equalityOn _ | .equalityWhen _ => true
  | .ifThen _ cl => usesIneq cl
  | _ => false

/-- The free variables of the latest inequality that a clause refers to. -/
def ineqFree (st : St) (cl : Clause) : List Codes :=
  if usesIneq cl then
    match st.lastIneq with
    | some (bs, m) => freeIds 64 (bs.map (·.name)) m
    | none => []
  else []

/-- A piecewise formula that no piece covers is `0` there (for integrands). -/
def zeroElsewhere : Tm → Tm
  | .cases c v rest => .cases c v (zeroElsewhere rest)
  | .undef .real => .num 0
  | t => t

/-- The single inequality of a chain, for `with equality only at`. -/
def inequality : MT → Option MT
  | .chain x rs =>
    let terms := x :: rs.map (·.2)
    let idx := rs.findIdx? (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)
    match idx with
    | some k =>
      if (rs.filter (fun r => r.1 == .le || r.1 == .lt || r.1 == .ge || r.1 == .gt)).length == 1 then
        match terms[k]?, terms[k+1]? with
        | some a, some b => some (.chain a [(.eq, b)])
        | _, _ => none
      else none
    | none => none
  | _ => none

/-- Record the binders and inequalities of a claim about every element of a domain. -/
def recordBounds (bs : List BindInfo) (body : MT) : M Unit := do
  let ms := boundsOf body
  if !ms.isEmpty then modify fun st => { st with lastBounds := some (bs, ms) }
  if (inequality body).isSome then modify fun st => { st with lastIneq := some (bs, body) }

def F := 100000

def prop (sc : Scope) (pf : PF) (m : MT) : M Tm := do
  let (t, ty) ← term F sc pf m
  if ty == .prop then pure t else fail E.type

/-- The domain (type, predicate) of a point-free function formula such as `\nu-\rho`. -/
def pfDomain : Nat → MT → M (Option (Ty × Option Tm))
  | 0, _ => pure none
  | f + 1, m =>
    match m with
    | .id n => do
      match ← lookupGlob n with
      | some (_, g) => match g.ty with
        | .fn a _ => pure (some (a, (g.doms.head?).join))
        | _ => pure none
      | none => pure none
    | .minus x y | .add x y | .mul x y | .div x y => do
      match ← pfDomain f x with
      | some r => pure (some r)
      | none => pfDomain f y
    | .neg x => pfDomain f x
    | _ => pure none

def holdsAt (p : Option Tm) (x : Tm) : Tm := match p with | some p => .app p x | none => .tt

/-- A map `v ↦ body` used only on the points of a domain: its definedness
condition asks for the body only there. -/
def onDomain (p : Option Tm) : Tm → Tm
  | .lam t _ b => .lam t (holdsAt p (.loc 0)) b
  | t => t

/-- Resolve a relation object: a formula, or a named object (possibly introduced here). -/
def object (sc : Scope) (ty : Ty) : Obj → M Tm
  | .math (.mapsto pat body) => do
    match ty with
    | .fn a r => do let (t, _) ← Elab.lam F sc pat [a] (some r) body; pure t
    | _ => fail E.type
  | .math m => do let (t, mty) ← term F sc none m; coerce t mty ty
  | .named name none => do
    let some i := lookupWords (← get).named name | fail E.referent name.flatten
    pure (.glob i)
  | .named name (some (.mapsto pat body)) => do
    match ty with
    | .fn a r => do
      let (t, tty) ← Elab.lam F [] pat [a] (some r) body
      let i ← addGlob ⟨[], tty, [], false⟩ t
      modify fun st => { st with named := st.named ++ [(name, i)] }
      pure (.glob i)
    | _ => fail E.type
  | _ => fail E.unsupported

def predicate (sc : Scope) (s : Tm × Ty) (phrase : List Codes) (o : Obj) : M Tm := do
  let some i := lookupWords (← get).preds phrase | fail E.noun phrase.flatten
  let g := ((← get).globs[i]?).getD default
  match g.ty with
  | .fn _ (.fn b .prop) => do
    let ot ← object sc b o
    let (t, _) ← applyAll (.glob i) g.ty g.doms [s, (ot, b)]
    pure t
  | _ => fail E.type

def subjectTm (sc : Scope) : Subj → M (Tm × Ty)
  | .math m => term F sc none m
  | .its name => do
    let some (s, sty) := (← get).subject | fail E.referent
    let some i := lookupWords (← get).ops name | fail E.noun name.flatten
    let g := ((← get).globs[i]?).getD default
    applyAll (.glob i) g.ty g.doms [(s, sty)]

/-- Extremum statement: bound, attainment, uniqueness. -/
def extremumTm (sc : Scope) (isMax : Bool) (fm value : MT) (s : Tm × Ty) : M (Tm × Ty × Option Tm) := do
  let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) fm)
  let mx ← asReal (← term F inner none value)
  let bound := Tm.all ty (.imp (holdsAt p (.loc 0)) (if isMax then .le fx mx else .le mx fx))
  let fs ← asReal (← term F sc (some (s', ty)) fm)
  let ms ← asReal (← term F sc none value)
  let attained := Tm.and (holdsAt p s') (.eq fs ms)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  pure (.and bound (.and attained unique), ty, p)

def attainsOnly (sc : Scope) (ex : Extremum) (s : Tm × Ty) (withAttained : Bool) : M Tm := do
  let some (ty, p) ← pfDomain 16 ex.f | fail E.unsupported
  let s' ← coerce s.1 s.2 ty
  let inner := (w!"", ty) :: sc
  let fx ← asReal (← term F inner (some (.loc 0, ty)) ex.f)
  let mx ← asReal (← term F inner none ex.value)
  let unique := Tm.all ty (.imp (holdsAt p (.loc 0)) (.imp (.eq fx mx) (.eq (.loc 0) (shift 1 0 s'))))
  if withAttained then
    let fs ← asReal (← term F sc (some (s', ty)) ex.f)
    let ms ← asReal (← term F sc none ex.value)
    pure (.and (.and (holdsAt p s') (.eq fs ms)) unique)
  else pure unique

def findExtremum (env : Nat) (isMax : Bool) : M Extremum := do
  let st ← get
  match st.extrema.find? (fun (e, x) => e == env && x.isMax == isMax) with
  | some (_, x) => pure x
  | none => fail E.referent

structure SentCtx where
  ctx : Context
  /-- Environment index of the result a proof proves. -/
  target : Nat
  idx : Nat

def claimRole (c : SentCtx) : Role :=
  match c.ctx.kind with
  | .result _ => .statement c.ctx.env
  | .proof => .step c.ctx.env
  | .text => .text

/-- Premise claim ids for citing a label (definitions contribute none). -/
def citeClaims (l : Codes) : M (List Nat) := do
  let st ← get
  match st.labels.lookup l with
  | some cs => pure cs
  | none => if st.defLabels.contains l then pure [] else fail E.label l

def addLabels (ls : List Codes) (claims : List Nat) (isDef : Bool) : M Unit := do
  for l in ls do
    modify fun st =>
      let st := if isDef then { st with defLabels := st.defLabels ++ [l] } else st
      match st.labels.lookup l with
      | some cs => { st with labels := st.labels.map fun (k, v) => if k == l then (k, cs ++ claims) else (k, v) }
      | none => { st with labels := st.labels ++ [(l, claims)] }

/-- Record a claim of the current sentence (with premises for proof steps). -/
def emit (c : SentCtx) (body : Tm) (cites : List Codes) : M Nat := do
  let st ← get
  match c.ctx.kind with
  | .proof => do
    let cited ← cites.mapM citeClaims
    let allCites := (st.proofCites ++ cited.flatten).eraseDups
    let premises := (allCites ++ st.proofSteps).eraseDups
    let id ← addClaim ⟨c.idx, body, .step c.ctx.env, cites, premises⟩
    modify fun st => { st with proofCites := allCites, proofSteps := st.proofSteps ++ [id] }
    pure id
  | _ => do
    discard <| cites.mapM citeClaims
    addClaim ⟨c.idx, body, claimRole c, cites, []⟩

/-! ## Definition sentences -/

/-- Registered operation names: the name as written, and without a final `of`. -/
def registerOp (name : List Codes) (i : Nat) : M Unit := do
  let base := match name.reverse with
    | w :: r => if w == w!"of" then r.reverse else name
    | [] => name
  let names := [name, base].eraseDups.filter (!·.isEmpty)
  modify fun st => { st with ops := st.ops ++ names.map (·, i) }

/-- The head of a defining left-hand side: the defined key, whether it is a
family, and its explicit arguments. -/
def defHead (binder : Codes) : MT → M (Codes × Bool × List Codes)
  | .app h args => do
    let names ← args.mapM fun a => match a with | .id n => pure n | _ => fail E.unsupported
    match h with
    | .id k => if names == [binder] then pure (k, false, []) else fail E.unsupported k
    | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, names) else fail E.unsupported
    | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, names) else fail E.unsupported
    | .sub (.id k) (.id x) => if x == binder then pure (k, true, names) else fail E.unsupported
    | _ => fail E.unsupported
  | .sup (.id x) (.id d) => if x == binder then pure (w!"^" ++ d, false, []) else fail E.unsupported
  | .hat (.id x) => if x == binder then pure (w!"\\widehat", false, []) else fail E.unsupported
  | .sub (.id k) (.id x) => if x == binder then pure (k, true, []) else fail E.unsupported
  | _ => fail E.unsupported

def argTypes : Ty → Nat → List Ty
  | _, 0 => []
  | .fn a b, n + 1 => a :: argTypes b n
  | _, _ => []

def lamWrap : List Ty → Tm → Tm
  | [], b => b
  | t :: ts, b => .lam t .tt (lamWrap ts b)

def tyWrap : List Ty → Ty → Ty
  | [], r => r
  | t :: ts, r => .fn t (tyWrap ts r)

/-- Claims `a₁ R₁ a₂ R₂ …` after a definition `X := a₁`, pairwise, under binders. -/
def chainClaims (sc : Scope) (first : MT) (rest : List (Rel × MT)) : M (List Tm) := do
  let rec go : MT → List (Rel × MT) → M (List Tm)
    | _, [] => pure []
    | a, (r, b) :: more => do
      let ta ← term F sc none a
      let tb ← term F sc none b
      let p ← relTm r ta tb
      pure (p :: (← go b more))
  go first rest

/-- `For a N $x$, the NAME is DEF`. -/
def defItem (c : SentCtx) (b : BindInfo) (it : DefItem) : M (List Nat × List Nat) := do
  let bty := b.ty
  match it.defn with
  | .chain lhs ((.defeq, rhs) :: more) => do
    let (key, family, args) ← defHead b.name lhs
    let ats := match bty with
      | .fn _ _ => argTypes bty args.length
      | _ => []
    if ats.length != args.length then fail E.type
    let sc := ((args.zip ats).reverse) ++ [(b.name, bty)]
    let (body, rty) ← term F sc none rhs
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) (lamWrap ats body)
    let ty := Ty.fn bty (tyWrap ats rty)
    let i ← addGlob ⟨key, ty, b.pred :: ats.map (fun _ => none), family⟩ value
    registerOp it.name i
    let cs ← chainClaims sc rhs more
    let bs := b :: (args.zip ats).map fun (n, t) => ⟨n, t, none⟩
    let ids ← cs.mapM fun p => emit c (wrap bs p) []
    addLabels it.labels ids true
    pure ([i], ids)
  | .mapsto pat body => do
    -- an operation named by its noun, e.g. `the copula associated with γ`
    let nouns := (← get).nouns
    let some ni := it.name.findSome? (fun w => nouns.lookup [w]) | fail E.noun
    let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
    let elemTy ← match gty with
      | some (.fn a .prop) => pure a
      | _ => fail E.type
    let ats := argTypes elemTy (match pat with | .tuple vs => vs.length | _ => 1)
    let (lt, lty) ← Elab.lam F [(b.name, bty)] pat ats (some .real) body
    let value := Tm.lam bty (holdsAt b.pred (.loc 0)) lt
    let i ← addGlob ⟨[], .fn bty lty, [b.pred], false⟩ value
    registerOp it.name i
    pure ([i], [])
  | _ => fail E.unsupported

/-- One branch of a piecewise definition of `f`, in the scope of its argument `x`:
the condition under which it applies and its value. A parametric piece also
defines its parameter family (the `where` part). -/
def defBranch (f : Codes) (aty cty : Ty) : DefPiece → M (Tm × Tm)
  -- f(x) := rhs [, x ∈ D]
  | .formula (.chain (.app (.id f') [.id x]) [(.defeq, rhs)]) => do
    if f != f' then fail E.unsupported
    let (v, vty) ← term F [(x, aty)] none rhs
    pure (.tt, ← coerce v vty cty)
  | .formula (.conj [.chain (.app (.id f') [.id x]) [(.defeq, rhs)], .chain (.id x') [(.mem, d)]]) => do
    if f != f' || x != x' then fail E.unsupported
    let (v, vty) ← term F [(x, aty)] none rhs
    let cnd ← Elab.term.member F [(x, aty)] (.loc 0, aty) d
    pure (cnd, ← coerce v vty cty)
  -- f(c) := v for a constant c
  | .formula (.chain (.app (.id f') [a]) [(.defeq, rhs)]) => do
    if f != f' then fail E.unsupported
    let some at_ := Elab.constMT a | fail E.unsupported
    let (v, vty) ← term F [] none rhs
    let v ← coerce v vty cty
    let xr ← coerce (.loc 0) aty .real
    pure (.eq xr at_, shift 1 0 v)
  -- on D, parametrically by f(e_b) := g(b), b ∈ P, where e_b := h(b) [, b ∈ P']
  | .param d (.conj items) => do
    match items with
    | .chain (.app (.id f') [.sub (.id e) (.id b)]) [(.defeq, g)] :: .chain (.id b1) [(.mem, pdom)] ::
        .text wh :: .chain (.sub (.id e') (.id b2)) [(.defeq, h)] :: rest => do
      if f != f' || e != e' || b != b1 || b != b2 || wh != w!"where" then fail E.unsupported
      let edom ← match rest with
        | [] => pure pdom
        | [.chain (.id b3) [(.mem, d2)]] => if b3 == b then pure d2 else fail E.unsupported
        | _ => fail E.unsupported
      -- the family e_b on its domain
      let (_, epred) ← domainOf true edom
      let (hv, hty) ← term F [(b, .real)] none h
      let hv ← coerce hv hty .real
      let ie ← addGlob ⟨e, .fn .real .real, [epred], true⟩ (.lam .real (holdsAt epred (.loc 0)) hv)
      -- the value at x: the y with x = e_b and y = g(b) for some b ∈ P
      let (_, ppred) ← domainOf true pdom
      let sc : Scope := [(b, .real), (w!"", cty), (w!"", aty)]
      let (gv, gty) ← term F sc none g
      let gv ← coerce gv gty cty
      let eb := Tm.guard (holdsAt epred (.loc 0)) (.app (.glob ie) (.loc 0))
      let xr ← coerce (.loc 2) aty .real
      let body := Tm.ex .real (Elab.conjAll [holdsAt ppred (.loc 0), .eq eb xr, .eq (.loc 1) gv])
      let cnd ← Elab.term.member F [(w!"", aty)] (.loc 0, aty) d
      pure (cnd, .the cty body)
    | _ => fail E.unsupported
  | _ => fail E.unsupported

/-- `define $f:A\to B$ by PIECES [and observe that φ for every x∈A]`: `f` is the
function on `A` given by its pieces (point values, formulas on subdomains and
parametric pieces), each applying where its condition holds; it is defined only
where some piece applies. Its values lie in `B` (a claim). -/
def defBy (c : SentCtx) (sg : MT) (pieces : List DefPiece) (labels : List Codes)
    (observe : Option (MT × List Codes × MT)) : M (List Nat × List Nat) := do
  match sg with
  | .sig (.id f) dom cod => do
    let (aty, apred) ← domainOf true dom
    let (cty, cpred) ← domainOf true cod
    let start := (← get).globs.length
    let body ← match pieces with
      | [.formula (.chain (.app (.id f') [.id x]) [(.defeq, rhs)])] => do
        if f != f' then fail E.unsupported
        let (body, bty) ← term F [(x, aty)] none rhs
        coerce body bty cty
      | _ => do
        let bs ← pieces.mapM (defBranch f aty cty)
        pure (bs.foldr (fun (cnd, v) acc => Tm.cases cnd v acc) (.undef cty))
    let value := Tm.lam aty (holdsAt apred (.loc 0)) body
    let i ← addGlob ⟨f, .fn aty cty, [apred], false⟩ value
    let applied := Tm.guard (holdsAt apred (.loc 0)) (.app (.glob i) (.loc 0))
    let codomain := match cpred with
      | some p => [Tm.all aty (.imp (holdsAt apred (.loc 0)) (.app p applied))]
      | none => []
    let ids ← codomain.mapM fun p => emit c p []
    let obs ← match observe with
      | some (φ, vs, d) => do
        let bs ← binderInfos (.every vs d)
        let p ← prop (scopeOf bs) none φ
        pure [← emit c (wrap bs p) []]
      | none => pure []
    addLabels labels (ids ++ obs) true
    pure ((List.range (i + 1 - start)).map (· + start), ids ++ obs)
  | _ => fail E.unsupported

/-- `For B, the NAME $f_c:A\to B$ reads DISPLAY`. -/
def defReads (c : SentCtx) (b : BindInfo) (sg disp : MT) (labels : List Codes) : M (List Nat × List Nat) := do
  match sg, disp with
  | .sig (.sub (.id f) (.id p)) dom cod, .chain (.app (.sub (.id f') (.id p')) [.id x]) ((.defeq, rhs) :: more) => do
    if f != f' || p != b.name || p' != b.name then fail E.unsupported
    let (aty, apred) ← domainOf false dom
    let (cty, cpred) ← domainOf false cod
    if cpred.isSome then fail E.unsupported
    let sc : Scope := [(x, aty), (b.name, b.ty)]
    let (body, bty) ← term F sc none rhs
    let body' ← coerce body bty cty
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (.lam aty (holdsAt apred (.loc 0)) body')
    let i ← addGlob ⟨f, .fn b.ty (.fn aty cty), [b.pred, apred], true⟩ value
    let cs ← chainClaims sc rhs more
    let ids ← cs.mapM fun q => emit c (wrap [b, ⟨x, aty, apred⟩] q) []
    addLabels labels ids true
    pure ([i], ids)
  | _, _ => fail E.unsupported

/-- `NAME is denoted by $S$`: binds the symbol `S` to a named notion of the
vocabulary (`Lebesgue measure on $[0,1]$`). -/
def denotedBy (name : List Chunk) (sym : MT) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  let V := (← get).vocab
  match V.notions.find? (fun n => match matchPhrase n.name name with
      | some (none, []) => true
      | _ => false) with
  | some n => do
    let i ← addGlob ⟨key, n.ty, [], false⟩ n.value
    pure ([i], [])
  | none => fail E.noun (wordsOf name).flatten

/-- `For B, set $X_p\coloneqq e [\in D]$` or `$f(p)\coloneqq e$`. -/
def setDefSimple (c : SentCtx) (b : BindInfo) (m : MT) : M (List Nat × List Nat) := do
  match m with
  | .chain lhs ((.defeq, rhs) :: more) => do
    let (key, family) ← match lhs with
      | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else fail E.unsupported
      -- `f(x)\coloneqq e`: a function of the binder's variable
      | .app (.id k) [.id p] => if p == b.name then pure (k, false) else fail E.unsupported
      | _ => fail E.unsupported
    let sc : Scope := [(b.name, b.ty)]
    let (v, vty) ← term F sc none rhs
    let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family⟩ (.lam b.ty (holdsAt b.pred (.loc 0)) v)
    let x : Tm × Ty := (.guard (holdsAt b.pred (.loc 0)) (.app (.glob i) (.loc 0)), vty)
    let ps ← more.mapM fun (r, y) => do
      if r == .mem then Elab.term.member F sc x y
      else do relTm r x (← term F sc none y)
    let ids ← ps.mapM fun p => emit c (wrap [b] p) []
    pure ([i], ids)
  | _ => fail E.unsupported

/-- `For B, set $X_p\coloneqq e [\in D]$`: a family on the binder's domain, and the
claims of the rest of the chain. -/
def setDef (c : SentCtx) (b : BindInfo) (m : MT) : M (List Nat × List Nat) := do
  match m with
  -- `f_p(x,…)\coloneqq e`, `R_p^-(z)\coloneqq e`: a family with further real
  -- arguments; `z_-(x)\coloneqq e`, `c\coloneqq e`: a symbol that does not show `p`,
  -- whose implicit parameter `p` is supplied from the scope at each use
  | .chain lhs ((.defeq, rhs) :: more) =>
    let (hd, args) := match lhs with
      | .app h as => (h, as)
      | _ => (lhs, [])
    let names := args.filterMap fun a => match a with | .id n => some n | _ => none
    let simple := match lhs with
      | .sub (.id _) (.id p) => p == b.name
      | .app (.id _) [.id p] => p == b.name
      | _ => false
    if simple || names.length != args.length || names.contains b.name then setDefSimple c b m else do
    let (key, family) ← match hd with
      | .sub (.id k) (.id p) =>
        if p == b.name then pure (k, true) else
        match Elab.symKey hd with | some k' => pure (k', false) | none => fail E.unsupported
      | .sup (.sub (.id k) (.id p)) (.id s) => if p == b.name then pure (k ++ w!"^" ++ s, true) else fail E.unsupported
      | .id k => pure (k, false)
      | _ => match Elab.symKey hd with | some k' => pure (k', false) | none => fail E.unsupported
    if !more.isEmpty && !args.isEmpty then fail E.unsupported
    let ats := names.map fun _ => Ty.real
    let sc : Scope := (names.zip ats).reverse ++ [(b.name, b.ty)]
    let (v, vty) ← term F sc none rhs
    let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) (lamWrap ats v)
    let i ← addGlob ⟨key, .fn b.ty (tyWrap ats vty), b.pred :: ats.map (fun _ => none), family⟩ value
    if !family then modify fun st => { st with implicits := st.implicits ++ [(i, b.name)] }
    let x : Tm × Ty := (.guard (holdsAt b.pred (.loc 0)) (.app (.glob i) (.loc 0)), vty)
    let sc1 : Scope := [(b.name, b.ty)]
    let ps ← more.mapM fun (r, y) => do
      if r == .mem then Elab.term.member F sc1 x y
      else do relTm r x (← term F sc1 none y)
    let ids ← ps.mapM fun p => emit c (wrap [b] p) []
    pure ([i], ids)
  | _ => fail E.unsupported

/-- The fixed variable (`fix $b\in B$` earlier in the section) that the subscript of a
definition's symbol names, as in `Set $R_b^-(z)\coloneqq …$`. -/
def fixedFor (c : SentCtx) (m : MT) : M (Option BindInfo) := do
  let lhs := match m with | .chain l _ => l | _ => m
  let hd := match lhs with | .app h _ => h | h => h
  let v := match hd with
    | .sub (.id _) (.id p) => some p
    | .sup (.sub (.id _) (.id p)) _ => some p
    | _ => none
  match v with
  | some p => pure (((← get).fixed.find? fun (s, b) => s == c.ctx.sec && b.name == p).map (·.2))
  | none => pure none

/-- `Set $d_0\coloneqq e$.`: constants, with the claims of the rest of each chain;
under a binder, families and functions of the binder's variable (`setDef`). -/
def constDefs (c : SentCtx) (b : Option BindInfo) (defs : List MT) (labels : List Codes) :
    M (List Nat × List Nat) := do
  let mut ds : List Nat := []
  let mut cs : List Nat := []
  for m in defs do
    match b with
    | some bi =>
      let (d', c') ← setDef c bi m
      ds := ds ++ d'
      cs := cs ++ c'
    | none =>
      match ← fixedFor c m with
      | some fb => do
        let (d', c') ← setDef c fb m
        ds := ds ++ d'
        cs := cs ++ c'
      | none =>
      match m with
      | .chain lhs ((.defeq, rhs) :: more) => do
        let some key := symKey lhs | fail E.unsupported
        let (v, vty) ← term F [] none rhs
        let i ← addGlob ⟨key, vty, [], false⟩ v
        let x : Tm × Ty := (.glob i, vty)
        let ps ← more.mapM fun (r, y) => do
          if r == .mem then Elab.term.member F [] x y
          else do relTm r x (← term F [] none y)
        let ids ← ps.mapM fun p => emit c p []
        ds := ds ++ [i]
        cs := cs ++ ids
      | _ => fail E.unsupported
  addLabels labels cs true
  pure (ds, cs)

/-- `define continuous functions $f,g:A\to\R$ by $f(a)=c$, …, and DISPLAY` with
`f'(x) = …` in the display: `f(x) = c + ∫_a^x f'(t)\,dt` for `x ∈ A` (defined when the
derivative is integrable between `a` and `x`). Where no piece of a piecewise
derivative applies (at finitely many points), the integrand is `0`, which does not
change the integral. Under a binder `p`, `f_p` is a family. -/
def defDeriv (bi : Option BindInfo) (names : List MT) (dom cod : MT) (anchors : List MT)
    (derivs : MT) (labels : List Codes) : M (List Nat × List Nat) := do
  let (aty, apred) ← domainOf true dom
  let (cty, _) ← domainOf true cod
  if aty != .real || cty != .real then fail E.unsupported
  let rows := match derivs with | .conj xs => xs | m => [m]
  let sc0 : Scope := match bi with | some b => [(b.name, b.ty)] | none => []
  let mut ids : List Nat := []
  for n in names do
    let some nk := Elab.symKey n | fail E.unsupported
    let (key, family) ← match n, bi with
      | .sub (.id k) (.id p), some b => if p == b.name then pure (k, true) else fail E.unsupported
      | .id k, none => pure (k, false)
      | _, _ => fail E.unsupported
    -- the value at one point
    let some (a, cv) := anchors.findSome? (fun an => match an with
        | .chain (.app h [a]) [(.eq, cv)] => if Elab.symKey h == some nk then some (a, cv) else none
        | _ => none)
      | fail E.referent nk
    -- the derivative
    let some (x, g) := rows.findSome? (fun r => match r with
        | .chain (.app (.sup h (.id d)) [.id x]) [(.eq, g)] =>
          if d == [39] && Elab.symKey h == some nk then some (x, g) else none
        | _ => none)
      | fail E.referent nk
    let at_ ← asReal (← term F sc0 none a)
    let ct ← asReal (← term F sc0 none cv)
    let gt ← asReal (← term F ((x, .real) :: (w!"", .real) :: sc0) none g)
    let gl := Tm.lam .real .tt (zeroElsewhere gt)
    let a1 := shift 1 0 at_
    let integral := Tm.app (.app (.app (.prim .intervalIntegral) a1) (.loc 0)) gl
    let integrable := Tm.app (.app (.app (.prim .intervalIntegrable) gl) a1) (.loc 0)
    let body := Tm.add (shift 1 0 ct) (.guard integrable integral)
    let fx := Tm.lam .real (holdsAt apred (.loc 0)) body
    let (g, v) : Glob × Tm := match bi with
      | some b => (⟨key, .fn b.ty (.fn .real .real), [b.pred, apred], family⟩, Tm.lam b.ty (holdsAt b.pred (.loc 0)) fx)
      | none => (⟨key, .fn .real .real, [apred], family⟩, fx)
    let i ← addGlob g v
    ids := ids ++ [i]
  addLabels labels [] true
  pure (ids.eraseDups, [])

/-- `For B, let $X_p$ denote NP`. -/
def letDenote (b : BindInfo) (sym : MT) (np : List Chunk) : M (List Nat × List Nat) := do
  let (key, family) ← match sym with
    | .sub (.id k) (.id p) => if p == b.name then pure (k, true) else fail E.unsupported
    -- `\gamma^T`: a family written with a superscript
    | .sup (.id k) (.id p) => if p == b.name then pure (k ++ w!"^", true) else fail E.unsupported
    | .id k => pure (k, false)
    | _ => fail E.unsupported
  let sc : Scope := [(b.name, b.ty)]
  let (val, vty) ← match np with
    -- the law of $(X, f(X))$ for $X$ uniformly distributed on $[0,1]$
    | [.w t, .w l, .w o, .m pair, .w fr, .m [.id x], .w u, .w d, .w on, .m zo] =>
      if [t, l, o, fr, u, d, on] == [w!"the", w!"law", w!"of", w!"for", w!"uniformly", w!"distributed", w!"on"]
          && isUnitInterval (Math.parseFormula zo) then do
        match Math.parseFormula pair with
        | some (.tuple [e1, e2]) => do
          -- λ A. Leb {x : A(e1(x), e2(x))}, with A a measurable subset of [0,1]^2
          let sc' := (x, Ty.unit) :: (w!"", Ty.set2) :: sc
          let a ← coerce (← term F sc' none e1).1 .unit .unit
          let t1 ← term F sc' none e1
          let t2 ← term F sc' none e2
          let a1 ← coerce t1.1 t1.2 .unit
          let a2 ← coerce t2.1 t2.2 .unit
          let _ := a
          let set := Tm.lam .unit .tt (.app (.app (.loc 1) a1) a2)
          let body := Tm.guard (.app (.prim .measurableSet1) set) (.app (.prim .leb) set)
          pure (Tm.lam Ty.set2 (.app (.prim .measurableSet2) (.loc 0)) body, Ty.meas2)
        | _ => fail E.unsupported
      else fail E.noun
    | .w t :: rest =>
      if t != w!"the" then fail E.unsupported
      else do
        let ws := wordsOf rest
        match mathsOf rest with
        | [arg] => do
          let some i := lookupWords (← get).ops ws | fail E.noun ws.flatten
          let g := ((← get).globs[i]?).getD default
          let m ← liftO (Math.parseFormula arg) E.unsupported
          let a ← term F sc none m
          applyAll (.glob i) g.ty g.doms [a]
        | _ => fail E.unsupported
    | _ => fail E.unsupported
  let value := Tm.lam b.ty (holdsAt b.pred (.loc 0)) val
  let i ← addGlob ⟨key, .fn b.ty vty, [b.pred], family⟩ value
  pure ([i], [])

/-- `We say that a N $x$ is PHRASE of a M $y$ if φ for all u,v∈A`. -/
def weSay (subj : List Chunk) (phrase : List Codes) (o : List Chunk) (cond : MT) (vs : List Codes) (d : MT) :
    M (List Nat × List Nat) := do
  let s ← nounPhrase subj
  let t ← nounPhrase o
  let bs ← binderInfos (.every vs d)
  let sc := scopeOf ([s, t] ++ bs)
  let body ← prop sc none cond
  let inner := forallBinders (bs.map fun b => (b.name, b.ty, b.pred.map fun p => Tm.app p (.loc 0))) body
  let value := Tm.lam s.ty (holdsAt s.pred (.loc 0)) (.lam t.ty (holdsAt t.pred (.loc 0)) inner)
  let i ← addGlob ⟨[], .fn s.ty (.fn t.ty .prop), [s.pred, t.pred], false⟩ value
  modify fun st => { st with preds := st.preds ++ [(phrase, i)] }
  pure ([i], [])

/-- `let $S$ denote the class of Ns, that is, NP`: `S` is the class described by
the noun phrase `NP`, and `N` (singular) names it. -/
def defClass (sym : MT) (plural : List Codes) (np : List Chunk) : M (List Nat × List Nat) := do
  let key ← match sym with | .id k => pure k | _ => fail E.unsupported
  -- without `that is, NP`, the class is a noun of the vocabulary
  let b ← nounPhrase (if np.isEmpty then plural.map Chunk.w else np)
  if !b.name.isEmpty then fail E.unsupported b.name
  let p := b.pred.getD (.lam b.ty .tt .tt)
  let i ← addGlob ⟨key, .fn b.ty .prop, [none], false⟩ p
  let sing := plural.dropLast ++ (plural.getLast?.map singular).toList
  let names := [sing, (sing.getLast?).toList].eraseDups
  modify fun st => { st with nouns := st.nouns ++ names.map (·, i), classes := st.classes ++ [(plural, i)] }
  pure ([i], [])

/-! ## Claim sentences -/

/-- One clause; `rest` are the following clauses of the sentence (for scopes). -/
def clauseTm (c : SentCtx) (sc : Scope) (onVar : Option BindInfo) (lastRhs : Option MT) :
    Clause → M Tm
  | .fact f | .holds f => prop sc none f
  | .extremaOver items f noun v cond => do
    -- the class: the noun as written, or its singular
    let sing := noun.dropLast ++ (noun.getLast?.map singular).toList
    let nouns := (← get).nouns
    let some ni := (lookupWords nouns noun).orElse (fun _ => lookupWords nouns sing)
      | fail E.noun noun.flatten
    let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
    let ty ← match gty with
      | some (.fn a .prop) => pure a
      | _ => fail E.type
    let p := Tm.glob ni
    -- `F` and `φ` about one element (`loc 0`), and about a second one (`loc 0`, the first `loc 1`)
    let sx := (v, ty) :: sc
    let fx ← asReal (← term F sx none f)
    let cx ← prop sx none cond
    let sy := (v, ty) :: (w!"", ty) :: sc
    let fy ← asReal (← term F sy none f)
    let cy ← prop sy none cond
    let parts ← items.mapM fun (isMax, x) => do
      let xv ← asReal (← term F sc none x)
      let x1 := shift 1 0 xv
      let x2 := shift 2 0 xv
      let bound := Tm.all ty (.imp (.app p (.loc 0)) (.imp cx (if isMax then .le fx x1 else .le x1 fx)))
      let uniq := Tm.all ty (.imp (.app p (.loc 0)) (.imp cy (.imp (.eq fy x2) (.eq (.loc 0) (.loc 1)))))
      pure (Tm.and bound (.ex ty (Elab.conjAll [.app p (.loc 0), cx, .eq fx x1, uniq])))
    pure (Elab.conjAll parts)
  | .every vs d body => do
    let bs ← binderInfos (.every vs d)
    let p ← prop (scopeOf bs ++ sc) none body
    recordBounds bs body
    pure (wrap bs p)
  | .scoped f vs d eq => do
    let bs ← match d with
      | some d => binderInfos (.every vs d)
      | none => pure []
    let sc' := scopeOf bs ++ sc
    let p ← prop sc' none f
    if !bs.isEmpty && (inequality f).isSome then modify fun st => { st with lastIneq := some (bs, f) }
    let p ← match eq with
      | some at_ => do
        let ineq ← liftO (inequality f) E.unsupported
        let e ← prop sc' none ineq
        let a ← prop sc' none at_
        pure (Tm.and p (.imp e a))
      | none => pure p
    pure (wrap bs p)
  | .extremum isMax fv s rels => do
    match fv with
    | .chain fm [(.eq, value)] => do
      let st ← subjectTm sc s
      let (core, ty, _) ← extremumTm sc isMax fm value st
      let s' ← coerce st.1 st.2 ty
      let extra ← rels.mapM fun r => match r with
        | .has m => prop sc (some (s', ty)) m
        | .pred ph o => predicate sc (s', ty) ph o
      modify fun st' => { st' with
        extrema := st'.extrema ++ [(c.ctx.env, ⟨isMax, fm, value⟩)], subject := some (s', ty) }
      pure (conjAll (core :: extra))
    | _ => fail E.unsupported
  | .increases (.mapsto pat body) a b => do
    let (aty, apred) ← domainOf false a
    let (bty, bpred) ← domainOf false b
    if bty != .real then fail E.unsupported
    let (fn, _) ← Elab.lam F sc pat [aty] (some .real) body
    let fn := onDomain apred fn
    let fx : Tm := .app (shift 1 0 fn) (.loc 0)
    let into := Tm.all aty (Tm.mkImp (holdsAt apred (.loc 0)) (holdsAt bpred fx))
    let fxx : Tm := .app (shift 2 0 fn) (.loc 1)
    let fyy : Tm := .app (shift 2 0 fn) (.loc 0)
    let ltA : Tm := if aty == .unit then .lt (.ofUnit (.loc 1)) (.ofUnit (.loc 0)) else .lt (.loc 1) (.loc 0)
    let mono := Tm.all aty (.all aty (Tm.mkImp (holdsAt apred (.loc 1)) (Tm.mkImp (holdsAt apred (.loc 0))
      (.imp ltA (.lt fxx fyy)))))
    let onto := Tm.all .real (Tm.mkImp (holdsAt bpred (.loc 0)) (.ex aty (Tm.mkAnd (holdsAt apred (.loc 0))
      (.eq (.app (shift 2 0 fn) (.loc 0)) (.loc 1)))))
    pure (conjAll [into, mono, onto])
  | .deriv d positive cond => do
    let some v := onVar | fail E.referent
    let some rhs := lastRhs | fail E.referent
    let some ip := v.pred | fail E.unsupported
    let (g, _) ← Elab.lam F sc (.id v.name) [.real] (some .real) rhs
    let g := match g with | .lam t _ b => Tm.lam t (.app ip (.loc 0)) b | g => g
    let dt ← asReal (← term F sc none d)
    let ct ← prop sc none cond
    let hd := Tm.app (.app (.app (.app (.prim .hasDerivWithin) g) ip) (.loc 0)) dt
    let sign := if positive then Tm.lt (.num 0) dt else Tm.lt dt (.num 0)
    pure (.and hd (.imp ct sign))
  | .noOther noun x isMax => do
    let ex ← findExtremum c.target isMax
    let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
    let xt ← term F sc none x
    let u ← attainsOnly sc ex xt false
    match u with
    | .all ty (.imp p rest) =>
      if p == .app (.glob ni) (.loc 0) then pure u
      else pure (.all ty (.imp (.and (.app (.glob ni) (.loc 0)) p) rest))
    | u => pure u
  | .onlyAttains x => do
    let isMax ← match (← get).topic with
      | .maximum => pure true | .minimum => pure false | .none => fail E.referent
    let ex ← findExtremum c.target isMax
    let xt ← term F sc none x
    attainsOnly sc ex xt true
  | .sends (.mapsto (.id v) body) fm gm => do
    let some (ty, p) ← pfDomain 16 fm | fail E.unsupported
    let sc' := (v, ty) :: sc
    let (mt, mty) ← term F sc' none body
    let mt ← coerce mt mty ty
    let lhs ← asReal (← term F sc' (some (mt, ty)) fm)
    let rhs ← asReal (← term F sc' (some (.loc 0, ty)) gm)
    pure (.all ty (.imp (holdsAt p (.loc 0)) (.eq lhs rhs)))
  | .pred s ph o => do
    let st ← subjectTm sc s
    predicate sc st ph o
  | .onlyWith s noun conds => do
    let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
    let (st, sty) ← subjectTm sc s
    let atS ← conds.mapM (prop sc (some (st, sty)))
    let sc' := (w!"", sty) :: sc
    let ay ← conds.mapM (prop sc' (some (.loc 0, sty)))
    let uniq := Tm.all sty (.imp (.app (.glob ni) (.loc 0)) (.imp (conjAll ay) (.eq (.loc 0) (shift 1 0 st))))
    pure (conjAll ([Tm.app (.glob ni) st] ++ atS ++ [uniq]))
  | .everyNP np body => do
    let mb := match np with
      | [.m ts] => Grammar.binderMath ts
      | _ => none
    match mb with
    | some (vs, d) => do
      -- `every $(x,z)\in[0,1]^2$ satisfies φ`
      let bs ← binderInfos (.every vs d)
      let p ← prop (scopeOf bs ++ sc) none body
      recordBounds bs body
      pure (wrap bs p)
    | none => do
      let b ← nounPhrase np
      if b.name.isEmpty then fail E.unsupported
      let p ← prop ((b.name, b.ty) :: sc) none body
      recordBounds [b] body
      pure (wrap [b] p)
  | .sharp => do
    let some (bs, ms) := (← get).lastBounds | fail E.referent
    let k := bs.length
    -- for every ε > 0 (`loc k` under the binders), some element has `larger - smaller < ε`
    let sc' := scopeOf bs ++ (w!"", .real) :: sc
    let parts ← ms.mapM fun m => do
      let some (a, b) := ineqSides m | fail E.unsupported
      let at_ ← asReal (← term F sc' none a)
      let bt ← asReal (← term F sc' none b)
      let body := Tm.lt (.sub bt at_) (.loc k)
      let exs := bs.foldr (fun bi acc => Tm.ex bi.ty (Tm.mkAnd (holdsAt bi.pred (.loc 0)) acc)) body
      pure (Tm.all .real (.imp (.lt (.num 0) (.loc 0)) exs))
    pure (conjAll parts)
  | .equalityOn s => do
    let some (bs, ineq) := (← get).lastIneq | fail E.referent
    let some e := inequality ineq | fail E.referent
    let sc' := scopeOf bs ++ sc
    let ep ← prop sc' none e
    let (st, sty) ← term F sc' none s
    let k := bs.length
    let rec memb : Tm → Ty → List (Tm × Ty) → M Tm
      | t, .prop, [] => pure t
      | t, .fn a r, (x, xt) :: xs => do memb (.app t (← coerce x xt a)) r xs
      | _, _, _ => fail E.type
    let mem ← memb st sty ((List.range k).reverse.zip (bs.map (·.ty)) |>.map fun (j, t) => (Tm.loc j, t))
    pure (wrap bs (.iff ep mem))
  | .equalityWhen φ => do
    let some (bs, ineq) := (← get).lastIneq | fail E.referent
    let some e := inequality ineq | fail E.referent
    let sc' := scopeOf bs ++ sc
    let ep ← prop sc' none e
    let q ← prop sc' none φ
    pure (wrap bs (.iff ep q))
  | .ifThen cond cl => do
    let h ← prop sc none cond
    let p ← clauseTm c sc onVar lastRhs cl
    pure (.imp h p)
  | .adjectives s adjs => do
    let (t, ty) ← term F sc none s
    -- a function's domain is the one its definition states
    let dom : Tm ← match Elab.symKey s with
      | some k => do
        match ← lookupGlob k with
        | some (_, g) => pure (((g.doms.head?).join).getD (.lam .real .tt .tt))
        | none => pure (.lam .real .tt .tt)
      | none => pure (.lam .real .tt .tt)
    let ps ← adjs.mapM fun a => do
      if ty == .fn .real (.fn .real .prop) then
        if a == [w!"compact"] then pure (Tm.app (.prim .compact2) t)
        else if a == [w!"convex"] then pure (Tm.app (.prim .convex2) t)
        else if a == [w!"centrally", w!"symmetric"] then pure (Tm.app (.prim .symm2) t)
        else fail E.type
      else if ty == .fn .real .real then
        if a == [w!"continuous"] then pure (Tm.app (.app (.prim .continuousOn) t) dom)
        else if a == [w!"concave"] then pure (Tm.app (.app (.prim .concaveOn) t) dom)
        else if a == [w!"strictly", w!"increasing"] then pure (Tm.app (.app (.prim .strictMonoOn) t) dom)
        else fail E.type
      else fail E.type
    pure (conjAll ps)
  | .extremumOf isMax value f s at_ rels => do
    let fm ← match f with
      | some fm => pure fm
      | none => match (← get).lastExtremum with
        | some fm => pure fm
        | none => fail E.referent
    let st ← subjectTm sc s
    let (core, ty, _) ← extremumTm sc isMax fm value st
    let s' ← coerce st.1 st.2 ty
    let atP ← match at_ with
      | some a => do pure [← prop sc (some (s', ty)) a]
      | none => pure []
    let extra ← rels.mapM fun r => match r with
      | .has m => prop sc (some (s', ty)) m
      | .pred ph o => predicate sc (s', ty) ph o
    modify fun st' => { st' with
      extrema := st'.extrema ++ [(c.ctx.env, ⟨isMax, fm, value⟩)], subject := some (s', ty),
      lastExtremum := some fm }
    pure (conjAll (core :: atP ++ extra))
  | .increasing maps => do
    let mut parts := []
    let mut infos := []
    for m in maps do
      match m with
      | .mapsto (.id v) body => do
        let some b := (← get).envBinders.find? (·.name == v) | fail E.free v
        let (fn, _) ← Elab.lam F sc (.id v) [b.ty] (some .real) body
        let fn := onDomain b.pred fn
        let fxx : Tm := .app (shift 2 0 fn) (.loc 1)
        let fyy : Tm := .app (shift 2 0 fn) (.loc 0)
        let ltA : Tm := if b.ty == .unit then .lt (.ofUnit (.loc 1)) (.ofUnit (.loc 0)) else .lt (.loc 1) (.loc 0)
        parts := parts ++ [Tm.all b.ty (.all b.ty (Tm.mkImp (holdsAt b.pred (.loc 1))
          (Tm.mkImp (holdsAt b.pred (.loc 0)) (.imp ltA (.lt fxx fyy)))))]
        infos := infos ++ [(v, body)]
      | _ => fail E.unsupported
    modify fun st => { st with lastMaps := infos }
    pure (conjAll parts)
  | _ => fail E.unsupported

/-- `for $v\in D$, the k-th ranges over $B$`: the image of `D` under the `k`-th map
of the preceding sentence is `B`. -/
def rangesTm (sc : Scope) (k : Nat) (bind : BindInfo) (target : MT) : M Tm := do
  let some (v, body) := (← get).lastMaps[k]? | fail E.referent
  if v != bind.name then fail E.referent v
  let (fn, _) ← Elab.lam F sc (.id v) [bind.ty] (some .real) body
  let fn := onDomain bind.pred fn
  let fv : Tm := .app (shift 1 0 fn) (.loc 0)
  let inner ← Elab.term.member F ((v, bind.ty) :: sc) (fv, .real) target
  let into := Tm.all bind.ty (Tm.mkImp (holdsAt bind.pred (.loc 0)) inner)
  let inB ← Elab.term.member F ((w!"", .real) :: sc) (.loc 0, .real) target
  let onto := Tm.all .real (.imp inB (.ex bind.ty (Tm.mkAnd (holdsAt bind.pred (.loc 0))
    (.eq (.app (shift 2 0 fn) (.loc 0)) (.loc 1)))))
  pure (.and into onto)

def rhsOf : Clause → Option MT
  | .fact (.chain _ rs) | .scoped (.chain _ rs) _ _ _ => rs.getLast?.map (·.2)
  | _ => none

def citesOf (cl : CClause) : List Codes := cl.cites

/-- The claims of one sentence. `exactly one` takes the following clauses into its scope. -/
def claimSentence (c : SentCtx) (topic : Topic) (binds : List Bind) (cls : List CClause) : M (List Nat) := do
  modify fun st => { st with topic := if topic == .none then st.topic else topic }
  -- `If $φ$, …` about variables that are already bound (by the result or a fixed
  -- variable) is a hypothesis: of the first clause when a later clause has its own,
  -- otherwise of every clause
  let st0 ← get
  let known := st0.envBinders.map (·.name) ++ (st0.fixed.filter (·.1 == c.ctx.sec)).map (·.2.name)
  let isHyp (b : Bind) : Bool := match b with
    | .ifCond φ =>
      let fr := ((freeIds 64 [] φ).filter fun n => !(st0.globs.any fun g => g.key == n && !g.family)).eraseDups
      !fr.isEmpty && fr.all known.contains
    | _ => false
  let hyps := binds.filter isHyp
  let binds := binds.filter (!isHyp ·)
  let laterIf := (cls.drop 1).any fun cl => match cl.clause with | .ifThen .. => true | _ => false
  let cls := hyps.foldr (fun h acc => match h with
    | .ifCond φ =>
      if laterIf then match acc with
        | cl :: rest => { cl with clause := Clause.ifThen φ cl.clause } :: rest
        | [] => []
      else acc.map fun cl => { cl with clause := Clause.ifThen φ cl.clause }
    | _ => acc) cls
  let bss ← binds.mapM binderInfos
  let bs := bss.flatten
  -- `On I,`: the sentence's single free variable ranges over I
  let onVar ← match binds.find? (fun b => match b with | .on _ => true | _ => false) with
    | some (.on d) => do
      let (_, p) ← domainOf true d
      let known := (scopeOf bs).map (·.1)
      let st ← get
      let free := (cls.flatMap (fun cl => (clauseMaths cl.clause).flatMap (freeIds 64 known))).eraseDups
      let free := free.filter fun n => !(st.globs.any (·.key == n))
      match free with
      | [v] => pure (some (⟨v, .real, p⟩ : BindInfo))
      | _ => fail E.free free.flatten
    | _ => pure none
  -- variables bound by the opening binders of the current result carry over to
  -- its later sentences (`For $w\in[0,1]$, … . In particular, … w …`)
  let st ← get
  let inResult := match c.ctx.kind with | .result _ => true | _ => false
  let inherited ← if inResult && !st.envBinders.isEmpty then do
      let known := (scopeOf (bs ++ onVar.toList)).map (·.1)
      let clBound := cls.flatMap fun cl => (cl.binds.flatMap fun b => match b with
        | .every vs _ => vs | _ => []) ++ (match cl.clause with
          | .scoped _ vs _ _ | .every vs _ _ => vs | _ => [])
      let free := (cls.flatMap (fun cl => (clauseMaths cl.clause).flatMap (freeIds 64 (known ++ clBound)) ++
        ineqFree st cl.clause)).eraseDups
      let free := free.filter fun n => !(st.globs.any fun g => g.key == n && !g.family)
      pure (st.envBinders.filter fun b => free.contains b.name)
    else pure []
  if inResult && !bs.isEmpty then
    modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun b => !(bs.any (·.name == b.name)) }
  let allBs := inherited ++ bs ++ onVar.toList
  let sc := scopeOf allBs
  let rec go : Nat → List CClause → Option MT → M (List Nat)
    | 0, _, _ => pure []
    | _ + 1, [], _ => pure []
    | g + 1, cl :: rest, last =>
      match cl.clause with
      | .exactlyOne noun v cond sat => do
        let some ni := lookupWords (← get).nouns noun | fail E.noun noun.flatten
        let gty : Option Ty := ((← get).globs[ni]?).map (·.ty)
        let ty ← match gty with
          | some (.fn a .prop) => pure a
          | _ => fail E.type
        let sx := (v, ty) :: sc
        let cx ← prop sx none cond
        let sx' ← prop sx none sat
        let sy := (v, ty) :: sx
        let cy ← prop sy none cond
        let sy' ← prop sy none sat
        let uniq := Tm.all ty (.imp (.app (.glob ni) (.loc 0)) (.imp cy (.imp sy' (.eq (.loc 0) (.loc 1)))))
        modify fun st => { st with subject := some (.loc 0, ty) }
        -- the remaining clauses are in the scope of the unique element
        let inner ← rest.mapM fun cl' => clauseTm c sx none none cl'.clause
        let body := Tm.ex ty (conjAll ([Tm.app (.glob ni) (.loc 0), cx, sx', uniq] ++ inner))
        let id ← emit c (wrap allBs body) (cl.cites ++ rest.flatMap (·.cites))
        pure [id]
      | .ranges k target => do
        -- the binder of the map's variable (of the clause, or of the sentence) restricts
        -- the map's domain
        let some (v, _) := (← get).lastMaps[k]? | fail E.referent
        let cbs := (← cl.binds.mapM binderInfos).flatten
        let some b := (cbs ++ allBs).find? (·.name == v) | fail E.referent v
        let outer := (if cbs.isEmpty then allBs else inherited).filter (·.name != v)
        let p ← rangesTm (scopeOf outer) k b target
        let id ← emit c (wrap outer p) cl.cites
        let ids ← go g rest last
        pure (id :: ids)
      | k => do
        let cbs := (← cl.binds.mapM binderInfos).flatten
        -- a clause with its own binder is not in the scope of the sentence's opening
        -- binders; inherited binders bind the variables the clause uses
        let own := match k with | .scoped _ vs _ _ | .every vs _ _ => vs | _ => []
        let free := (clauseMaths k).flatMap (freeIds 64 ((scopeOf (bs ++ cbs)).map (·.1) ++ own)) ++
          ineqFree (← get) k
        let inh := inherited.filter fun b => free.contains b.name
        let outer := if cbs.isEmpty then inh ++ bs ++ onVar.toList else inh
        let p ← clauseTm c (scopeOf cbs ++ scopeOf outer) onVar last k
        let id ← emit c (wrap (outer ++ cbs) p) cl.cites
        let ids ← go g rest (match rhsOf k with | some r => some r | none => last)
        pure (id :: ids)
  go 16 cls none

/-- Compile one sentence: definitions and claims, or a reason it has none. -/
def sentence (c : SentCtx) (s : Sent) : M (List Nat × List Nat) := do
  match s with
  | .defClass sym plural np => defClass sym plural np
  | .defIs b items => do
    let bs ← binderInfos b
    let [bi] := bs | fail E.unsupported
    -- `the X and the Y are DISPLAY` with one definition each
    let items := items.flatMap fun it => match it.defn with
      | .conj xs =>
        let parts := (it.name.splitOn w!"and").map fun ws => ws.filter (· != w!"the")
        if parts.length == xs.length then (xs.zip parts).map fun (x, n) => ({ it with defn := x, name := n } : DefItem)
        else xs.map fun x => ({ it with defn := x } : DefItem)
      | _ => [it]
    let rs ← items.mapM (defItem c bi)
    pure (rs.flatMap (·.1), rs.flatMap (·.2))
  | .constDefs b defs labels => do
    match b with
    | some bd => do
      let [bi] ← binderInfos bd | fail E.unsupported
      constDefs c (some bi) defs labels
    | none => constDefs c none defs labels
  | .defReads b _ sg disp labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    defReads c bi sg disp labels
  | .defBy sg pieces labels obs => defBy c sg pieces labels obs
  | .denotedBy name sym => denotedBy name sym
  | .letDenote b sym np => do
    let [bi] ← binderInfos b | fail E.unsupported
    letDenote bi sym np
  | .weSay sb ph o cond vs d => weSay sb ph o cond vs d
  | .defSteps b sets sym np whereDef => do
    let [bi] ← binderInfos b | fail E.unsupported
    let mut ds := []
    let mut cs := []
    for m in sets do
      let (d', c') ← setDef c bi m
      ds := ds ++ d'
      cs := cs ++ c'
    if let some (sg, disp, ls) := whereDef then
      let (d', c') ← defReads c bi sg disp ls
      ds := ds ++ d'
      cs := cs ++ c'
    let (d', c') ← letDenote bi sym np
    pure (ds ++ d', cs ++ c')
  | .claims topic binds cls => do
    let ids ← claimSentence c topic binds cls
    pure ([], ids)
  | .fix b defs labels => do
    let [bi] ← binderInfos b | fail E.unsupported
    modify fun st => { st with fixed := (c.ctx.sec, bi) :: st.fixed.filter (·.2.name != bi.name) }
    if defs.isEmpty then pure ([], []) else constDefs c (some bi) defs labels
  | .assume b => do
    let bs ← binderInfos b
    match c.ctx.kind with
    | .text =>
      modify fun st => { st with fixed := bs.map (c.ctx.sec, ·) ++ st.fixed.filter fun (_, x) => !(bs.any (·.name == x.name)) }
    | _ =>
      modify fun st => { st with envBinders := bs ++ st.envBinders.filter fun x => !(bs.any (·.name == x.name)) }
    pure ([], [])
  | .defDeriv b sets names dom cod anchors derivs labels => do
    let bi ← match b with
      | some bd => do
        let [bi] ← binderInfos bd | fail E.unsupported
        pure (some bi)
      | none =>
        -- the variable of the names' subscripts, fixed earlier in the section
        match names.head? with
        | some (.sub (.id _) (.id p)) => do
          match (← get).fixed.find? (fun (s, x) => s == c.ctx.sec && x.name == p) with
          | some (_, x) => pure (some x)
          | none => fail E.free p
        | _ => pure none
    let (d1, c1) ← match bi, sets with
      | _, [] => pure ([], [])
      | some x, _ => constDefs c (some x) sets []
      | none, _ => fail E.unsupported
    let (d2, c2) ← defDeriv bi names dom cod anchors derivs labels
    pure (d1 ++ d2, c1 ++ c2)

end Compile

/-- The state of the compiler between sentences. -/
structure CState where
  st : St
  /-- Index of the next sentence. -/
  idx : Nat := 0
  /-- Outcomes of the sentences read so far, latest first. -/
  outcomesRev : List Outcome := []
  proofs : List ProofInfo := []
  deriving Inhabited, Lean.ToExpr

/-- Environment index of each result, by label (for proofs that name their result). -/
def envTable (ss : List Sentence) : List (Codes × Nat) :=
  ss.filterMap fun s => match s.ctx.kind with
    | .result _ => some (s.ctx.label, s.ctx.env)
    | _ => none

open Compile in
/-- Compile one sentence. A failing sentence leaves no trace in the state. -/
def compileOne (envs : List (Codes × Nat)) (c : CState) (s : Sentence) : CState :=
  -- entering a new environment resets proof-local state
  let st0 := c.st
  let st0 := if st0.proofEnv != s.ctx.env then
      { st0 with proofEnv := s.ctx.env, proofCites := [], proofSteps := [], topic := .none, envBinders := [] }
    else st0
  let ps := match s.ctx.kind with
    | .proof => if c.proofs.any (·.env == s.ctx.env) then c.proofs
      else c.proofs ++ [({ env := s.ctx.env, proves := s.ctx.proves, steps := [], cites := [], complete := true } : ProofInfo)]
    | _ => c.proofs
  let incomplete (ps : List ProofInfo) : List ProofInfo :=
    ps.map fun p => if p.env == s.ctx.env then { p with complete := false } else p
  match Grammar.parseSentence s with
  | none => { c with st := st0, idx := c.idx + 1, outcomesRev := .prose :: c.outcomesRev, proofs := incomplete ps }
  | some sent =>
    let sc : SentCtx := ⟨s.ctx, (envs.lookup s.ctx.proves).getD 0, c.idx⟩
    let labelled : M (List Nat × List Nat) := do
      let (ds, cs) ← Compile.sentence sc sent
      match sent with
      | .claims _ _ _ =>
        -- labels of displays in the sentence, and of the enclosing result, name its claims
        let ls := s.toks.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        let ls := match s.ctx.kind with
          | .result _ => if s.ctx.label.isEmpty then ls else s.ctx.label :: ls
          | _ => ls
        Compile.addLabels ls cs false
      | _ => pure ()
      pure (ds, cs)
    let (r, st) := labelled.run.run st0
    match r with
    | .ok (ds, cs) =>
      let ps := ps.map fun p => if p.env == s.ctx.env then
        { p with steps := st.proofSteps, cites := st.proofCites } else p
      { st, idx := c.idx + 1, outcomesRev := .compiled ds cs :: c.outcomesRev, proofs := ps }
    | .error e =>
      { c with st := st0, idx := c.idx + 1, outcomesRev := .failed e :: c.outcomesRev, proofs := incomplete ps }

/-- Compile a list of sentences, starting from a compiler state. -/
def compileAll (envs : List (Codes × Nat)) (c : CState) (ss : List Sentence) : CState :=
  ss.foldl (compileOne envs) c

theorem compileAll_append (envs : List (Codes × Nat)) (c : CState) (a b : List Sentence) :
    compileAll envs c (a ++ b) = compileAll envs (compileAll envs c a) b := by
  simp [compileAll, List.foldl_append]

/-- Results whose printed proof compiled completely: the proof is their premise. -/
def closeProofs (ss : List Sentence) (claims : List Claim) (ps : List ProofInfo) : List Claim :=
  claims.map fun cl =>
    match cl.role with
    | .statement env =>
      let label := (ss.find? (fun s => s.ctx.env == env)).map (·.ctx.label) |>.getD []
      match ps.find? (fun p => p.proves == label && p.complete && !p.steps.isEmpty) with
      | some p => { cl with premises := (p.steps ++ p.cites).eraseDups }
      | none => cl
    | _ => cl

def beginDocument (ts : List PTok) : List PTok :=
  match ts.findIdx? (fun t => t.tok == .begin w!"document") with
  | some i => ts.drop (i + 1)
  | none => ts

/-- The document of a compiled article, from the final compiler state. -/
def finish (ss : List Sentence) (c : CState) : Doc :=
  let st := c.st
  let claims := closeProofs ss st.claims c.proofs
  ⟨st.globs, st.values, claims, ss.map (fun s => (s.ctx, s.start, s.stop)), c.outcomesRev.reverse,
    st.labels, c.proofs, st.preds ++ st.named ++ st.ops ++ st.classes⟩

/-- Compile the sentences of an article into its document. -/
def assemble (V : Vocab) (ss : List Sentence) : Doc :=
  finish ss (compileAll (envTable ss) { st := { vocab := V } } ss)

def isBeginDocument (l : Codes) : Bool := l.take 16 == w!"\\begin{document}"

/-- Lex and segment the paragraph blocks in order: the completed sentences, the
final math-mode stack and the segmentation state. -/
def lexSeg (ms : Macros) : List (Nat × List Codes) → List Bool → Segment.St →
    Option (List Sentence × List Bool × Segment.St)
  | [], m, s => some ([], m, s)
  | (p, ls) :: bs, m, s =>
    match lexBlock ms (joinLines ls) m with
    | none => none
    | some (t, m') =>
      let r := segBlock p (t ++ blockBreak m') s
      match lexSeg ms bs m' r.2 with
      | none => none
      | some (rest, m'', s'') => some (r.1 ++ rest, m'', s'')

theorem lexSeg_nil (ms : Macros) (m : List Bool) (s : Segment.St) : lexSeg ms [] m s = some ([], m, s) := rfl

theorem lexSeg_cons (ms : Macros) (p : Nat) (ls : List Codes) (b : Codes) (bs : List (Nat × List Codes))
    (m m' m'' : List Bool) (s s' s'' : Segment.St) (t : List PTok) (ss rest : List Sentence)
    (h0 : joinLines ls = b) (h1 : lexBlock ms b m = some (t, m')) (h2 : segBlock p (t ++ blockBreak m') s = (ss, s'))
    (h3 : lexSeg ms bs m' s' = some (rest, m'', s'')) :
    lexSeg ms ((p, ls) :: bs) m s = some (ss ++ rest, m'', s'') := by
  simp [lexSeg, h0, h1, h2, h3]

/-- The complete compilation of an article from its source lines, with the
vocabulary `V`: the preamble supplies the macros, the paragraphs after
`\begin{document}` the sentences. -/
def compileArticle (V : Vocab) (src : Source) : Option Doc := do
  let k ← src.findIdx? isBeginDocument
  let ms ← macrosOf (joinLines (src.take k))
  let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
  let (ss, _, s) ← lexSeg ms bs [] {}
  some (assemble V (ss ++ segFinish s))

/-- Staged kernel certificates compose to the compilation of the whole source. -/
theorem compileArticle_eq {V : Vocab} {src : Source} {k : Nat} {ms : Macros} {bs : List (Nat × List Codes)}
    {ss ss' : List Sentence} {m : List Bool} {s : Segment.St} {d : Doc}
    (h0 : src.findIdx? isBeginDocument = some k)
    (h1 : macrosOf (joinLines (src.take k)) = some ms)
    (h2 : blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none [] = bs)
    (h3 : lexSeg ms bs [] {} = some (ss, m, s)) (h4 : ss ++ segFinish s = ss') (h5 : assemble V ss' = d) :
    compileArticle V src = some d := by
  simp [compileArticle, h0, h1, h2, h3, h4, h5]

end Proofread
