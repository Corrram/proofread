import Proofread.Grammar
import Proofread.Vocab

/-! # Elaboration: the fixed readings of the grammar

Every construction of `Grammar` has exactly one reading, given here. Symbols
introduced by the article are *definitions*: their meaning is their defining
formula, nothing else. Applying a symbol outside the domain stated in its
definition is recorded as a definedness condition, never silently allowed.

Readings (`x`, `y` range over the domain of the noun or binder):
* `let S denote the class of Ns, that is, NP` — `S := {F | NP(F)}`; `N` names `S`.
* `For a N $x$, the NAME is $X(…) := e$` — defines `X` on `N`; further `= e'` are claims.
* `define $f:A\to B$ by …` — defines `f` on `A`; `f(A) ⊆ B` is a claim.
* `We say that a N $x$ is P of a M $y$ if φ for all …` — defines the relation `P`.
* `exactly one N $x$ with φ satisfies ψ` — `∃x∈N, φ ∧ ψ ∧ ∀y∈N, φ(y) ∧ ψ(y) → y = x`;
  following clauses about `its …` are inside this scope.
* `X is the only N with φ` — `X ∈ N ∧ φ(X) ∧ ∀y∈N, φ(y) → y = X`.
* `The maximum $F=m$ is attained only by X` — `∀x, F(x) ≤ m`, `X` is in the domain,
  `F(X) = m`, and `F(x) = m → x = X` (minimum: `≥`).
* `$λ$ increases bijectively from A onto B` — maps `A` into `B`, strictly increasing, onto `B`.
* `On I, … its derivative $d$ is positive for φ` — the derivative within `I` of the
  preceding right-hand side is `d`, and `φ → d > 0`.
* `φ for every $x\in A$, with equality only at ψ` — `∀x∈A, φ ∧ (a = b → ψ)` for the
  inequality `a ≤ b` of `φ`.
* `no N other than X attains the maximum` — `∀y∈N, F(y) = m → y = X`.
* `the map $λ$ sends F to G` — `∀x, F(λ x) = G(x)`.
* `only X attains it` — `X` attains the topic extremum, and no other element does.
* `X is P of Y` — the article's relation `P` holds of `X` and `Y`.
-/
namespace Proofread
open Grammar

structure Glob where
  key : Codes
  ty : Ty
  /-- Domain predicates of the curried arguments (`none`: the whole type). -/
  doms : List (Option Tm)
  family : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Role where
  | definition
  | statement (env : Nat)
  | step (env : Nat)
  | text
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Claim where
  sent : Nat
  body : Tm
  role : Role
  cites : List Codes
  premises : List Nat
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Err where
  code : Nat
  detail : Codes
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

inductive Outcome where
  | prose
  | failed (e : Err)
  | compiled (defs : List Nat) (claims : List Nat)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- Error codes (rendered by the driver). -/
def E.undefined := 1
def E.type := 2
def E.unsupported := 3
def E.noun := 4
def E.label := 5
def E.free := 6
def E.redefined := 7
def E.referent := 8
def E.shadow := 9

abbrev Local := Codes × Ty
abbrev Scope := List Local

/-- The topic extremum of a statement: the function's formula, its value, and
whether it is a maximum. -/
structure Extremum where
  isMax : Bool
  f : MT
  value : MT
  deriving Repr, Inhabited

structure St where
  /-- The vocabulary of the article. -/
  vocab : Vocab := {}
  globs : List Glob := []
  values : List Tm := []
  claims : List Claim := []
  /-- Noun phrases naming a predicate (a class). -/
  nouns : List (List Codes × Nat) := []
  /-- Noun phrases naming an operation, e.g. `survival copula`. -/
  ops : List (List Codes × Nat) := []
  /-- Relation phrases, e.g. `supported on the graph`. -/
  preds : List (List Codes × Nat) := []
  /-- Named objects, e.g. `tent map`. -/
  named : List (List Codes × Nat) := []
  labels : List (Codes × List Nat) := []
  /-- Labels of definitions (cited definitions are always available). -/
  defLabels : List Codes := []
  /-- Extremum of each result environment. -/
  extrema : List (Nat × Extremum) := []
  /-- Citations accumulated in the current proof, and its earlier steps. -/
  proofEnv : Nat := 0
  proofCites : List Nat := []
  proofSteps : List Nat := []
  /-- The most recent subject (for `its`). -/
  subject : Option (Tm × Ty) := none
  topic : Topic := .none
  deriving Inhabited

abbrev M := ExceptT Err (StateM St)

def fail {α : Type} (code : Nat) (detail : Codes := []) : M α := throw ⟨code, detail⟩

def liftO {α : Type} (o : Option α) (code : Nat) (detail : Codes := []) : M α :=
  match o with | some a => pure a | none => fail code detail

namespace Elab

def tTrue : Tm := .tt
def interval (lo hi : Tm) (x : Tm) : Tm := .and (.le lo x) (.le x hi)

def singular (w : Codes) : Codes :=
  match w.reverse with
  | 115 :: r => r.reverse
  | _ => w

def lookupGlob (key : Codes) : M (Option (Nat × Glob)) := do
  let st ← get
  let rec find : Nat → List Glob → Option (Nat × Glob)
    | _, [] => none
    | i, g :: gs => match find (i + 1) gs with
      | some r => some r
      | none => if g.key == key && !key.isEmpty then some (i, g) else none
  pure (find 0 st.globs)

def addGlob (g : Glob) (v : Tm) : M Nat := do
  let st ← get
  if !g.key.isEmpty && (st.globs.any (·.key == g.key)) then fail E.redefined g.key
  set { st with globs := st.globs ++ [g], values := st.values ++ [v] }
  pure st.globs.length

def addClaim (c : Claim) : M Nat := do
  let st ← get
  set { st with claims := st.claims ++ [c] }
  pure st.claims.length

def globTy (i : Nat) : M Ty := do
  let st ← get
  match st.globs[i]? with
  | some g => pure g.ty
  | none => fail E.undefined

def lookupLocal : Scope → Codes → Option (Nat × Ty)
  | [], _ => none
  | (n, t) :: sc, x => if n == x then some (0, t) else (lookupLocal sc x).map fun (i, t) => (i + 1, t)

/-- Shift free local indices `≥ c` by `k`. -/
abbrev shift := Tm.shift

/-- Closed terms (predicates of globals) used under `n` binders need no shift,
but a predicate applied to a local must be written as an application. -/
def applyPred (p : Tm) (x : Tm) : Tm := .app p x

def coerce (t : Tm) (src dst : Ty) : M Tm :=
  if src == dst then pure t
  else if src == .unit && dst == .real then pure (.ofUnit t)
  else if src == .real && dst == .unit then pure (.toUnit t)
  else fail E.type

def asReal (p : Tm × Ty) : M Tm := coerce p.1 p.2 .real

def isMeasure : Ty → Bool
  | .fn (.fn .unit .prop) .real => true
  | .fn (.fn .unit (.fn .unit .prop)) .real => true
  | _ => false

def measGuard (argTy : Ty) (arg : Tm) : Option Tm :=
  if argTy == Ty.set1 then some (.app (.prim .measurableSet1) arg)
  else if argTy == Ty.set2 then some (.app (.prim .measurableSet2) arg)
  else none

/-- Apply a head of type `ty` to arguments, inserting coercions, the domain
guards of the head's definition, and measurability guards for measures. -/
def applyAll (head : Tm) (ty : Ty) (doms : List (Option Tm)) : List (Tm × Ty) → M (Tm × Ty)
  | [] => pure (head, ty)
  | (a, aty) :: rest =>
    match ty with
    | .fn dom cod => do
      let a' ← coerce a aty dom
      let applied := Tm.app head a'
      let guarded := match doms.head? with
        | some (some p) => Tm.guard (applyPred p a') applied
        | _ => applied
      let guarded := if isMeasure ty then
          match measGuard dom a' with | some g => Tm.guard g guarded | none => guarded
        else guarded
      applyAll guarded cod (doms.drop 1) rest
    | _ =>
      -- a real number applied to one argument is a product
      if ty == .real && rest.isEmpty then do
        let a' ← coerce a aty .real
        pure (.mul head a', .real)
      else fail E.type

def relTm (r : Rel) (x y : Tm × Ty) : M Tm := do
  match r with
  | .eq =>
    if x.2 == y.2 then pure (.eq x.1 y.1)
    else pure (.eq (← asReal x) (← asReal y))
  | .ne =>
    if x.2 == y.2 then pure (.not (.eq x.1 y.1))
    else pure (.not (.eq (← asReal x) (← asReal y)))
  | .le => pure (.le (← asReal x) (← asReal y))
  | .lt => pure (.lt (← asReal x) (← asReal y))
  | .ge => pure (.le (← asReal y) (← asReal x))
  | .gt => pure (.lt (← asReal y) (← asReal x))
  | _ => fail E.unsupported

def conjAll : List Tm → Tm
  | [] => .tt
  | [p] => p
  | p :: ps => .and p (conjAll ps)

/-- `∀` over a list of binders (innermost last), with domain hypotheses. -/
def forallBinders : List (Codes × Ty × Option Tm) → Tm → Tm
  | [], body => body
  | (_, t, p) :: bs, body =>
    let inner := forallBinders bs body
    match p with
    | some p => .all t (.imp p inner)
    | none => .all t inner

/-- Pointwise set equality of two predicates of the same (curried) type. -/
def setEq (ty : Ty) (a b : Tm) : Tm :=
  match ty with
  | .fn t1 (.fn t2 .prop) =>
    .all t1 (.all t2 (.iff (.app (.app (shift 2 0 a) (.loc 1)) (.loc 0))
      (.app (.app (shift 2 0 b) (.loc 1)) (.loc 0))))
  | .fn t1 .prop => .all t1 (.iff (.app (shift 1 0 a) (.loc 0)) (.app (shift 1 0 b) (.loc 0)))
  | _ => .eq a b

def isPredTy : Ty → Bool
  | .fn _ .prop => true
  | .fn _ (.fn _ .prop) => true
  | _ => false

def isZeroOne : MT → Bool
  | .interval (.num 0) (.num 1) => true
  | _ => false

/-- The point-free subject: a term substituted for unapplied functions on its type. -/
abbrev PF := Option (Tm × Ty)

/-- Elaborate a formula. Fuel bounds the recursion (kernel-reducible). -/
def term : Nat → Scope → PF → MT → M (Tm × Ty)
  | 0, _, _, _ => fail E.unsupported
  | f + 1, sc, pf, m =>
    match m with
    | .num n => pure (.num n, .real)
    | .id n => do
      match lookupLocal sc n with
      | some (i, t) =>
        match pf, t with
        | some (s, sty), .fn a b => if a == sty then pure (.app (.loc i) s, b) else pure (.loc i, t)
        | _, _ => pure (.loc i, t)
      | none =>
        match ← lookupGlob n with
        | some (i, g) =>
          match pf, g.ty with
          | some (s, sty), .fn a _ =>
            if a == sty then applyAll (.glob i) g.ty g.doms [(s, sty)] else pure (.glob i, g.ty)
          | _, _ => pure (.glob i, g.ty)
        | none => fail E.undefined n
    | .add x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.add a b, .real)
    | .minus x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.sub a b, .real)
    | .mul x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.mul a b, .real)
    | .div x y | .frac x y => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y); pure (.div a b, .real)
    | .neg x => do let a ← asReal (← term f sc pf x); pure (.neg a, .real)
    | .abs x => do let a ← asReal (← term f sc pf x); pure (.abs a, .real)
    | .minm [x, y] => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y)
      pure (.app (.app (.prim .min) a) b, .real)
    | .maxm [x, y] => do
      let a ← asReal (← term f sc pf x); let b ← asReal (← term f sc pf y)
      pure (.app (.app (.prim .max) a) b, .real)
    | .sup b e =>
      match e with
      | .id d =>
        if d == w!"\\top" || d == w!"\\perp" then do
          let (h, g) ← liftO (← lookupGlob (w!"^" ++ d)) E.undefined (w!"^" ++ d)
          let x ← term f sc pf b
          applyAll (.glob h) g.ty g.doms [x]
        else fail E.unsupported d
      | .num n => do
        let a ← asReal (← term f sc pf b)
        pure (.powNat a n, .real)
      | _ => do
        let a ← asReal (← term f sc pf b)
        let p ← asReal (← term f sc pf e)
        pure (.guard (.le (.num 0) a) (.app (.app (.prim .rpow) a) p), .real)
    | .hat x => do
      let (h, g) ← liftO (← lookupGlob w!"\\widehat") E.undefined w!"\\widehat"
      let a ← term f sc pf x
      applyAll (.glob h) g.ty g.doms [a]
    | .sub b i =>
      match b with
      | .id key => do
        let (h, g) ← liftO (← lookupGlob key) E.undefined key
        if !g.family then fail E.unsupported key
        let a ← term f sc none i
        applyAll (.glob h) g.ty g.doms [a]
      | _ => fail E.unsupported
    | .app hd args => do
      let (h, hty, doms) ← head f sc hd
      let xs ← args.mapM (term f sc pf)
      applyAll h hty doms xs
    | .int (.num 0) (.num 1) body v => do
      if (lookupLocal sc v).isSome then fail E.shadow v
      let b ← asReal (← term f ((v, .unit) :: sc) (pf.map fun (s, t) => (shift 1 0 s, t)) body)
      pure (.integral b, .real)
    | .chain x rest => do
      let ts ← (x :: rest.map (·.2)).mapM (term f sc pf)
      let rels := rest.map (·.1)
      if rels.any (· == .mem) then
        match x, rest with
        | _, [(.mem, dom)] => do
          let a ← term f sc pf x
          let p ← member f sc a dom
          pure (p, .prop)
        | _, _ => fail E.unsupported
      else
      -- set equality between predicates
      match ts, rels with
      | [a, b], [.eq] =>
        if isPredTy a.2 && a.2 == b.2 then pure (setEq a.2 a.1 b.1, .prop)
        else do pure (← relTm .eq a b, .prop)
      | _, _ => do
        let rec pairs : List (Tm × Ty) → List Rel → M (List Tm)
          | a :: b :: more, r :: rs => do
            let p ← relTm r a b
            let ps ← pairs (b :: more) rs
            pure (p :: ps)
          | _, _ => pure []
        pure (conjAll (← pairs ts rels), .prop)
    | .conj xs => do
      let ps ← xs.mapM fun x => do
        let (p, t) ← term f sc pf x
        if t == .prop then pure p else fail E.type
      pure (conjAll ps, .prop)
    | .setOf pat dom conds => setOf f sc pat dom conds
    | .image (.tuple [e1, e2]) v (.id dom) => do
      -- {(e1(v), e2(v)) : v ∈ D} as the relation (r, n) ↦ ∃ v ∈ D, e1 = r ∧ e2 = n
      let (dp, dg) ← liftO (← lookupGlob dom) E.undefined dom
      let vty ← match dg.ty with | .fn a .prop => pure a | _ => fail E.type
      let sc' := (v, vty) :: (w!"", .real) :: (w!"", .real) :: sc
      let a ← asReal (← term f sc' none e1)
      let b ← asReal (← term f sc' none e2)
      let body := Tm.and (.app (.glob dp) (.loc 0)) (.and (.eq a (.loc 2)) (.eq b (.loc 1)))
      pure (.lam .real .tt (.lam .real .tt (.ex vty body)), .fn .real (.fn .real .prop))
    | .cases rows => casesRows f sc pf rows
    | _ => fail E.unsupported
where
  casesRows : Nat → Scope → PF → List (MT × MT) → M (Tm × Ty)
    | 0, _, _, _ => fail E.unsupported
    | _ + 1, _, _, [] => pure (.undef .real, .real)
    | g + 1, sc, pf, (v, c) :: rs => do
      let (vt, ty) ← term g sc pf v
      let vt ← coerce vt ty .real
      let (ct, cty) ← term g sc pf c
      if cty != .prop then fail E.type
      let (rt, _) ← casesRows g sc pf rs
      pure (.cases ct vt rt, .real)
  head : Nat → Scope → MT → M (Tm × Ty × List (Option Tm))
    | 0, _, _ => fail E.unsupported
    | g + 1, sc, hd =>
      match hd with
      | .id n =>
        match lookupLocal sc n with
        | some (i, t) => pure (.loc i, t, [])
        | none => do
          let (i, gl) ← liftO (← lookupGlob n) E.undefined n
          pure (.glob i, gl.ty, gl.doms)
      | .sub (.id key) i => do
        let (h, gl) ← liftO (← lookupGlob key) E.undefined key
        let a ← term g sc none i
        let (t, ty) ← applyAll (.glob h) gl.ty gl.doms [a]
        pure (t, ty, gl.doms.drop 1)
      | _ => do
        let (t, ty) ← term g sc none hd
        pure (t, ty, [])
  member : Nat → Scope → Tm × Ty → MT → M Tm
    | 0, _, _, _ => fail E.unsupported
    | g + 1, sc, x, dom =>
      match dom with
      | .interval lo hi => do
        if x.2 == .unit && isZeroOne dom then pure .tt
        else
          let l ← asReal (← term g sc none lo)
          let h ← asReal (← term g sc none hi)
          pure (interval l h (← asReal x))
      | .id n => do
        let (i, gl) ← liftO (← lookupGlob n) E.undefined n
        match gl.ty with
        | .fn a .prop => do let x' ← coerce x.1 x.2 a; pure (.app (.glob i) x')
        | _ => fail E.type
      | _ => fail E.unsupported
  setOf : Nat → Scope → MT → MT → List MT → M (Tm × Ty)
    | 0, _, _, _, _ => fail E.unsupported
    | g + 1, sc, pat, dom, conds =>
      match pat, dom with
      | .id v, d => do
        let (ty, pred) ← elemDom g d
        let sc' := (v, ty) :: sc
        let cs ← conds.mapM fun c => do
          let (p, t) ← term g sc' none c
          if t == .prop then pure p else fail E.type
        let mem := match pred with | some p => [p] | none => []
        pure (.lam ty .tt (conjAll (mem ++ cs)), .fn ty .prop)
      | .tuple [.id v1, .id v2], .sup d (.num 2) => do
        let (ty, pred) ← elemDom g d
        let sc' := (v2, ty) :: (v1, ty) :: sc
        let cs ← conds.mapM fun c => do
          let (p, t) ← term g sc' none c
          if t == .prop then pure p else fail E.type
        -- both coordinates lie in the domain; `p` speaks about `loc 0`
        let mem := match pred with
          | some p => [Tm.and (.app (.lam ty .tt p) (.loc 1)) (.app (.lam ty .tt p) (.loc 0))]
          | none => []
        pure (.lam ty .tt (.lam ty .tt (conjAll (mem ++ cs))), .fn ty (.fn ty .prop))
      | _, _ => fail E.unsupported
  /-- Element type of an interval domain, and the membership predicate of the
  innermost bound variable (`loc 0`). -/
  elemDom : Nat → MT → M (Ty × Option Tm)
    | 0, _ => fail E.unsupported
    | _ + 1, d =>
      if isZeroOne d then pure (.unit, none)
      else match d with
        | .interval (.neg (.num a)) (.num b) => pure (.real, some (interval (.neg (.num a)) (.num b) (.loc 0)))
        | .interval (.num a) (.num b) => pure (.real, some (interval (.num a) (.num b) (.loc 0)))
        | _ => fail E.unsupported

/-- Elaborate a lambda `pat ↦ body` with the given argument types and result type. -/
def lam (f : Nat) (sc : Scope) (pat : MT) (args : List Ty) (res : Option Ty) (body : MT) :
    M (Tm × Ty) := do
  let names ← match pat with
    | .id v => pure [v]
    | .tuple vs => vs.mapM fun v => match v with | .id n => pure n | _ => fail E.unsupported
    | _ => fail E.unsupported
  if names.length != args.length then fail E.type
  let sc' := (names.zip args).reverse ++ sc
  let (b, bty) ← term f sc' none body
  let (b, bty) ← match res with
    | some r => do pure (← coerce b bty r, r)
    | none => pure (b, bty)
  let rec wrap : List Ty → Tm × Ty
    | [] => (b, bty)
    | t :: ts => let (x, xt) := wrap ts; (.lam t .tt x, .fn t xt)
  pure (wrap args)

end Elab
end Proofread
