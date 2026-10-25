import Proofread.Segment

/-! # The sentence grammar

A sentence is read as a sequence of chunks: words, punctuation, inline formulas,
displays and references. The grammar is a fixed list of constructions of
mathematical English. Each has one documented reading (see `Elab`). A sentence
that matches none of them completely is prose: it is kept and shown, but it
asserts nothing checkable. A partial match is never accepted. -/
namespace Proofread

inductive Chunk where
  | w (word : Codes)
  | p (c : Nat)
  | m (toks : List MTok)
  | d (toks : List MTok) (labels : List Codes)
  | r (kind : RefKind) (arg : Codes)
  | x
  deriving Repr, Inhabited

namespace Grammar

def lower (c : Codes) : Codes := c.map fun x => if 65 ≤ x && x ≤ 90 then x + 32 else x

def isSig : List MTok → Bool := fun ts => ts.contains (.cmd w!"to")

/-- Drop a final period or comma of a display (it belongs to the sentence). -/
def hoist (ts : List MTok) : List MTok × Option Nat :=
  -- a final period may sit inside nested environments; a comma only at top level
  let rec go : List MTok → List MTok → Option (List MTok × Nat)
    | [], _ => none
    | t :: rest, after =>
      match t with
      | .finish _ | .rb | .row => go rest (t :: after)
      | .sym 46 => some (rest.reverse ++ after, 46)
      | .sym 44 => if after.isEmpty then some (rest.reverse ++ after, 44) else none
      | _ => none
  match go ts.reverse [] with
  | some (r, c) => (r, some c)
  | none => (ts, none)

/-- Group a sentence's tokens into chunks. -/
def chunks : Nat → List PTok → List Chunk → Option (List Chunk)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | f + 1, t :: ts, acc =>
    match t.tok with
    | .word w => chunks f ts (.w (lower w) :: acc)
    | .punct c => chunks f ts (.p c :: acc)
    | .ref k a => chunks f ts (.r k a :: acc)
    | .mopen =>
      let body := ts.takeWhile (fun p => p.tok != .mclose)
      match Math.simplify (body.length + 1) body with
      | some ms =>
        let (ms, punct) := hoist ms
        let acc := Chunk.m ms :: acc
        let acc := match punct with | some c => .p c :: acc | none => acc
        chunks f (ts.drop (body.length + 1)) acc
      | none => none
    | .begin e =>
      if Lex.wDisplayEnvs.contains e then
        let body := ts.takeWhile (fun p => p.tok != .finish e)
        let labels := body.filterMap fun p => match p.tok with | .ref .label l => some l | _ => none
        match Math.simplify (body.length + 1) body with
        | some ms =>
          let (ms, punct) := hoist ms
          let acc := Chunk.d ms labels :: acc
          let acc := match punct with | some c => .p c :: acc | none => acc
          chunks f (ts.drop (body.length + 1)) acc
        | none => none
      else chunks f ts (.x :: acc)
    | _ => chunks f ts (.x :: acc)

/-- A sequence of exact (lower-case) words. -/
def kw : List Codes → List Chunk → Option (List Chunk)
  | [], cs => some cs
  | w :: ws, .w v :: cs => if v == w then kw ws cs else none
  | _, _ => none

def punct (c : Nat) : List Chunk → Option (List Chunk)
  | .p d :: cs => if c == d then some cs else none
  | _ => none

def optPunct (c : Nat) (cs : List Chunk) : List Chunk := (punct c cs).getD cs

def mathChunk : List Chunk → Option (List MTok × List Chunk)
  | .m ts :: cs => some (ts, cs)
  | _ => none

def formula (cs : List Chunk) : Option (MT × List Chunk) := do
  let (ts, rest) ← mathChunk cs
  let m ← Math.parseDisplay ts
  some (m, rest)

def sig (cs : List Chunk) : Option (MT × List Chunk) := do
  let (ts, rest) ← mathChunk cs
  let m ← Math.parseSig ts
  some (m, rest)

def display (cs : List Chunk) : Option (MT × List Codes × List Chunk) :=
  match cs with
  | .d ts ls :: rest => do
    let m ← Math.parseDisplay ts
    some (m, ls, rest)
  | _ => none

/-- Binder formulas `x\in A`, `u,v\in A`, or `(x,z)\in A^2` (each coordinate in `A`). -/
def binderMath (ts : List MTok) : Option (List Codes × MT) := do
  let i ← ts.findIdx? (· == .cmd w!"in")
  let pre := ts.take i
  let (pre, square) := match pre with
    | .sym 40 :: r => match r.reverse with
      | .sym 41 :: r' => (r'.reverse, true)
      | _ => (pre, false)
    | _ => (pre, false)
  let vars := pre.filter (· != .sym 44)
  let names ← vars.mapM fun t => match t with | .id n => some n | _ => none
  let dom ← Math.parseFormula (ts.drop (i + 1))
  let dom ← if square then
      match dom with
      | .sup d (.num k) => if k == names.length then some d else none
      | _ => none
    else some dom
  if names.isEmpty then none else some (names, dom)

/-- Words until (not including) a stop word; fails if a non-word chunk occurs. -/
def wordsUntil (stop : List Codes) : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | f + 1, .w v :: cs, acc =>
    if stop.contains v then some (acc.reverse, .w v :: cs) else wordsUntil stop f cs (v :: acc)
  | _, _, _ => none

/-- Chunks until a stop word at top level (words and formulas allowed). -/
def chunksUntil (stop : List Codes) : List Chunk → List Chunk → Option (List Chunk × List Chunk)
  | [], _ => none
  | .w v :: cs, acc =>
    if stop.contains v then some (acc.reverse, .w v :: cs) else chunksUntil stop cs (.w v :: acc)
  | c :: cs, acc =>
    match c with
    | .m _ => chunksUntil stop cs (c :: acc)
    | _ => none

/-- Citations: `Lemma~\ref{l}`, `Theorem~\ref{l}`, `\eqref{l}`. -/
def cite : List Chunk → Option (Codes × List Chunk)
  | .r .eqref l :: cs => some (l, cs)
  | .w v :: .r .ref l :: cs =>
    if [w!"lemma", w!"theorem", w!"corollary", w!"proposition", w!"equation", w!"section"].contains v then
      some (l, cs) else none
  | _ => none

def isEnd : List Chunk → Bool
  | [.p 46] => true
  | _ => false

/-- Discourse markers: they connect sentences and assert nothing. -/
def wMarkers : List (List Codes) :=
  [[w!"to", w!"make", w!"this", w!"precise"], [w!"consequently"], [w!"hence"], [w!"in", w!"particular"],
   [w!"then"], [w!"thus"], [w!"therefore"], [w!"indeed"], [w!"moreover"], [w!"furthermore"],
   [w!"in", w!"addition"], [w!"finally"], [w!"again"], [w!"conversely"], [w!"similarly"],
   [w!"in", w!"other", w!"words"], [w!"that", w!"is"], [w!"we", w!"have"], [w!"it", w!"follows", w!"that"],
   [w!"we", w!"obtain"], [w!"note", w!"that"], [w!"we", w!"see", w!"that"]]

/-- Discourse markers have no content of their own (`For the minimum` sets a topic). -/
inductive Topic where
  | none | maximum | minimum
  deriving DecidableEq, Repr, Lean.ToExpr

def marker (cs : List Chunk) : Topic × List Chunk :=
  match kw [w!"for", w!"the", w!"minimum"] cs with
  | some r => (.minimum, optPunct 44 r)
  | none =>
  match kw [w!"for", w!"the", w!"maximum"] cs with
  | some r => (.maximum, optPunct 44 r)
  | none =>
    -- up to two markers in a row (`Hence, it follows that`)
    let one (cs : List Chunk) : Option (List Chunk) := wMarkers.findSome? fun m => (kw m cs).map (optPunct 44 ·)
    let tryAll (_ : List (List Codes)) : Topic × List Chunk :=
      match one cs with
      | some r => (.none, (one r).getD r)
      | none => (.none, cs)
    -- a topic in words only: `For the second region, whose boundary has two regimes,`
    match kw [w!"for", w!"the"] cs with
    | some r =>
      match wordsTo r with
      | some r' => (.none, r')
      | none => tryAll wMarkers
    | none =>
      -- a purpose: `To describe the supporting lines of the region,`
      match purpose cs with
      | some r => (.none, r)
      | none => tryAll wMarkers
where
  /-- `To WORDS,` with at least two words. -/
  purpose (cs : List Chunk) : Option (List Chunk) := do
    let r ← kw [w!"to"] cs
    let ws := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
    if ws.length < 2 then none else
    match r.drop ws.length with
    | .p 44 :: r' => some r'
    | _ => none
  /-- Words up to a comma, then relative clauses `whose|which|where WORDS,`. -/
  wordsTo (cs : List Chunk) : Option (List Chunk) :=
    let ws := cs.takeWhile (fun c => match c with | .w _ => true | _ => false)
    if ws.isEmpty then none else
    match cs.drop ws.length with
    | .p 44 :: r =>
      match r with
      | .w v :: r' =>
        if v == w!"whose" || v == w!"which" || v == w!"where" then
          let ws' := r'.takeWhile (fun c => match c with | .w _ => true | _ => false)
          match r'.drop ws'.length with
          | .p 44 :: r'' => if ws'.isEmpty then none else some r''
          | _ => none
        else some r
      | _ => some r
    | _ => none

inductive Bind where
  | every (vars : List Codes) (dom : MT)
  | noun (np : List Chunk)
  | on (dom : MT)
  /-- `If $φ$, then …`: the free variables of `φ` range over the real numbers
  subject to `φ`. -/
  | ifCond (cond : MT)
  /-- `For $x\in A$ and $y\in B$,`. -/
  | many (bs : List Bind)
  deriving Repr, Inhabited

/-- Further `and $y\in B$` after a binder. -/
def moreAnd : Nat → List Chunk → List Bind → List Bind × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, cs, acc =>
    match (do
        let r ← kw [w!"and"] cs
        let (ts, r') ← mathChunk r
        let (vs, dom) ← binderMath ts
        some (Bind.every vs dom, r')) with
    | some (b, r) => moreAnd f r (b :: acc)
    | none => (acc.reverse, cs)

/-- Sentence-initial binders: `For every $x\in A$,` `For $x\in A$,` `For a NP,` `On $I$,`. -/
def binder (cs : List Chunk) : Option (Bind × List Chunk) :=
  match kw [w!"for", w!"every"] cs, kw [w!"for", w!"all"] cs with
  | some r, _ | none, some r => do
    let (ts, r') ← mathChunk r
    let (vs, dom) ← binderMath ts
    some (.every vs dom, r')
  | none, none =>
    match kw [w!"for", w!"a"] cs, kw [w!"for", w!"an"] cs with
    | some r, _ | none, some r =>
      let np := r.takeWhile (fun c => match c with | .p 44 => false | _ => true)
      some (.noun np, r.drop np.length)
    | none, none =>
      match kw [w!"for"] cs with
      | some r => do
        let (ts, r') ← mathChunk r
        let (vs, dom) ← binderMath ts
        match moreAnd 4 r' [] with
        | ([], _) => some (.every vs dom, r')
        | (bs, r'') => some (.many (.every vs dom :: bs), r'')
      | none =>
        match kw [w!"on"] cs with
        | some r => do
          let (m, r') ← formula r
          some (.on m, r')
        | none =>
          match kw [w!"if"] cs with
          | some r => do
            let (m, r') ← formula r
            some (.ifCond m, r')
          | none => none

inductive Subj where
  | math (m : MT)
  | its (name : List Codes)
  deriving Repr, Inhabited

inductive Obj where
  | math (m : MT)
  | named (name : List Codes) (m : Option MT)
  deriving Repr, Inhabited

inductive RelPart where
  | has (m : MT)
  | pred (phrase : List Codes) (obj : Obj)
  deriving Repr, Inhabited

inductive Clause where
  | fact (f : MT)
  | holds (f : MT)
  | exactlyOne (noun : List Codes) (v : Codes) (cond sat : MT)
  | onlyWith (s : Subj) (noun : List Codes) (conds : List MT)
  | every (vars : List Codes) (dom body : MT)
  | extremum (isMax : Bool) (fv : MT) (s : Subj) (rels : List RelPart)
  | increases (f dom cod : MT)
  | deriv (d : MT) (positive : Bool) (cond : MT)
  | noOther (noun : List Codes) (x : MT) (isMax : Bool)
  | pred (s : Subj) (phrase : List Codes) (obj : Obj)
  | sends (map f g : MT)
  | onlyAttains (x : MT)
  /-- `φ`, possibly `for every x∈A`, possibly `with equality only at x=a`. -/
  | scoped (f : MT) (vars : List Codes) (dom : Option MT) (equalityAt : Option MT)
  /-- `every NP satisfies|obeys φ`. -/
  | everyNP (np : List Chunk) (body : MT)
  /-- `the maximum V of F is attained only by S[, at which φ][, which RELS]`; without
  `of F` (`the minimum V only by S`), `F` is the function of the preceding extremum. -/
  | extremumOf (isMax : Bool) (value : MT) (f : Option MT) (s : Subj) (at_ : Option MT) (rels : List RelPart)
  /-- `both maps F and G are strictly increasing`. -/
  | increasing (maps : List MT)
  /-- `the first|second ranges over B`: the image of a map of the preceding sentence. -/
  | ranges (which : Nat) (target : MT)
  /-- `the maximum X [and the minimum Y] of F over all NOUNS $C$ with φ are each
  attained by exactly one NOUN`: each value is the extremum of `F` over the
  elements with `φ`, attained by exactly one of them. -/
  | extremaOver (items : List (Bool × MT)) (f : MT) (noun : List Codes) (v : Codes) (cond : MT)
  /-- `equality holds exactly on $S$` (after an inequality `a ≥ b` for every `x` in
  a domain): for every such `x`, `a = b` exactly when `x ∈ S`. -/
  | equalityOn (s : MT)
  /-- `equality holds exactly when $φ$`: for every `x`, `a = b ↔ φ`. -/
  | equalityWhen (φ : MT)
  /-- `if $φ$, CLAUSE`: the clause under the hypothesis `φ` about variables
  that are already bound. -/
  | ifThen (cond : MT) (c : Clause)
  /-- `$X$ is ADJ, ADJ and ADJ`: properties of a set of points of the plane
  (`compact`, `convex`, `centrally symmetric`) or of a function on its domain
  (`continuous`, `concave`, `strictly increasing`). -/
  | adjectives (s : MT) (adjs : List (List Codes))
  /-- `Both constants are sharp.`, `The bound is sharp.`: each inequality `a ≤ b` of
  the preceding claim about every element of a domain cannot be improved: for every
  `ε > 0`, some element has `b - a < ε`. -/
  | sharp
  /-- `$x$ is NAME[, NAME] and|or NAME`: notions the article defines (`disj`: `or`). -/
  | notions (s : MT) (names : List (List Codes)) (disj : Bool)
  /-- `every NP is NAME [and|or NAME]`. -/
  | everyIs (np : List Chunk) (names : List (List Codes)) (disj : Bool)
  /-- `$φ$ if and only if $ψ$`. -/
  | iff (p q : MT)
  /-- `[the WORDS] $X$ is at most [the WORDS] $Y$` (at least, less than, greater than,
  equal to); either side may define its symbol (`the geometric mean $G\coloneqq\sqrt{ab}$`). -/
  | compare (lhs : MT) (rel : Rel) (rhs : MT)
  deriving Repr, Inhabited

/-- A clause with the citations that justify it, its own binders
(`…, and for $b\in B$, CLAUSE`) and the definitions of a trailing `where`
(`…, where $g(x)\coloneqq x-1$`). -/
structure CClause where
  cites : List Codes
  clause : Clause
  binds : List Bind := []
  defs : List MT := []
  deriving Repr, Inhabited

def subj (cs : List Chunk) : Option (Subj × List Chunk) :=
  match cs with
  | .m _ :: _ => do let (m, r) ← formula cs; some (.math m, r)
  | .w v :: r =>
    if v == w!"its" then
      let ws := r.takeWhile (fun c => match c with
        | .w u => !([w!"is", w!"which", w!"attains"].contains u) | _ => false)
      some (.its (ws.filterMap (fun c => match c with | .w w => some w | _ => none)), r.drop ws.length)
    else none
  | _ => none

def obj (cs : List Chunk) : Option (Obj × List Chunk) :=
  match cs with
  | .m _ :: _ => do let (m, r) ← formula cs; some (.math m, r)
  | .w v :: r =>
    if v == w!"the" then
      let name := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      let words := name.filterMap fun c => match c with | .w w => some w | _ => none
      let r' := r.drop name.length
      match formula r' with
      | some (m, r'') => some (.named words (some m), r'')
      | none => some (.named words none, r')
    else none
  | _ => none

/-- `has $φ$` or `is <words> of OBJ` (relative clause parts joined by `and`). -/
def relParts : Nat → List Chunk → List RelPart → Option (List RelPart × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    let one : Option (RelPart × List Chunk) :=
      match kw [w!"has"] cs with
      | some r => do let (m, r') ← formula r; some (.has m, r')
      | none => do
        let r ← kw [w!"is"] cs
        let (phrase, r') ← wordsUntil [w!"of"] 8 r []
        let r'' ← kw [w!"of"] r'
        let (o, r3) ← obj r''
        some (.pred phrase o, r3)
    match one with
    | some (p, r) =>
      match kw [w!"and"] r with
      | some r' => relParts f r' (p :: acc)
      | none => some ((p :: acc).reverse, r)
    | none => none

def nounWords (cs : List Chunk) : Option (List Codes × List Chunk) :=
  wordsUntil [w!"with", w!"other"] 6 cs []

/-- A formula or a display. -/
def formulaOrDisplay (cs : List Chunk) : Option (MT × List Chunk) :=
  formula cs <|> (do let (m, _, r) ← display cs; some (m, r))

/-- Ordinal words for anaphora (`the first`, `the second`). -/
def ordinal (w : Codes) : Option Nat :=
  if w == w!"first" then some 0 else if w == w!"second" then some 1
  else if w == w!"third" then some 2 else none

/-- Map formulas joined by `and` (`$f$ and $g$`). -/
def mapList : Nat → List Chunk → List MT → Option (List MT × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (m, r) ← formula cs
    match kw [w!"and"] r with
    | some r' => mapList f r' (m :: acc)
    | none => some ((m :: acc).reverse, r)

/-- Adjectives of the core: shapes of sets of the plane and properties of functions. -/
def wAdjectives : List (List Codes) :=
  [[w!"compact"], [w!"convex"], [w!"centrally", w!"symmetric"], [w!"continuous"], [w!"concave"],
   [w!"strictly", w!"increasing"]]

def adjective (cs : List Chunk) : Option (List Codes × List Chunk) :=
  wAdjectives.findSome? fun a => (kw a cs).map (a, ·)

/-- `ADJ, ADJ and ADJ`. -/
def adjectiveList : Nat → List Chunk → List (List Codes) → Option (List (List Codes) × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (a, r) ← adjective cs
    let acc := a :: acc
    let next := (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r
    match next with
    | some r' =>
      if (adjective r').isSome then adjectiveList f r' acc else some (acc.reverse, r)
    | none => some (acc.reverse, r)

/-- Words that end the name of a notion. -/
def notionStops : List Codes :=
  [w!"if", w!"and", w!"or", w!"for", w!"of", w!"on", w!"by", w!"with", w!"then", w!"is", w!"are",
   w!"in", w!"to", w!"at", w!"from", w!"whenever", w!"where", w!"when", w!"since", w!"a", w!"an",
   w!"the", w!"every", w!"each", w!"all", w!"called", w!"not", w!"so", w!"whereas", w!"as", w!"both",
   w!"either", w!"neither"]

/-- The name of a notion: words and hyphens (`left-tail decreasing`, the hyphen as `-`). -/
def nameWords : Nat → List Chunk → List Codes → List Codes × List Chunk
  | 0, cs, acc => (acc.reverse, cs)
  | f + 1, .w v :: cs, acc =>
    if notionStops.contains v then (acc.reverse, .w v :: cs) else nameWords f cs (v :: acc)
  | f + 1, .p 45 :: cs, acc =>
    if acc.isEmpty then ([], .p 45 :: cs) else nameWords f cs (w!"-" :: acc)
  | _, cs, acc => (acc.reverse, cs)

/-- The end of a clause: the period, a comma, or a trailing citation. -/
def clauseEnd (cs : List Chunk) : Bool :=
  isEnd cs || (punct 44 cs).isSome || (kw [w!"by"] cs >>= cite).isSome

/-- `NAME[, NAME] and|or NAME`, ending a clause; `or` makes a disjunction. -/
def notionList (cs : List Chunk) : Option (List (List Codes) × Bool × List Chunk) := do
  let (n1, r1) := nameWords 8 cs []
  if n1.isEmpty then none else
  match kw [w!"and"] r1 <|> kw [w!"or"] r1 with
  | some r2 =>
    let disj := (kw [w!"or"] r1).isSome
    let (n2, r3) := nameWords 8 r2 []
    if n2.isEmpty || !clauseEnd r3 then none else some ([n1, n2], disj, r3)
  | none => if clauseEnd r1 then some ([n1], false, r1) else none

/-- `[the WORDS] $X$`, possibly `$X\coloneqq e$`: a term named by a phrase. -/
def namedTerm (cs : List Chunk) : Option (MT × List Chunk) :=
  let r := match kw [w!"the"] cs with
    | some r' => r'.dropWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
    | none => cs
  formula r

/-- `is at most`, `is at least`, `is less than`, `is greater than`, `is equal to`,
`does not exceed`, `equals`. -/
def compareRel (cs : List Chunk) : Option (Rel × List Chunk) :=
  ((kw [w!"is", w!"at", w!"most"] cs).map (.le, ·)) <|> ((kw [w!"does", w!"not", w!"exceed"] cs).map (.le, ·)) <|>
  ((kw [w!"is", w!"at", w!"least"] cs).map (.ge, ·)) <|> ((kw [w!"is", w!"less", w!"than"] cs).map (.lt, ·)) <|>
  ((kw [w!"is", w!"smaller", w!"than"] cs).map (.lt, ·)) <|> ((kw [w!"is", w!"greater", w!"than"] cs).map (.gt, ·)) <|>
  ((kw [w!"is", w!"larger", w!"than"] cs).map (.gt, ·)) <|> ((kw [w!"is", w!"equal", w!"to"] cs).map (.eq, ·)) <|>
  ((kw [w!"equals"] cs).map (.eq, ·))

/-- One clause, without its citations. Must be followed by a clause boundary. -/
def clause (cs : List Chunk) : Option (Clause × List Chunk) :=
  -- It holds that DISPLAY
  match kw [w!"it", w!"holds", w!"that"] cs with
  | some r => do let (m, _, r') ← display r; some (.holds m, r')
  | none =>
  -- $φ$ if and only if $ψ$
  match (do
      let (p, r) ← formula cs
      let r1 ← kw [w!"if", w!"and", w!"only", w!"if"] r
      let (q, r2) ← formula r1
      some (Clause.iff p q, r2)) with
  | some res => some res
  | none =>
  -- equality holds exactly on $S$ | when $φ$; it holds exactly on $S$
  -- [both|the|this|these|all] constants|bounds|inequalities are sharp
  match (do
      let r0 := ((kw [w!"both"] cs <|> kw [w!"the"] cs <|> kw [w!"this"] cs <|> kw [w!"these"] cs <|>
        kw [w!"all"] cs).getD cs)
      let r1 ← [w!"constants", w!"constant", w!"bounds", w!"bound", w!"inequalities", w!"inequality",
        w!"estimates", w!"estimate"].findSome? (fun w => kw [w] r0)
      let r2 ← kw [w!"are", w!"sharp"] r1 <|> kw [w!"is", w!"sharp"] r1
      some (Clause.sharp, r2)) with
  | some res => some res
  | none =>
  -- $X$ is ADJ, ADJ and ADJ
  match (do
      let (m, r) ← formula cs
      let r1 ← kw [w!"is"] r
      let (adjs, r2) ← adjectiveList 6 r1 []
      some (Clause.adjectives m adjs, r2)) with
  | some res => some res
  | none =>
  -- $X$ is NAME [and|or NAME]: notions of the article
  match (do
      let (m, r) ← formula cs
      let r1 ← kw [w!"is"] r
      let (names, disj, r2) ← notionList r1
      some (Clause.notions m names disj, r2)) with
  | some res => some res
  | none =>
  match (do
      let r ← kw [w!"equality", w!"holds", w!"exactly"] cs <|> kw [w!"it", w!"holds", w!"exactly"] cs
      match kw [w!"on"] r with
      | some r1 => do let (m, r2) ← formula r1; some (Clause.equalityOn m, r2)
      | none => do
        let r1 ← kw [w!"when"] r
        let (m, r2) ← formula r1
        some (Clause.equalityWhen m, r2)) with
  | some res => some res
  | none =>
  -- [both] [the] [parameter] maps $f$ and $g$ are strictly increasing
  match (do
      let r0 := (kw [w!"both"] cs).getD cs
      let r1 := (kw [w!"the"] r0).getD r0
      let r2 := (kw [w!"parameter"] r1).getD r1
      let r3 ← kw [w!"maps"] r2 <|> kw [w!"map"] r2
      let (ms, r4) ← mapList 4 r3 []
      let r5 ← kw [w!"are", w!"strictly", w!"increasing"] r4 <|> kw [w!"is", w!"strictly", w!"increasing"] r4
      some (Clause.increasing ms, r5)) with
  | some res => some res
  | none =>
  -- the first|second ranges over $B$
  match (do
      let r ← kw [w!"the"] cs
      match r with
      | .w o :: r1 => do
        let k ← ordinal o
        let r2 ← kw [w!"ranges", w!"over"] r1
        let (b, r3) ← formula r2
        some (Clause.ranges k b, r3)
      | _ => none) with
  | some res => some res
  | none =>
  -- the maximum X [and the minimum Y] of F over all NOUNS $C$ with φ are each attained by exactly one NOUN
  match (do
      let item (r : List Chunk) : Option ((Bool × MT) × List Chunk) := do
        let r1 ← kw [w!"the"] r
        let (isMax, r2) ← (kw [w!"maximum"] r1).map (true, ·) <|> (kw [w!"minimum"] r1).map (false, ·)
        let (x, r3) ← formula r2
        some ((isMax, x), r3)
      let (i1, r1) ← item cs
      let (items, r2) : List (Bool × MT) × List Chunk := match (kw [w!"and"] r1).bind item with
        | some (i2, r') => ([i1, i2], r')
        | none => ([i1], r1)
      let r3 ← kw [w!"of"] r2
      let (f, r4) ← formula r3
      let r5 ← kw [w!"over", w!"all"] r4
      let ws := r5.takeWhile (fun (c : Chunk) => match c with | .w _ => true | _ => false)
      let noun := ws.filterMap (fun (c : Chunk) => match c with | .w w => some w | _ => none)
      let (vt, r6) ← mathChunk (r5.drop ws.length)
      let v ← match vt with | [.id v] => some v | _ => none
      let r7 ← kw [w!"with"] r6
      let (cond, r8) ← formula r7
      let r9 ← kw [w!"are", w!"each", w!"attained", w!"by", w!"exactly", w!"one"] r8 <|>
        kw [w!"is", w!"attained", w!"by", w!"exactly", w!"one"] r8
      let ws2 := r9.takeWhile (fun (c : Chunk) => match c with | .w _ => true | _ => false)
      if ws2.isEmpty then none else some (Clause.extremaOver items f noun v cond, r9.drop ws2.length) :
        Option (Clause × List Chunk)) with
  | some res => some res
  | none =>
  -- exactly one N $x$ with $φ$ satisfies $ψ$
  match kw [w!"exactly", w!"one"] cs with
  | some r => do
    let (noun, r1) ← wordsUntil [] 6 r [] <|> (do
      let words := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (words.filterMap (fun c => match c with | .w w => some w | _ => none), r.drop words.length))
    let (vt, r2) ← mathChunk r1
    let v ← match vt with | [.id v] => some v | _ => none
    let r3 ← kw [w!"with"] r2
    let (cond, r4) ← formula r3
    let r5 ← kw [w!"satisfies"] r4
    let (sat, r6) ← formula r5
    some (.exactlyOne noun v cond sat, r6)
  | none =>
  -- Every $x\in A$ satisfies $φ$ | Every NP satisfies|obeys φ
  match kw [w!"every"] cs with
  | some r =>
    (do
      let (ts, r1) ← mathChunk r
      let (vs, dom) ← binderMath ts
      let r2 ← kw [w!"satisfies"] r1 <|> kw [w!"obeys"] r1
      let (body, r3) ← formulaOrDisplay r2
      some (.every vs dom body, r3)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"satisfies", w!"obeys"] r []
      let r2 ← kw [w!"satisfies"] r1 <|> kw [w!"obeys"] r1
      let (body, r3) ← formulaOrDisplay r2
      some (.everyNP np body, r3)) <|>
    (do
      let (np, r1) ← chunksUntil [w!"is"] r []
      let r2 ← kw [w!"is"] r1
      let (names, disj, r3) ← notionList r2
      some (.everyIs np names disj, r3))
  | none =>
  -- The maximum/minimum $F=m$ is attained only by SUBJ[, which REL]
  match kw [w!"the", w!"maximum"] cs, kw [w!"the", w!"minimum"] cs with
  | some r, _ | none, some r => do
    let isMax := (kw [w!"the", w!"maximum"] cs).isSome
    let (fv, r1) ← formula r
    -- `the maximum V of F is attained only by …`, or (after a maximum) `the minimum V only by …`
    let (ofF, r1) := match kw [w!"of"] r1 >>= formula with
      | some (fm, r') => (some fm, r')
      | none => (none, r1)
    let gapped := ofF.isNone && (kw [w!"only", w!"by"] r1).isSome
    let r2 ← kw [w!"is", w!"attained", w!"only", w!"by"] r1 <|> (if gapped then kw [w!"only", w!"by"] r1 else none)
    let (s, r3) ← subj r2
    let (atw, r3) := match punct 44 r3 >>= kw [w!"at", w!"which"] >>= formula with
      | some (m, r') => (some m, r')
      | none => (none, r3)
    let (rels, r5) ← match punct 44 r3 >>= kw [w!"which"] with
      | some r4 => relParts 4 r4 []
      | none => some ([], r3)
    if ofF.isSome || gapped || atw.isSome then some (.extremumOf isMax fv ofF s atw rels, r5)
    else some (.extremum isMax fv s rels, r5)
  | none, none =>
  -- its derivative $d$ is positive/negative for $φ$
  match kw [w!"its", w!"derivative"] cs with
  | some r => do
    let (d, r1) ← formula r
    let r2 ← kw [w!"is"] r1
    let (positive, r3) ← (match kw [w!"positive"] r2, kw [w!"negative"] r2 with
      | some r', _ => some (true, r') | none, some r' => some (false, r') | _, _ => none :
      Option (Bool × List Chunk))
    let r4 ← kw [w!"for"] r3
    let (cond, r5) ← formula r4
    some (.deriv d positive cond, r5)
  | none =>
  -- no N other than $x$ attains the maximum/minimum
  match kw [w!"no"] cs with
  | some r => do
    let (noun, r1) ← nounWords r
    let r2 ← kw [w!"other", w!"than"] r1
    let (x, r3) ← formula r2
    let r4 ← kw [w!"attains", w!"the"] r3
    let (isMax, r5) ← (match kw [w!"maximum"] r4, kw [w!"minimum"] r4 with
      | some r', _ => some (true, r') | none, some r' => some (false, r') | _, _ => none :
      Option (Bool × List Chunk))
    some (.noOther noun x isMax, r5)
  | none =>
  -- the map $λ$ sends $F$ to $G$
  match kw [w!"the", w!"map"] cs with
  | some r => do
    let (mp, r1) ← formula r
    let r2 ← kw [w!"sends"] r1
    let (fm, r3) ← formula r2
    let r4 ← kw [w!"to"] r3
    let (gm, r5) ← formula r4
    some (.sends mp fm gm, r5)
  | none =>
  -- only $x$ attains it
  match kw [w!"only"] cs with
  | some r => do
    let (x, r1) ← formula r
    let r2 ← kw [w!"attains", w!"it"] r1
    some (.onlyAttains x, r2)
  | none =>
  -- DISPLAY (and DISPLAY)*
  match display cs with
  | some (m, _, r) =>
    let rec more : Nat → List MT → List Chunk → Option (List MT × List Chunk)
      | 0, _, _ => none
      | g + 1, acc, rest =>
        match kw [w!"and"] rest >>= display with
        | some (m', _, r') => more g (m' :: acc) r'
        | none => some (acc.reverse, rest)
    match more 6 [m] r with
    | some ([m], r') => some (.fact m, r')
    | some (ms, r') => some (.fact (.conj ms), r')
    | none => none
  | none =>
  -- [the WORDS] $X$ is at most [the WORDS] $Y$
  match (do
      let (l, r) ← namedTerm cs
      let (rel, r1) ← compareRel r
      let (rr, r2) ← namedTerm r1
      some (Clause.compare l rel rr, r2)) with
  | some res => some res
  | none =>
  -- SUBJ is the only N with $φ$ (and $ψ$)* | SUBJ is <words> of OBJ
  match subj cs with
  | some (s, r) =>
    match kw [w!"is", w!"the", w!"only"] r with
    | some r1 => do
      let (noun, r2) ← wordsUntil [w!"with"] 6 r1 []
      let r3 ← kw [w!"with"] r2
      let (c1, r4) ← formula r3
      match kw [w!"and"] r4 >>= formula with
      | some (c2, r5) => some (.onlyWith s noun [c1, c2], r5)
      | none => some (.onlyWith s noun [c1], r4)
    | none =>
    match kw [w!"is"] r with
    | some r1 =>
      match wordsUntil [w!"of"] 8 r1 [] with
      | some (phrase, r2) => do
        let r3 ← kw [w!"of"] r2
        let (o, r4) ← obj r3
        some (.pred s phrase o, r4)
      | none => none
    | none =>
    match s, kw [w!"increases", w!"bijectively", w!"from"] r with
    | .math f, some r1 => do
      let (a, r2) ← formula r1
      let r3 ← kw [w!"onto"] r2
      let (b, r4) ← formula r3
      some (.increases f a b, r4)
    | _, _ =>
    -- $φ$ [for every $x\in A$] [, with equality only at $x=a$]
    match s with
    | .math f =>
      let (vars, dom, r1) := match kw [w!"for", w!"every"] r <|> kw [w!"for", w!"all"] r with
        | some r' => match mathChunk r' with
          | some (ts, r'') => match binderMath ts with
            | some (vs, d) => (vs, some d, r'')
            | none => ([], none, r)
          | none => ([], none, r)
        | none => ([], none, r)
      match punct 44 r1 >>= kw [w!"with", w!"equality", w!"only", w!"at"] with
      | some r2 => do
        let (at_, r3) ← formula r2
        some (.scoped f vars dom (some at_), r3)
      | none => some (.scoped f vars dom none, r1)
    | _ => none
  | none => none

/-- A clause with its leading citations: `By CITE, ...`, `CITE gives ...`, trailing `by CITE`. -/
def cclause (cs : List Chunk) : Option (CClause × List Chunk) :=
  let (pre, r0) : List Codes × List Chunk :=
    match kw [w!"by"] cs >>= cite with
    | some (l, r) => ([l], optPunct 44 r)
    | none => ([], cs)
  -- CITE gives $φ$
  match cite r0 with
  | some (l, r1) =>
    match kw [w!"gives"] r1 with
    | some r2 => do
      let (m, r3) ← formula r2
      some (⟨pre ++ [l], .fact m, [], []⟩, r3)
    | none => none
  | none => do
    -- a hypothesis about bound variables: `if $φ$, CLAUSE`
    let (hyp, r0) : Option MT × List Chunk :=
      match (do
          let r ← kw [w!"if"] r0
          let (m, r') ← formula r
          let r'' ← punct 44 r'
          some (m, r'')) with
      | some (m, r) => (some m, r)
      | none => (none, r0)
    -- a clause's own binder: `for $b\in B$, CLAUSE`
    let (bs, r0) : List Bind × List Chunk :=
      match kw [w!"for"] r0 >>= mathChunk with
      | some (ts, r) =>
        match binderMath ts, punct 44 r with
        | some (vs, d), some r' => ([.every vs d], r')
        | _, _ => ([], r0)
      | none => ([], r0)
    let (c, r1) ← clause r0
    let c := match hyp with | some m => Clause.ifThen m c | none => c
    let post := (kw [w!"by"] r1 >>= cite) <|> (kw [w!"as", w!"specified", w!"in"] r1 >>= cite)
    let (cites, r2) := match post with
      | some (l, r2) => (pre ++ [l], r2)
      | none => (pre, r1)
    -- `…, where $g(x)\coloneqq x-1$ [and $h\coloneqq …$]`
    match punct 44 r2 >>= kw [w!"where"] with
    | some r3 => do
      let (ds, r4) ← whereDefs 4 r3 []
      some (⟨cites, c, bs, ds⟩, r4)
    | none => some (⟨cites, c, bs, []⟩, r2)
where
  /-- Definitions `$X\coloneqq e$` separated by `,` and `and`. -/
  whereDefs : Nat → List Chunk → List MT → Option (List MT × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (m, r) ← formula cs
      match m with
      | .chain _ ((.defeq, _) :: _) =>
        let acc := m :: acc
        match (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r with
        | some r' =>
          match formula r' with
          | some (.chain _ ((.defeq, _) :: _), _) => whereDefs f r' acc
          | _ => some (acc.reverse, r)
        | none => some (acc.reverse, r)
      | _ => none

/-- Clauses separated by `, and` / `, so`, ending with the final period. -/
def clauses : Nat → List Chunk → List CClause → Option (List CClause)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (c, r) ← cclause cs
    -- a reason in words only (`…, since the square root is injective.`) asserts nothing
    let r := match punct 44 r >>= kw [w!"since"] with
      | some r' =>
        let ws := r'.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
        if !ws.isEmpty && isEnd (r'.drop ws.length) then r'.drop ws.length else r
      | none => r
    if isEnd r then some (c :: acc).reverse
    else
      -- `, and`, `, so`, `, whereas`, or `and` between two formulas, or `,` before a
      -- formula (`$φ$, $ψ$ and $χ$`)
      let next := (do
        let r' ← punct 44 r
        kw [w!"and"] r' <|> kw [w!"so"] r' <|> kw [w!"whereas"] r' <|>
          (match r' with | .m _ :: _ => some r' | _ => none)) <|> kw [w!"and"] r
      match next with
      | some r'' => clauses f r'' (c :: acc)
      | none => none

/-- A definition item `the NAME [of $x$ ...] is DEF`. -/
structure DefItem where
  name : List Codes
  defn : MT
  labels : List Codes
  deriving Repr, Inhabited

def defItem (cs : List Chunk) : Option (DefItem × List Chunk) := do
  let r := (kw [w!"the"] cs).getD cs
  -- name words, possibly with `of $x$`, until `is`
  let rec nameWords : Nat → List Chunk → List Codes → Option (List Codes × List Chunk)
    | 0, _, _ => none
    | _ + 1, [], _ => none
    | g + 1, c :: rest, acc =>
      match c with
      | .w v => if v == w!"is" || v == w!"are" then some (acc.reverse, rest) else nameWords g rest (v :: acc)
      | .m _ => nameWords g rest acc
      | _ => none
  let (name, r1) ← nameWords 16 r []
  match display r1 with
  | some (m, ls, r2) => some (⟨name, m, ls⟩, r2)
  | none => do
    let (m, r2) ← formula r1
    some (⟨name, m, []⟩, r2)

/-- Trailing bibliographic remarks without mathematical content. -/
def trailer (cs : List Chunk) : List Chunk :=
  let cs' := optPunct 44 cs
  match kw [w!"as", w!"given", w!"in"] cs' <|> kw [w!"see"] cs' with
  | some (.r .cite _ :: r) => r
  | _ =>
    match kw [w!"from"] cs' >>= cite with
    | some (_, r) => r
    | none => cs

/-- A piece of a definition `define $f:A\to B$ by PIECES`: a defining formula
(inline or displayed, possibly with its domain), or `on $D$, parametrically by
DISPLAY`. -/
inductive DefPiece where
  | formula (m : MT)
  | param (dom : MT) (m : MT)
  deriving Repr, Inhabited

/-- Monotonicity of a map: `non-increasing`, `non-decreasing`, `strictly increasing`,
`strictly decreasing`. (A plain `increasing` is ambiguous between the first two
readings, so the grammar does not read it.) -/
inductive Mono where
  | nonincreasing | nondecreasing | increasing | decreasing
  deriving Repr, Inhabited, DecidableEq

/-- The condition of a notion the article defines. -/
inductive NotionCond where
  /-- `$φ$ [for all $u,v\in A$]` -/
  | formula (f : MT) (binds : List Bind)
  /-- `[for every $v\in A$,] the map $x\mapsto e$[, $x\in D$,] is non-increasing` -/
  | mono (binds : List Bind) (map : MT) (mono : Mono)
  deriving Repr, Inhabited

inductive Sent where
  | defClass (sym : MT) (plural : List Codes) (np : List Chunk)
  | defIs (bind : Bind) (items : List DefItem)
  | defReads (bind : Bind) (name : List Codes) (sig : MT) (disp : MT) (labels : List Codes)
  | defBy (sig : MT) (pieces : List DefPiece) (labels : List Codes) (observe : Option (MT × List Codes × MT))
  | denotedBy (name : List Chunk) (sym : MT)
  | letDenote (bind : Bind) (sym : MT) (np : List Chunk)
  /-- `For B, [set $X\coloneqq e$ and] let $S$ be NP[, where $sig$ is given by DISPLAY]`. -/
  | defSteps (bind : Bind) (sets : List MT) (sym : MT) (np : List Chunk) (whereDef : Option (MT × MT × List Codes))
  | weSay (subj : List Chunk) (phrase : List Codes) (obj : List Chunk) (cond : MT)
      (vars : List Codes) (dom : MT)
  | claims (topic : Topic) (binds : List Bind) (cs : List CClause)
  /-- `Set $X\coloneqq e$.`, `Define DISPLAY.`, `The NAME is $X\coloneqq e$.`, and
  under a binder `For B, set $f(x)\coloneqq e$.`: definitions of constants (or of
  functions of the binder's variable), possibly several, each `\coloneqq`. -/
  | constDefs (bind : Option Bind) (defs : List MT) (labels : List Codes)
  /-- `fix $B$ [and define|set|put DEFS]`: the binder stays fixed for the following
  sentences of the section (its variable names the same object until the section
  ends or the variable is fixed again); the definitions are made under it. -/
  | fix (bind : Bind) (defs : List MT) (labels : List Codes)
  /-- `Let $x\in A$.` in a result: `x` is bound for the rest of the result. -/
  | assume (bind : Bind)
  /-- Functions given by a value at one point and their derivative:
  `[For B, set DEFS, and] define continuous functions $f,g:A\to\R$ by $f(a)=c$, …,
  and DISPLAY` or `Let $f,g:A\to\R$ be continuous, normalized by $f(a)=c$ and …,
  with derivatives DISPLAY`, where the display gives `f'(x)` (piecewise). -/
  | defDeriv (bind : Option Bind) (sets : List MT) (names : List MT) (dom cod : MT) (anchors : List MT)
      (derivs : MT) (labels : List Codes)
  /-- `We call a NOUN $x$ NAME [(ABBR)] if COND.`, `[A NOUN] $x$ is called NAME [(ABBR)]
  if COND.`, `$x$ is NAME (ABBR) if COND.`: a notion of the article. `subj` is the noun
  phrase with its variable, or the variable alone (the subject of the previous notion). -/
  | defNotion (subj : List Chunk) (name : List Codes) (abbr : List Codes) (cond : NotionCond)
  /-- `Let $C$ be a NP[, and let $u,v\in A$][, and let $X\coloneqq e$, …].`, `Let
  $a,b\in A$, and let $X\coloneqq e$.`: variables of the rest of the result or proof,
  and definitions local to it. -/
  | assumeAll (binds : List Bind) (defs : List MT)
  deriving Repr, Inhabited

/-- `$f,g:A\to B$`: several names with one signature. -/
def namesSig (ts : List MTok) : Option (List MT × MT × MT) := do
  let i ← ts.findIdx? (· == .sym 58)
  let j ← ts.findIdx? (· == .cmd w!"to")
  if j < i then none else
  let rec split : List MTok → List MTok → List (List MTok) → List (List MTok)
    | [], cur, acc => (cur.reverse :: acc).reverse
    | t :: rest, cur, acc => if t == .sym 44 then split rest [] (cur.reverse :: acc) else split rest (t :: cur) acc
  let names ← (split (ts.take i) [] []).mapM Math.parseFormula
  let dom ← Math.parseFormula ((ts.drop (i + 1)).take (j - i - 1))
  let cod ← Math.parseFormula (ts.drop (j + 1))
  some (names, dom, cod)

/-- Formulas separated by `,`, `, and` or `and` (the values of functions at points). -/
def anchorList : Nat → List Chunk → List MT → Option (List MT × List Chunk)
  | 0, _, _ => none
  | f + 1, cs, acc =>
    match formula cs with
    | some (m, r) =>
      let r' := (punct 44 r).getD r
      let r'' := (kw [w!"and"] r').getD r'
      anchorList f r'' (m :: acc)
    | none => if acc.isEmpty then none else some (acc.reverse, cs)

/-- A fixed variable: `$b\in B$`, or a condition `$\kappa>0$`. -/
def fixBinder (ts : List MTok) : Option Bind :=
  match binderMath ts with
  | some (vs, d) => some (.every vs d)
  | none => (Math.parseFormula ts).map Bind.ifCond

def isDefeq : MT → Bool
  | .chain _ ((.defeq, _) :: _) => true
  | _ => false

/-- Definitions joined by `,` and `and`, inline or displayed (a display may hold
several, separated by `\qquad`). -/
def defList : Nat → List Chunk → List MT → List Codes → Option (List MT × List Codes × List Chunk)
  | 0, _, _, _ => none
  | f + 1, cs, acc, ls => do
    let (ms, ls', r) ← (do let (m, ls', r) ← display cs; some (m, ls', r)) <|>
      (do let (m, r) ← formula cs; some (m, [], r))
    let items := match ms with | .conj xs => xs | m => [m]
    let acc := acc ++ items
    let ls := ls ++ ls'
    let next := (punct 44 r >>= fun r' => (kw [w!"and"] r').getD r' |> some) <|> kw [w!"and"] r
    match next with
    | some r' =>
      match defList f r' acc ls with
      | some res => some res
      | none => some (acc, ls, r)
    | none => some (acc, ls, r)

def constDefsOf (b : Option Bind) (cs : List Chunk) : Option Sent := do
  let (items, ls, r) ← defList 6 cs [] []
  if isEnd (trailer r) && !items.isEmpty && items.all isDefeq then some (.constDefs b items ls) else none

/-- `class of [all]`, `set of [all]`. -/
def classOf (cs : List Chunk) : Option (List Chunk) := do
  let r ← kw [w!"class", w!"of"] cs <|> kw [w!"set", w!"of"] cs
  some ((kw [w!"all"] r).getD r)

/-- `NOUN $x$`, the noun phrase of a notion's subject with its variable, or `$x$`. -/
def nounVar (cs : List Chunk) : Option (List Chunk × List Chunk) :=
  let ws := cs.takeWhile (fun c => match c with
    | .w v => !notionStops.contains v
    | .p 45 => true
    | _ => false)
  match cs.drop ws.length with
  | .m [.id v] :: r => some (ws ++ [.m [.id v]], r)
  | _ => none

/-- `NAME [(ABBR)]`. -/
def nameAbbr (cs : List Chunk) : Option (List Codes × List Codes × List Chunk) := do
  let (name, r) := nameWords 8 cs []
  if name.isEmpty then none else
  match punct 40 r with
  | some r1 => do
    let (abbr, r2) := nameWords 4 r1 []
    let r3 ← punct 41 r2
    if abbr.isEmpty then none else some (name, abbr, r3)
  | none => some (name, [], r)

/-- `non-increasing`, `non-decreasing`, `strictly increasing`, `strictly decreasing`. -/
def monoWord (cs : List Chunk) : Option (Mono × List Chunk) :=
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"increasing"]).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"nonincreasing"] cs).map (Mono.nonincreasing, ·)) <|>
  ((kw [w!"non"] cs >>= punct 45 >>= kw [w!"decreasing"]).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"nondecreasing"] cs).map (Mono.nondecreasing, ·)) <|>
  ((kw [w!"strictly", w!"increasing"] cs).map (Mono.increasing, ·)) <|>
  ((kw [w!"strictly", w!"decreasing"] cs).map (Mono.decreasing, ·))

/-- `for every|all|each $x\in A$`. -/
def forBinder (cs : List Chunk) : Option (Bind × List Chunk) := do
  let r ← kw [w!"for", w!"every"] cs <|> kw [w!"for", w!"all"] cs <|> kw [w!"for", w!"each"] cs
  let (ts, r1) ← mathChunk r
  let (vs, d) ← binderMath ts
  some (.every vs d, r1)

/-- The condition of a notion: `[, for every $v\in A$,] the map M[,] is MONO`, or
`$φ$ [for all $x\in A$]`. -/
def notionCond (cs : List Chunk) : Option NotionCond :=
  let cs := optPunct 44 cs
  (do
    let (bs, r) : List Bind × List Chunk := match forBinder cs with
      | some (b, r') => match punct 44 r' with
        | some r'' => ([b], r'')
        | none => ([], cs)
      | none => ([], cs)
    let r1 ← kw [w!"the", w!"map"] r <|> kw [w!"the", w!"function"] r
    let (m, r2) ← (display r1).map (fun (m, _, r') => (m, r')) <|> formula r1
    let r3 ← kw [w!"is"] (optPunct 44 r2)
    let (mono, r4) ← monoWord r3
    if isEnd r4 then some (NotionCond.mono bs m mono) else none) <|>
  (do
    let (φ, r1) ← formula cs
    if isEnd r1 then some (NotionCond.formula φ []) else do
    let (b, r2) ← forBinder r1
    if isEnd r2 then some (NotionCond.formula φ [b]) else none)

/-- A notion defined in the text: `We call a NOUN $x$ NAME [(ABBR)] if COND.`,
`[A NOUN] $x$ is called NAME [(ABBR)] if COND.`, `[A NOUN] $x$ is NAME [(ABBR)] if COND.` -/
def notionDef (cs : List Chunk) : Option Sent :=
  let article (r : List Chunk) := (kw [w!"a"] r <|> kw [w!"an"] r).getD r
  (do
    let r ← kw [w!"we", w!"call"] cs
    let (np, r1) ← nounVar (article r)
    let (name, abbr, r2) ← nameAbbr r1
    let r3 ← kw [w!"if"] r2
    let cond ← notionCond r3
    some (.defNotion np name abbr cond)) <|>
  (do
    let (np, r1) ← nounVar (article cs)
    let r2 ← kw [w!"is", w!"called"] r1 <|> kw [w!"is", w!"said", w!"to", w!"be"] r1 <|> kw [w!"is"] r1
    let (name, abbr, r3) ← nameAbbr r2
    let r4 ← kw [w!"if"] r3
    let cond ← notionCond r4
    some (.defNotion np name abbr cond))

/-- `$x\in A$`, or `$C$ be a|an NP`: the variable of a `let`. -/
def letBinder (cs : List Chunk) : Option (Bind × List Chunk) :=
  (do
    let (ts, r) ← mathChunk cs
    let (vs, d) ← binderMath ts
    some (.every vs d, r)) <|>
  (do
    let (ts, r) ← mathChunk cs
    let v ← match ts with | [.id v] => some v | _ => none
    let r1 ← kw [w!"be", w!"a"] r <|> kw [w!"be", w!"an"] r
    let ws := r1.takeWhile (fun c => match c with | .w _ | .p 45 => true | _ => false)
    if ws.isEmpty then none else some (.noun (ws ++ [.m [.id v]]), r1.drop ws.length))

/-- Further variables and definitions of a `let`: `, and let $u\in A$`, `and $v\in B$`,
`, and let $X\coloneqq e$`, `, $Y\coloneqq f$ and $Z\coloneqq g$`. -/
def letMore : Nat → List Chunk → List Bind → List MT → Option (List Bind × List MT × List Chunk)
  | 0, cs, bs, ds => some (bs.reverse, ds.reverse, cs)
  | f + 1, cs, bs, ds =>
    let next := (punct 44 cs >>= kw [w!"and", w!"let"]) <|> (punct 44 cs >>= kw [w!"and"]) <|>
      kw [w!"and", w!"let"] cs <|> kw [w!"and"] cs <|> punct 44 cs
    match next with
    | none => some (bs.reverse, ds.reverse, cs)
    | some r =>
      match letBinder r with
      | some (b, r') => letMore f r' (b :: bs) ds
      | none =>
        match formula r with
        | some (m, r') =>
          match m with
          | .chain _ ((.defeq, _) :: _) => letMore f r' bs (m :: ds)
          | _ => some (bs.reverse, ds.reverse, cs)
        | none => some (bs.reverse, ds.reverse, cs)

def sentence (cs : List Chunk) : Option Sent :=
  let (topic, cs) := marker cs
  match notionDef cs with
  | some s => some s
  | none =>
  -- let $S$ denote the class of NOUNS, that is, NP.
  match kw [w!"let"] cs with
  | some r =>
    -- `Let $x\in A$.`
    (do
      let (ts, r1) ← mathChunk r
      let (vs, d) ← binderMath ts
      if isEnd r1 then some (.assume (.every vs d)) else none) <|>
    -- `Let $C$ be a|an NP[, and let …]`, `Let $a,b\in A$, and let $X\coloneqq e$, ….`
    (do
      let (b1, r1) ← letBinder r
      let (bs, ds, r2) ← letMore 6 r1 [b1] []
      let isNoun := match b1 with | .noun _ => true | _ => false
      if isEnd r2 && (isNoun || bs.length > 1 || !ds.isEmpty) then some (.assumeAll bs ds) else none) <|>
    -- `Let $f,g:A\to B$ be continuous, normalized by …, with derivatives DISPLAY.`
    (do
      let (ts, r1) ← mathChunk r
      let (names, dom, cod) ← namesSig ts
      let r2 ← kw [w!"be", w!"continuous"] r1
      let r3 ← punct 44 r2 >>= kw [w!"normalized", w!"by"]
      let (anchors, r4) ← anchorList 6 r3 []
      let r5 ← kw [w!"with", w!"derivatives"] r4
      let (m, ls, r6) ← display r5
      if isEnd r6 then some (.defDeriv none [] names dom cod anchors m ls) else none) <|>
    (do
    let (sym, r1) ← formula r
    let r2 ← kw [w!"denote", w!"the"] r1
    let r2 ← classOf r2
    let (plural, r3) ← wordsUntil [] 6 r2 [] <|> (do
      let ws := r2.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (ws.filterMap (fun c => match c with | .w w => some w | _ => none), r2.drop ws.length))
    -- `let $S$ denote the class of NOUNS.`: a class of the vocabulary
    if isEnd r3 then some (.defClass sym plural []) else do
    let r4 ← punct 44 r3 >>= kw [w!"that", w!"is"] >>= punct 44
    let np := r4.dropLast
    if isEnd (r4.drop np.length) then some (.defClass sym plural np) else none)
  | none =>
  -- `[We] denote by $S$ the class of NOUNS.`, `[We] denote the class of NOUNS by $S$.`
  let cs1 := (kw [w!"we"] cs).getD cs
  match kw [w!"denote", w!"by"] cs1, kw [w!"denote", w!"the"] cs1 with
  | some r, _ => do
    let (sym, r1) ← formula r
    let r2 ← kw [w!"the"] r1 >>= classOf
    let ws := r2.takeWhile (fun c => match c with | .w _ => true | _ => false)
    let plural := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
    if isEnd (r2.drop ws.length) && !plural.isEmpty then some (.defClass sym plural []) else none
  | none, some r => do
    let r1 ← classOf r
    let ws := r1.takeWhile (fun c => match c with | .w v => v != w!"by" | _ => false)
    let plural := ws.filterMap (fun c => match c with | .w w => some w | _ => none)
    let r2 ← kw [w!"by"] (r1.drop ws.length)
    let (sym, r3) ← formula r2
    if isEnd r3 && !plural.isEmpty then some (.defClass sym plural []) else none
  | none, none =>
  -- define $sig$ by DISPLAY [and observe that $φ$ for every $x\in A$].
  match kw [w!"define"] cs with
  | some r => (do
    let (s, r1) ← sig r
    let r2 ← kw [w!"by"] r1
    let (pieces, ls, r3) ← defPieces 6 r2 [] []
    if isEnd r3 then some (.defBy s pieces ls none)
    else do
      let r4 ← kw [w!"and", w!"observe", w!"that"] r3
      let (φ, r5) ← formula r4
      let r6 ← kw [w!"for", w!"every"] r5
      let (ts, r7) ← mathChunk r6
      let (vs, dom) ← binderMath ts
      if isEnd r7 then some (.defBy s pieces ls (some (φ, vs, dom))) else none) <|>
    constDefsOf none r
  | none =>
  match kw [w!"set"] cs <|> kw [w!"put"] cs with
  | some r => constDefsOf none r
  | none =>
  -- fix $B$ [and define|set|put DEFS].
  match kw [w!"fix"] cs with
  | some r => do
    let (ts, r1) ← mathChunk r
    let b ← fixBinder ts
    if isEnd r1 then some (.fix b [] []) else do
    let r2 ← kw [w!"and"] r1
    let r3 ← kw [w!"define"] r2 <|> kw [w!"set"] r2 <|> kw [w!"put"] r2
    let (items, ls, r4) ← defList 6 r3 [] []
    if isEnd (trailer r4) && !items.isEmpty && items.all isDefeq then some (.fix b items ls) else none
  | none =>
  -- We say that a N $x$ is PHRASE of a ADJ $sig$ if $φ$ for all $u,v\in A$.
  match kw [w!"we", w!"say", w!"that", w!"a"] cs with
  | some r => do
    let (sbj, r1) ← chunksUntil [w!"is"] r []
    let r2 ← kw [w!"is"] r1
    let (phrase, r3) ← wordsUntil [w!"of"] 8 r2 []
    let r4 ← kw [w!"of", w!"a"] r3 <|> kw [w!"of", w!"an"] r3
    let (o, r5) ← chunksUntil [w!"if"] r4 []
    let r6 ← kw [w!"if"] r5
    let (φ, r7) ← formula r6
    let r8 ← kw [w!"for", w!"all"] r7
    let (ts, r9) ← mathChunk r8
    let (vs, dom) ← binderMath ts
    if isEnd r9 then some (.weSay sbj phrase o φ vs dom) else none
  | none =>
  -- NAME is denoted by $S$.
  match chunksUntil [w!"is"] cs [] with
  | some (name, r) =>
    match kw [w!"is", w!"denoted", w!"by"] r with
    | some r1 => do
      let (s, r2) ← formula r1
      if isEnd r2 then some (.denotedBy name s) else none
    | none => claimsOrDefs topic cs
  | none => claimsOrDefs topic cs
where
  /-- `$S$ be NP[, where $sig$ is given by DISPLAY].` -/
  letBe (b : Bind) (sets : List MT) (cs : List Chunk) : Option Sent := do
    let (sym, r1) ← formula cs
    let r2 ← kw [w!"be"] r1
    let np := r2.takeWhile (fun c => match c with | .p 46 | .p 44 => false | _ => true)
    let r3 := r2.drop np.length
    if isEnd r3 then some (.defSteps b sets sym np none)
    else do
      let r4 ← punct 44 r3 >>= kw [w!"where"]
      let (sg, r5) ← sig r4
      let r6 ← kw [w!"is", w!"given", w!"by"] r5
      let (m, ls, r7) ← display r6
      if isEnd r7 then some (.defSteps b sets sym np (some (sg, m, ls))) else none
  /-- The pieces of a definition, separated by `,` and `, and`. -/
  defPieces : Nat → List Chunk → List DefPiece → List Codes → Option (List DefPiece × List Codes × List Chunk)
    | 0, _, _, _ => none
    | f + 1, cs, acc, ls => do
      let (p, ls', r) ← (do
          -- on $D$, parametrically by DISPLAY
          let r1 ← kw [w!"on"] cs
          let (d, r2) ← formula r1
          let r3 ← punct 44 r2
          let r4 ← kw [w!"parametrically", w!"by"] r3
          let (m, ls', r5) ← display r4
          some (DefPiece.param d m, ls', r5)) <|>
        (do let (m, ls', r1) ← display cs; some (DefPiece.formula m, ls', r1)) <|>
        (do let (m, r1) ← formula cs; some (DefPiece.formula m, [], r1))
      let acc := p :: acc
      let ls := ls ++ ls'
      match punct 44 r with
      | some r' =>
        match kw [w!"and"] r' with
        | some r'' =>
          if (kw [w!"observe"] r'').isSome then some (acc.reverse, ls, r)
          else defPieces f (optPunct 44 r'') acc ls
        | none => defPieces f r' acc ls
      | none =>
        match kw [w!"and"] r with
        | some r' =>
          if (kw [w!"observe"] r').isSome then some (acc.reverse, ls, r)
          else defPieces f (optPunct 44 r') acc ls
        | none => some (acc.reverse, ls, r)
  claimsOrDefs (topic : Topic) (cs : List Chunk) : Option Sent :=
    -- `Since $φ$ [and $ψ$], [it follows that] CLAUSES.`: the reasons are claims too
    match kw [w!"since"] cs with
    | some r => do
      let (facts, r1) ← sinceFacts 4 r []
      let r2 ← punct 44 r1
      let (_, r3) := marker r2
      let rest ← clauses 8 r3 []
      some (.claims topic [] (facts.map (fun m => ({ cites := [], clause := .fact m } : CClause)) ++ rest))
    | none =>
    match binder cs with
    | some (b, r) =>
      match (punct 44 r).map fun r1 => (kw [w!"then"] r1).getD r1 with
      | some r1 =>
        -- For B, let $S$ denote NP.
        match kw [w!"let"] r1 with
        | some r2 =>
          (do
            let (s, r3) ← formula r2
            let r4 ← kw [w!"denote"] r3
            let np := r4.takeWhile (fun c => match c with
              | .p 46 => false | .w v => v != w!"from" | _ => true)
            let rest := trailer (r4.drop np.length)
            if isEnd rest then some (.letDenote b s np) else none) <|>
          letBe b [] r2
        | none =>
        -- For B, set $X\coloneqq e$ and let $S$ be NP[, where …].
        match kw [w!"set"] r1 with
        | some r2 => (do
          let (m, r3) ← formula r2
          let r4 ← kw [w!"and", w!"let"] r3
          letBe b [m] r4) <|> derivAfterSet b r2 <|> constDefsOf (some b) r2
        | none =>
        -- For B, the NAME $sig$ reads DISPLAY.
        match defReads b r1 with
        | some s => some s
        | none =>
        -- For B, the NAME is DEF (, and the NAME is DEF)*.
        match defItems 4 r1 [] with
        | some items => some (.defIs b items)
        | none => do
          -- For B, (For B,)* CLAUSES.
          let (bs, r2) ← moreBinders 3 r1 [b]
          let cs ← clauses 8 r2 []
          some (.claims topic bs cs)
      | none => none
    | none =>
      (do
        let items ← defItems 4 cs []
        let ds := items.flatMap fun it => match it.defn with | .conj xs => xs | m => [m]
        if ds.all isDefeq then some (.constDefs none ds (items.flatMap (·.labels))) else none) <|>
      (do
        let cs ← clauses 8 cs []
        some (.claims topic [] cs))
  /-- `$φ$[, $ψ$] [and $χ$]` before the comma of `since`. -/
  sinceFacts : Nat → List Chunk → List MT → Option (List MT × List Chunk)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (m, r) ← formula cs
      let acc := m :: acc
      match kw [w!"and"] r with
      | some r' => sinceFacts f r' acc
      | none =>
        match r with
        | .p 44 :: .m t :: r' => sinceFacts f (.m t :: r') acc
        | _ => some (acc.reverse, r)
  /-- `set DEFS, and define continuous functions $f,g:A\to B$ by ANCHORS, and DISPLAY.` -/
  derivAfterSet (b : Bind) (cs : List Chunk) : Option Sent := do
    let (items, _, r1) ← defList 6 cs [] []
    if !items.all isDefeq then none else
    let r2 ← (punct 44 r1 >>= kw [w!"and"]) <|> kw [w!"and"] r1
    let r3 ← kw [w!"define", w!"continuous", w!"functions"] r2
    let (ts, r4) ← mathChunk r3
    let (names, dom, cod) ← namesSig ts
    let r5 ← kw [w!"by"] r4
    let (anchors, r6) ← anchorList 6 r5 []
    let (m, ls, r7) ← display r6
    if isEnd r7 then some (.defDeriv (some b) items names dom cod anchors m ls) else none
  defReads (b : Bind) (cs : List Chunk) : Option Sent := do
    let r ← kw [w!"the"] cs
    let (name, r1) ← wordsUntil [] 6 r [] <|> (do
      let ws := r.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (ws.filterMap (fun c => match c with | .w w => some w | _ => none), r.drop ws.length))
    let (s, r2) ← sig r1
    let r3 ← kw [w!"reads"] r2
    let (m, ls, r4) ← display r3
    if isEnd r4 then some (.defReads b name s m ls) else none
  defItems : Nat → List Chunk → List DefItem → Option (List DefItem)
    | 0, _, _ => none
    | f + 1, cs, acc => do
      let (it, r) ← defItem cs
      let r := trailer r
      if isEnd r then some (it :: acc).reverse
      else do
        let r' ← punct 44 r >>= kw [w!"and"]
        defItems f r' (it :: acc)
  moreBinders : Nat → List Chunk → List Bind → Option (List Bind × List Chunk)
    | 0, cs, acc => some (acc.reverse, cs)
    | f + 1, cs, acc =>
      match binder cs with
      | some (b, r) =>
        match punct 44 r with
        | some r' => moreBinders f r' (b :: acc)
        | none => some (acc.reverse, cs)
      | none => some (acc.reverse, cs)

def parseSentence (s : Sentence) : Option Sent := do
  let cs ← chunks (s.toks.length + 1) s.toks []
  sentence cs

end Grammar
end Proofread
