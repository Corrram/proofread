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

/-- Binder formulas `x\in A` or `u,v\in A`. -/
def binderMath (ts : List MTok) : Option (List Codes × MT) := do
  let i ← ts.findIdx? (· == .cmd w!"in")
  let vars := (ts.take i).filter (· != .sym 44)
  let names ← vars.mapM fun t => match t with | .id n => some n | _ => none
  let dom ← Math.parseFormula (ts.drop (i + 1))
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

def wMarkers : List (List Codes) :=
  [[w!"to", w!"make", w!"this", w!"precise"], [w!"for", w!"the", w!"first", w!"region"],
   [w!"for", w!"the", w!"second", w!"region"], [w!"consequently"], [w!"hence"], [w!"in", w!"particular"],
   [w!"then"], [w!"thus"], [w!"therefore"]]

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
    let rec tryAll : List (List Codes) → Topic × List Chunk
      | [] => (.none, cs)
      | m :: ms => match kw m cs with
        | some r => (.none, optPunct 44 r)
        | none => tryAll ms
    tryAll wMarkers

inductive Bind where
  | every (vars : List Codes) (dom : MT)
  | noun (np : List Chunk)
  | on (dom : MT)
  deriving Repr, Inhabited

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
        some (.every vs dom, r')
      | none =>
        match kw [w!"on"] cs with
        | some r => do
          let (m, r') ← formula r
          some (.on m, r')
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
  deriving Repr, Inhabited

/-- A clause with the citations that justify it. -/
structure CClause where
  cites : List Codes
  clause : Clause
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

/-- One clause, without its citations. Must be followed by a clause boundary. -/
def clause (cs : List Chunk) : Option (Clause × List Chunk) :=
  -- It holds that DISPLAY
  match kw [w!"it", w!"holds", w!"that"] cs with
  | some r => do let (m, _, r') ← display r; some (.holds m, r')
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
  -- Every $x\in A$ satisfies $φ$
  match kw [w!"every"] cs with
  | some r => do
    let (ts, r1) ← mathChunk r
    let (vs, dom) ← binderMath ts
    let r2 ← kw [w!"satisfies"] r1
    let (body, r3) ← formula r2
    some (.every vs dom body, r3)
  | none =>
  -- The maximum/minimum $F=m$ is attained only by SUBJ[, which REL]
  match kw [w!"the", w!"maximum"] cs, kw [w!"the", w!"minimum"] cs with
  | some r, _ | none, some r => do
    let isMax := (kw [w!"the", w!"maximum"] cs).isSome
    let (fv, r1) ← formula r
    let r2 ← kw [w!"is", w!"attained", w!"only", w!"by"] r1
    let (s, r3) ← subj r2
    match punct 44 r3 >>= kw [w!"which"] with
    | some r4 => do
      let (rels, r5) ← relParts 4 r4 []
      some (.extremum isMax fv s rels, r5)
    | none => some (.extremum isMax fv s [], r3)
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
      some (⟨pre ++ [l], .fact m⟩, r3)
    | none => none
  | none => do
    let (c, r1) ← clause r0
    match kw [w!"by"] r1 >>= cite with
    | some (l, r2) => some (⟨pre ++ [l], c⟩, r2)
    | none => some (⟨pre, c⟩, r1)

/-- Clauses separated by `, and` / `, so`, ending with the final period. -/
def clauses : Nat → List Chunk → List CClause → Option (List CClause)
  | 0, _, _ => none
  | f + 1, cs, acc => do
    let (c, r) ← cclause cs
    if isEnd r then some (c :: acc).reverse
    else
      let r' ← punct 44 r
      match kw [w!"and"] r', kw [w!"so"] r' with
      | some r'', _ | none, some r'' => clauses f r'' (c :: acc)
      | none, none => none

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
      | .w v => if v == w!"is" then some (acc.reverse, rest) else nameWords g rest (v :: acc)
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

inductive Sent where
  | defClass (sym : MT) (plural : List Codes) (np : List Chunk)
  | defIs (bind : Bind) (items : List DefItem)
  | defReads (bind : Bind) (name : List Codes) (sig : MT) (disp : MT) (labels : List Codes)
  | defBy (sig : MT) (disp : MT) (labels : List Codes) (observe : Option (MT × List Codes × MT))
  | denotedBy (name : List Chunk) (sym : MT)
  | letDenote (bind : Bind) (sym : MT) (np : List Chunk)
  | weSay (subj : List Chunk) (phrase : List Codes) (obj : List Chunk) (cond : MT)
      (vars : List Codes) (dom : MT)
  | claims (topic : Topic) (binds : List Bind) (cs : List CClause)
  deriving Repr, Inhabited

def sentence (cs : List Chunk) : Option Sent :=
  let (topic, cs) := marker cs
  -- let $S$ denote the class of NOUNS, that is, NP.
  match kw [w!"let"] cs with
  | some r => do
    let (sym, r1) ← formula r
    let r2 ← kw [w!"denote", w!"the", w!"class", w!"of"] r1
    let (plural, r3) ← wordsUntil [] 6 r2 [] <|> (do
      let ws := r2.takeWhile (fun c => match c with | .w _ => true | _ => false)
      some (ws.filterMap (fun c => match c with | .w w => some w | _ => none), r2.drop ws.length))
    let r4 ← punct 44 r3 >>= kw [w!"that", w!"is"] >>= punct 44
    let np := r4.dropLast
    if isEnd (r4.drop np.length) then some (.defClass sym plural np) else none
  | none =>
  -- define $sig$ by DISPLAY [and observe that $φ$ for every $x\in A$].
  match kw [w!"define"] cs with
  | some r => do
    let (s, r1) ← sig r
    let r2 ← kw [w!"by"] r1
    let (m, ls, r3) ← display r2
    if isEnd r3 then some (.defBy s m ls none)
    else do
      let r4 ← kw [w!"and", w!"observe", w!"that"] r3
      let (φ, r5) ← formula r4
      let r6 ← kw [w!"for", w!"every"] r5
      let (ts, r7) ← mathChunk r6
      let (vs, dom) ← binderMath ts
      if isEnd r7 then some (.defBy s m ls (some (φ, vs, dom))) else none
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
  claimsOrDefs (topic : Topic) (cs : List Chunk) : Option Sent :=
    match binder cs with
    | some (b, r) =>
      match punct 44 r with
      | some r1 =>
        -- For B, let $S$ denote NP.
        match kw [w!"let"] r1 with
        | some r2 => do
          let (s, r3) ← formula r2
          let r4 ← kw [w!"denote"] r3
          let np := r4.takeWhile (fun c => match c with
            | .p 46 => false | .w v => v != w!"from" | _ => true)
          let rest := trailer (r4.drop np.length)
          if isEnd rest then some (.letDenote b s np) else none
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
    | none => do
      let cs ← clauses 8 cs []
      some (.claims topic [] cs)
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
