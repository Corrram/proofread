import Proofread.Math

/-! # Sentences and their environments

The article body is split into sentences. Each sentence records its enclosing
environment (a result, a proof, or ordinary text), the label of that
environment, the result a proof belongs to, and its source span. Displayed
equations belong to the sentence that contains them; a display ending in a
period ends its sentence. Figures, tables and the bibliography are not
sentences of the mathematical text. -/
namespace Proofread

inductive EnvKind where
  | text | result (name : Codes) | proof
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Context where
  kind : EnvKind := .text
  /-- Sequential index of the environment (0 for ordinary text). -/
  env : Nat := 0
  label : Codes := []
  /-- For a proof: the label of the result it proves. -/
  proves : Codes := []
  sec : Nat := 0
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Sentence where
  ctx : Context
  toks : List PTok
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Segment

def wResults : List Codes := [w!"theorem", w!"lemma", w!"corollary", w!"proposition", w!"definition",
  w!"remark", w!"example", w!"conjecture"]
def wSkipEnvs : List Codes := [w!"figure", w!"figure*", w!"table", w!"table*", w!"thebibliography",
  w!"tikzpicture", w!"center"]

def isUpper (c : Nat) : Bool := 65 ≤ c && c ≤ 90

/-- Does a text period end the sentence, given the following token? -/
def endsAfter : List PTok → Bool
  | [] => true
  | t :: _ =>
    match t.tok with
    | .word (c :: _) => isUpper c
    | .par | .begin _ | .finish _ | .cmd _ | .mopen => true
    | _ => false

/-- Index of the token closing the current display environment `e`. -/
def displayEnd (e : Codes) : List PTok → Nat → Option Nat
  | [], _ => none
  | t :: ts, i => if t.tok == .finish e then some i else displayEnd e ts (i + 1)

/-- Skip an optional bracketed environment title at text level. -/
def skipTitle : List PTok → List PTok × List PTok
  | t :: ts =>
    if t.tok == .punct 91 then
      let rec go : Nat → List PTok → List PTok → Nat → List PTok × List PTok
        | 0, acc, r, _ => (acc.reverse, r)
        | _ + 1, acc, [], _ => (acc.reverse, [])
        | g + 1, acc, u :: us, depth =>
          if !u.math && u.tok == .punct 93 && depth == 0 then (acc.reverse, us)
          else if !u.math && u.tok == .punct 91 then go g (u :: acc) us (depth + 1)
          else if !u.math && u.tok == .punct 93 then go g (u :: acc) us (depth - 1)
          else go g (u :: acc) us depth
      go (ts.length + 1) [] ts 0
    else ([], t :: ts)
  | [] => ([], [])

structure St where
  out : List Sentence := []
  cur : List PTok := []
  ctx : Context := {}
  envCount : Nat := 0
  lastResult : Codes := []
  sec : Nat := 0
  skipDepth : Nat := 0
  deriving Inhabited, Lean.ToExpr

def flush (s : St) : St :=
  match s.cur with
  | [] => s
  | c =>
    let toks := c.reverse
    let start := (toks.headD default).pos
    let stop := (c.headD default).pos + 1
    { s with out := ⟨s.ctx, toks, start, stop⟩ :: s.out, cur := [] }

def labelOf : List PTok → Codes × List PTok
  | t :: ts =>
    match t.tok with
    | .ref .label l => (l, ts)
    | _ => ([], t :: ts)
  | [] => ([], [])

def proofTarget : List PTok → Codes
  | [] => []
  | t :: ts => match t.tok with
    | .ref .ref l => l
    | _ => proofTarget ts

def go : Nat → List PTok → St → St
  | 0, _, s => s
  | _ + 1, [], s => s
  | f + 1, t :: ts, s =>
    if s.skipDepth > 0 then
      match t.tok with
      | .begin e => if wSkipEnvs.contains e then go f ts { s with skipDepth := s.skipDepth + 1 } else go f ts s
      | .finish e => if wSkipEnvs.contains e then go f ts { s with skipDepth := s.skipDepth - 1 } else go f ts s
      | _ => go f ts s
    else
    match t.tok with
    | .begin e =>
      if wSkipEnvs.contains e then go f ts { flush s with skipDepth := 1 }
      else if wResults.contains e then
        let s := flush s
        let (_, rest) := skipTitle ts
        let (lab, rest) := labelOf rest
        let n := s.envCount + 1
        let c : Context := ⟨.result e, n, lab, [], s.sec⟩
        go f rest { s with ctx := c, envCount := n, lastResult := lab }
      else if e == w!"proof" then
        let s := flush s
        let (title, rest) := skipTitle ts
        let target := match proofTarget title with | [] => s.lastResult | l => l
        let n := s.envCount + 1
        let c : Context := ⟨.proof, n, [], target, s.sec⟩
        go f rest { s with ctx := c, envCount := n }
      else if Lex.wDisplayEnvs.contains e then
        -- the display joins the current sentence; a final period ends it
        match displayEnd e ts 0 with
        | some i =>
          let body := ts.take i
          let closer := ts[i]?.getD default
          let rest := ts.drop (i + 1)
          let last := body.reverse.find? (fun p => match p.tok with
            | .finish _ | .rbrace | .csym 92 | .ref .label _ => false | _ => true)
          let ends : Bool := match last with | some p => p.tok == .msym 46 | none => false
          let s := { s with cur := closer :: (body.reverse ++ (t :: s.cur)) }
          if ends then go f rest (flush s) else go f rest s
        | none => go f ts { s with cur := t :: s.cur }
      else go f ts (flush s)
    | .finish e =>
      if wResults.contains e || e == w!"proof" then
        let c : Context := ⟨.text, 0, [], [], s.sec⟩
        go f ts { flush s with ctx := c }
      else go f ts (flush s)
    | .par => go f ts (flush s)
    | .cmd n =>
      if n == w!"section" || n == w!"section*" then
        let c : Context := ⟨.text, 0, [], [], s.sec + 1⟩
        go f ts { flush s with sec := s.sec + 1, ctx := c }
      else if n == w!"subsection" || n == w!"subsubsection" || n == w!"item" || n == w!"appendix" then
        go f ts (flush s)
      else go f ts { s with cur := t :: s.cur }
    | .punct 46 =>
      if !t.math && endsAfter ts then go f ts (flush { s with cur := t :: s.cur })
      else go f ts { s with cur := t :: s.cur }
    | _ => go f ts { s with cur := t :: s.cur }

end Segment

/-- Segment the tokens of one paragraph block (at offset `base`), continuing the
state of the previous blocks: the sentences completed in the block, and the state
for the next block (a sentence may continue into it). -/
def segBlock (base : Nat) (toks : List PTok) (s : Segment.St) : List Sentence × Segment.St :=
  let toks := toks.map (PTok.shift base)
  let s' := Segment.go (toks.length + 1) toks { s with out := [] }
  (s'.out.reverse, { s' with out := [] })

/-- The sentence left unfinished at the end of the document. -/
def segFinish (s : Segment.St) : List Sentence :=
  (Segment.flush { s with out := [] }).out.reverse

end Proofread
