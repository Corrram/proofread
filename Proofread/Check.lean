import Proofread.Render

/-! # Checking an article quickly

`checkArticle` runs the compiler natively on an article file and reports, in the
`file:line:col: severity: message` format of editors, every sentence that did not
compile and (optionally) every sentence of a result or proof that has no
mathematical reading. It is the fast feedback loop while writing: it certifies
nothing. The kernel-checked compilation is `#proofread_article`. -/

namespace Proofread

/-- The file contents as lines of code points (CRLF normalized). -/
def readLines (path : System.FilePath) : IO (List (List Nat)) := do
  let s ← IO.FS.readFile path
  let s := s.replace "\r\n" "\n"
  let lines := s.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  pure (lines.map fun l => l.toList.map Char.toNat)


def errMessage (e : Err) : String :=
  let d := Codes.toString e.detail
  let what := if e.code == E.undefined then "undefined symbol"
    else if e.code == E.type then "type mismatch"
    else if e.code == E.unsupported then "unsupported construction"
    else if e.code == E.noun then "unknown noun"
    else if e.code == E.label then "unknown label"
    else if e.code == E.free then "unbound variable"
    else if e.code == E.redefined then "symbol defined twice"
    else if e.code == E.referent then "no referent"
    else if e.code == E.shadow then "variable shadows a definition"
    else s!"error {e.code}"
  if d.isEmpty then what else s!"{what}: {d}"

/-- Line and column (both from 1) of a code point offset. -/
def lineCol (lines : List (List Nat)) (off : Nat) : Nat × Nat := Id.run do
  let mut o := off
  let mut ln := 1
  for l in lines do
    if o ≤ l.length then return (ln, o + 1)
    o := o - (l.length + 1)
    ln := ln + 1
  return (ln, 1)

def kindString : EnvKind → String
  | .text => "text"
  | .result n => Codes.toString n
  | .proof => "proof"

/-- Coverage of an article: per environment kind, the number of compiled,
failed and prose sentences. -/
structure Coverage where
  rows : List (String × Nat × Nat × Nat) := []

def Coverage.add (c : Coverage) (kind : String) (outcome : Outcome) : Coverage :=
  let (a, b, p) := match outcome with
    | .compiled _ _ => (1, 0, 0) | .failed _ => (0, 1, 0) | .prose => (0, 0, 1)
  match c.rows.find? (·.1 == kind) with
  | some _ => ⟨c.rows.map fun (k, x, y, z) => if k == kind then (k, x + a, y + b, z + p) else (k, x, y, z)⟩
  | none => ⟨c.rows ++ [(kind, a, b, p)]⟩

def Coverage.render (c : Coverage) : String :=
  let line (k : String) (a b p : Nat) := s!"  {k}: {a} compiled, {b} failed, {p} prose (of {a + b + p})"
  let total := c.rows.foldl (fun (x, y, z) (_, a, b, p) => (x + a, y + b, z + p)) (0, 0, 0)
  String.intercalate "\n" (c.rows.map (fun (k, a, b, p) => line k a b p) ++
    [line "all" total.1 total.2.1 total.2.2])

def resultKind : EnvKind → String
  | .result _ => "results"
  | .proof => "proofs"
  | .text => "text"

/-- Diagnostics for a compiled document. `prose` also lists sentences of results
and proofs without a reading; `claims` prints the reading of every claim. -/
def diagnostics (V : Vocab) (rel : String) (lines : List (List Nat)) (d : Doc)
    (prose claims : Bool) : List String × Coverage := Id.run do
  let mut out : List String := []
  let mut cov : Coverage := {}
  let cs := V.constNames.map Codes.toString
  let gs := d.globNames
  for s in [0:d.sentences.length] do
    let (ctx, a, _) := d.sentences[s]!
    let (l, c) := lineCol lines a
    let o := d.outcomes[s]?.getD .prose
    cov := cov.add (resultKind ctx.kind) o
    match o with
    | .failed e => out := out ++ [s!"{rel}:{l}:{c}: warning: sentence not compiled ({errMessage e}); it asserts nothing checked"]
    | .prose =>
      if prose && ctx.kind != .text then
        out := out ++ [s!"{rel}:{l}:{c}: info: {kindString ctx.kind} sentence without a mathematical reading"]
    | .compiled ds ks =>
      if claims then
        for i in ds do
          out := out ++ [s!"{rel}:{l}:{c}: info: defines {gs.getD i s!"g{i}"}"]
        for k in ks do
          match d.claims[k]? with
          | some cl => out := out ++ [s!"{rel}:{l}:{c}: info: claim {k}: {cl.body.tex cs gs []}"]
          | none => pure ()
  return (out, cov)

/-- Compile the article at `path` natively and print its diagnostics. Returns
the number of sentences that failed to compile. -/
def checkArticle (V : Vocab) (path : System.FilePath) (prose claims : Bool := false) : IO Nat := do
  let lines ← readLines path
  match compileArticle V lines with
  | none =>
    IO.eprintln s!"{path}: error: the article could not be read (no \\begin\{document}, or unbalanced math)"
    pure 1
  | some d =>
    let (out, cov) := diagnostics V path.toString lines d prose claims
    for l in out do IO.println l
    IO.println s!"{path}: {d.globs.length} definitions, {d.claims.length} claims\n{cov.render}"
    pure (d.outcomes.filter (fun o => match o with | .failed _ => true | _ => false)).length

end Proofread
