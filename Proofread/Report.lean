import Proofread.Meta
import Lean.Data.Json

/-! # The per-sentence report of a compiled article

`<article>.proofread.json` records, for every sentence of the article, whether it
compiled, the claims and definitions it produced, their readings and Lean
statements, and (after `#proofread_certify`) how each claim is verified. Readers,
editors and CI read this file; it is never an input to a certificate.

`sourceHash` pins the article text. Lake does not track files read during
elaboration, so `#proofread_article` takes the hash of `article.tex` as an
argument: editing the article changes the hash, the pin must be updated, and
the changed Lean file makes Lake recompile and recertify. -/
namespace Proofread
open Lean Elab Command Meta

/-- The current pin of the article file. -/
def readPin (rel : String) : CommandElabM String := do
  let path ← liftCoreM (resolvePath rel)
  pure (sourcePin (← IO.FS.readFile path))

/-- The pin recorded by `#proofread_article` (the literal `Foo.sourceHash`). -/
def recordedPin (ns : Name) : CommandElabM String := do
  match (← getEnv).find? (ns ++ `sourceHash) with
  | some (.defnInfo v) =>
    match v.value with
    | .lit (.strVal s) => pure s
    | _ => throwError "{ns ++ `sourceHash} is not a string literal"
  | _ => throwError "{ns} has no compiled article (run #proofread_article first)"

/-- Stop if the article changed after it was compiled. -/
def checkFresh (ns : Name) (rel : String) : CommandElabM Unit := do
  let now ← readPin rel
  let was ← recordedPin ns
  unless now == was do
    throwError "{rel} changed after it was compiled ({was}, now {now}): update the pin in \
      #proofread_article to \"{now}\" so that the article is recompiled"

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

def roleString : Role → String
  | .definition => "definition"
  | .statement _ => "statement"
  | .step _ => "proof step"
  | .text => "text"

def kindString : EnvKind → String
  | .text => "text"
  | .result n => Codes.toString n
  | .proof => "proof"

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

/-- A Lean-identifier name for a definition. -/
def defName (d : Doc) (i : Nat) : String :=
  let g := (d.globs[i]?).getD default
  let key := Codes.toString g.key
  let clean (s : String) : String := String.ofList (s.toList.filter Char.isAlphanum)
  if !key.isEmpty then
    if key == "\\mathcal{C}" then "copulas"
    else if key == "^\\top" then "transpose"
    else if key == "^\\perp" then "reflection"
    else if key == "\\widehat" then "survival"
    else clean key
  else match d.names.find? (·.2 == i) with
    | some (ws, _) =>
      let parts := ws.map (fun w => clean (Codes.toString w))
      match parts with
      | [] => s!"def{i}"
      | p :: ps => String.join (p :: ps.map String.capitalize)
    | none => s!"def{i}"

/-- How a claim is verified, for the report. -/
structure ClaimInfo where
  status : String := "unverified"
  rank : Nat := 0
  justification : String := ""
  module : String := ""

/-- Write `<article>.proofread.json`. Claims without information are unverified. -/
def writeReport (ns jn : Name) (rel : String) (d : Doc) (claims : Array ClaimInfo)
    (defs : Array (String × String)) (verified : List Nat) (axioms : List Name) : CommandElabM Unit := do
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  let nm (s : String) : Name := Name.mkSimple s
  let names := (List.range d.values.length).map (defName d)
  let gTex := d.globNames
  let short (str : String) : String :=
    ((str.replace (toString ns ++ ".") "").replace "Proofread.Prelude." "").replace "↑unitInterval" "I"
  let ppConst (n : Name) : CommandElabM String := liftTermElabM do
    match (← getEnv).find? n with
    | some (.defnInfo v) => pure (short (toString (← ppExpr v.value)))
    | _ => pure ""
  let mut claimsJ : Array Json := #[]
  for k in [0:d.claims.length] do
    let c := d.claims[k]!
    let info := claims.getD k {}
    claimsJ := claimsJ.push <| Json.mkObj [
      ("index", toJson k), ("sentence", toJson c.sent), ("role", toJson (roleString c.role)),
      ("cites", toJson (c.cites.map Codes.toString)), ("premises", toJson c.premises),
      ("status", toJson info.status), ("rank", toJson info.rank),
      ("reading", toJson (c.body.tex gTex [])),
      ("lean", toJson (← ppConst (ns ++ nm s!"claim{k}"))),
      ("meaningful", toJson (← ppConst (ns ++ nm s!"meaningful{k}"))),
      ("justification", toJson info.justification), ("module", toJson info.module)]
  let mut defsJ : Array Json := #[]
  for i in [0:d.values.length] do
    let g := d.globs[i]!
    let sent := (List.range d.outcomes.length).find? fun s =>
      match d.outcomes[s]! with
      | .compiled ds _ => ds.contains i
      | _ => false
    let (just, mod) := defs.getD i ("", "")
    defsJ := defsJ.push <| Json.mkObj [
      ("index", toJson i), ("name", toJson names[i]!), ("symbol", toJson gTex[i]!),
      ("key", toJson (Codes.toString g.key)), ("sentence", (sent.map toJson).getD Json.null),
      ("lean", toJson (← ppConst (ns ++ nm names[i]!))),
      ("wellDefined", toJson (← ppConst (ns ++ nm s!"wellDefined{i}"))),
      ("justification", toJson just), ("module", toJson mod)]
  let mut sentsJ : Array Json := #[]
  for s in [0:d.sentences.length] do
    let (ctx, a, b) := d.sentences[s]!
    let (l1, c1) := lineCol lines a
    let (l2, c2) := lineCol lines b
    let out : List (String × Json) := match d.outcomes[s]? with
      | some (.failed e) => [("outcome", toJson "failed"), ("code", toJson e.code), ("message", toJson (errMessage e))]
      | some (.compiled ds cs) => [("outcome", toJson "compiled"), ("definitions", toJson ds), ("claims", toJson cs)]
      | _ => [("outcome", toJson "prose")]
    let base : List (String × Json) := [
      ("index", toJson s), ("start", toJson a), ("stop", toJson b), ("line", toJson l1),
      ("column", toJson c1), ("endLine", toJson l2), ("endColumn", toJson c2),
      ("environment", toJson (kindString ctx.kind)), ("env", toJson ctx.env),
      ("label", toJson (Codes.toString ctx.label))]
    sentsJ := sentsJ.push <| Json.mkObj (base ++ out)
  let report := Json.mkObj [
    ("article", toJson rel), ("sourceHash", toJson (← recordedPin ns)),
    ("namespace", toJson (toString ns)), ("justifications", toJson (toString jn)),
    ("verified", toJson verified), ("axioms", toJson (axioms.map toString)),
    ("definitions", Json.arr defsJ), ("claims", Json.arr claimsJ), ("sentences", Json.arr sentsJ)]
  IO.FS.writeFile (path.withExtension "proofread.json") (report.pretty 100 ++ "\n")

/-- Report sentences that did not compile (as information: they assert nothing). -/
def logUncompiled (rel : String) (d : Doc) : CommandElabM Unit := do
  let lines ← readLines (← liftCoreM (resolvePath rel))
  for s in [0:d.sentences.length] do
    if let some (.failed e) := d.outcomes[s]? then
      let (_, a, _) := d.sentences[s]!
      let (l, c) := lineCol lines a
      logInfo m!"{rel}:{l}:{c}: sentence not compiled ({errMessage e}); it asserts nothing checked"

end Proofread
