import Proofread.Check

/-! # Reading the article file and certifying its compilation

`#proofread_article Foo "article.tex"` reads the article at elaboration time,
evaluates the compiler natively to *propose* each stage's result, and adds those
results as literals together with theorems `lhs = rhs` proved by `Eq.refl`.
Such a theorem is checked only by Lean's kernel, which evaluates the compiler
itself. The stages compose to
`Foo.compiled : compileArticle Foo.vocab Foo.source = some Foo.doc`.
No `native_decide` or other trusted evaluation is used.

The assembly (the compilation of the sentences) is certified in chunks of
sentences: `Foo.run{i} : compileAll Foo.envs Foo.cstate{i} Foo.sents{i} = Foo.cstate{i+1}`.
Each chunk is an independent kernel computation. -/
namespace Proofread
open Lean Elab Term Meta Command

def resolvePath (rel : String) : CoreM System.FilePath := do
  let file ← getFileName
  let dir := (System.FilePath.mk file).parent.getD "."
  pure (dir / rel)

/-- A list literal built from `List.cons`/`List.nil` (no elaboration of elements). -/
def listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

def defineLiteral {α : Type} [ToExpr α] (n : Name) (val : α) : CommandElabM Unit := do
  let decl := Declaration.defnDecl
    { name := n, levelParams := [], type := toTypeExpr α, value := toExpr val,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  liftCoreM (addDecl decl)

/-- Add `name : lhs = rhs` proved by `Eq.refl`: only Lean's kernel checks it
(by evaluating `lhs`); the elaborator is not involved. -/
def kernelRefl (n : Name) (ty lhs rhs : Expr) : CommandElabM Unit := do
  let u ← liftTermElabM do
    match ← Meta.inferType ty with
    | .sort u => pure (u.dec.getD Level.zero)
    | _ => pure Level.zero
  let eqTy := mkApp3 (Lean.mkConst ``Eq [Level.succ u]) ty lhs rhs
  let pf := mkApp2 (Lean.mkConst ``Eq.refl [Level.succ u]) ty rhs
  liftCoreM <| addDecl <| Declaration.thmDecl { name := n, levelParams := [], type := eqTy, value := pf }

/-- FNV-1a (64 bit) of the UTF-8 bytes of the article with CRLF normalized. -/
def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def sourcePin (contents : String) : String :=
  let h := (fnv1a64 (contents.replace "\r\n" "\n")).toNat
  let hex := String.ofList (Nat.toDigits 16 h)
  "fnv1a64:" ++ String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Elaborate a closed term from syntax. -/
def elabClosed (stx : Term) : CommandElabM (Expr × Expr) := liftTermElabM do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  pure (e, ← instantiateMVars (← Meta.inferType e))

/-- The identifier of an optional `with X` clause (an optional node holding the
keyword and the identifier). -/
def withClause (s : Syntax) : Option Syntax :=
  if s.getNumArgs == 2 then some s[1] else none

def kernelEq (n : Name) (lhs rhs : Term) : CommandElabM Unit := do
  let (l, ty) ← elabClosed lhs
  let (r, _) ← elabClosed rhs
  kernelRefl n ty l r

unsafe def evalVocabUnsafe (n : Name) : CoreM Vocab := evalConstCheck Vocab ``Vocab n

/-- The value of a vocabulary constant (evaluated at elaboration time). -/
@[implemented_by evalVocabUnsafe] opaque evalVocab (n : Name) : CoreM Vocab

/-- The vocabulary an article was compiled with: `Foo.vocab` is defined by
`#proofread_article` as the vocabulary constant it was given. -/
def articleVocab (ns : Name) : CoreM Vocab := do
  match (← getEnv).find? (ns ++ `vocab) with
  | some (.defnInfo v) =>
    match v.value with
    | .const n _ => evalVocab n
    | _ => evalVocab (ns ++ `vocab)
  | _ => throwError "{ns} has no compiled article (no {ns ++ `vocab})"

/-- The literal of a compiler state, with the vocabulary given by a constant
(so that the vocabulary is not repeated in every literal). -/
def cstateExpr (vocab : Expr) (c : CState) : Expr :=
  let stE := toExpr { c.st with vocab := {} }
  let stE := match stE.getAppFn, stE.getAppArgs with
    | f, args => if h : 0 < args.size then mkAppN f (args.set 0 vocab) else stE
  mkApp4 (Lean.mkConst ``CState.mk) stE (toExpr c.idx) (toExpr c.outcomesRev) (toExpr c.proofs)

def defineExpr (n : Name) (ty val : Expr) : CommandElabM Unit :=
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := n, levelParams := [], type := ty, value := val,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }

/-- Right-nested appends `x₀ ++ (x₁ ++ …)`. -/
partial def chainT (xs : List Term) : CommandElabM Term := do
  match xs with
  | [] => `([])
  | [x] => pure x
  | x :: rest => do let r ← chainT rest; `($x ++ $r)

/-- `#proofread_article Foo "article.tex" "fnv1a64:…" with V` compiles the article
with the vocabulary `V` (default `Proofread.Vocab.core`), records each stage's
result as a literal and proves every stage with Lean's kernel, then proves
`Foo.compiled : compileArticle Foo.vocab Foo.source = some Foo.doc`. The pin is
the hash of the article's contents (see `sourcePin`): Lake does not track the
article file, so a changed article must change this Lean file to be recompiled. -/
syntax (name := proofreadArticle) "#proofread_article " ident str str (" with " ident)? : command

register_option proofread.timing : String := {
  defValue := ""
  descr := "append the time taken by each stage of #proofread_article to this file" }

/-- Run a stage and report its time when `proofread.timing` is set. -/
def timed {α : Type} (label : String) (k : CommandElabM α) : CommandElabM α := do
  let t0 ← IO.monoMsNow
  let a ← k
  let file := proofread.timing.get (← getOptions)
  if !file.isEmpty then
    let h ← IO.FS.Handle.mk file .append
    h.putStrLn s!"{label}: {(← IO.monoMsNow) - t0} ms"
    h.flush
  pure a

register_option proofread.stages : Nat := {
  defValue := 100
  descr := "debugging: stop #proofread_article after this many stages" }

/-- Sentences per kernel-checked chunk of the assembly. -/
register_option proofread.chunk : Nat := {
  defValue := 8
  descr := "number of sentences in each kernel-checked chunk of an article's compilation" }

/-- The certificates of `#proofread_article`, stage by stage. All proofs are
built as explicit terms: the kernel evaluates the compiler only in the `rfl`
stages (`start`, `preamble`, `paragraphs`, `lex{i}`, `seg{i}`, `segFinished`,
`envsEq`, `run{i}`, `finished`), each on literals. -/
@[command_elab proofreadArticle] def elabProofreadArticle : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  let some pin := stx[3].isStrLit? | throwUnsupportedSyntax
  let vocabName ← match withClause stx[4] with
    | some v => liftCoreM <| realizeGlobalConstNoOverloadWithInfo v
    | none => pure ``Vocab.core
  let V ← liftCoreM <| evalVocab vocabName
  let path ← liftCoreM (resolvePath rel)
  let now := sourcePin (← IO.FS.readFile path)
  unless now == pin do
    throwError "{rel} is pinned as {pin} but its contents are {now}: if the article changed \
      on purpose, update the pin to \"{now}\""
  let src ← readLines path
  let id (n : Name) : Term := mkIdent (ns ++ n)
  let nm (s : String) : Name := Name.mkSimple s
  let c (n : Name) : Expr := Lean.mkConst (ns ++ n)
  let stages := proofread.stages.get (← getOptions)
  defineExpr (ns ++ `sourceHash) (Lean.mkConst ``String) (.lit (.strVal pin))
  defineExpr (ns ++ `vocab) (Lean.mkConst ``Vocab) (Lean.mkConst vocabName)
  defineLiteral (ns ++ `source) src
  let some k := src.findIdx? isBeginDocument | throwError "the article has no \\begin\{document}"
  let some ms := macrosOf (joinLines (src.take k)) | throwError "the preamble macros could not be read"
  let bs := blocksOf (src.drop (k + 1)) (linesOffset (src.take (k + 1))) none []
  defineLiteral (ns ++ `bodyLine) k
  defineLiteral (ns ++ `macros) ms
  -- the blocks, each a constant (its lines)
  let codesTy := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Nat)
  let linesTy := mkApp (Lean.mkConst ``List [Level.zero]) codesTy
  let pairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (Lean.mkConst ``Nat) linesTy
  for i in [0:bs.length] do
    defineLiteral (ns ++ nm s!"l{i}") bs[i]!.2
  let blockE (i : Nat) : Expr := mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) (Lean.mkConst ``Nat)
    linesTy (mkRawNatLit bs[i]!.1) (c (nm s!"l{i}"))
  defineExpr (ns ++ `blocks) (mkApp (Lean.mkConst ``List [Level.zero]) pairTy)
    (listExpr pairTy ((List.range bs.length).map blockE))
  timed "start" do
    kernelEq (ns ++ `start) (← `(List.findIdx? isBeginDocument $(id `source))) (← `(some $(id `bodyLine)))
  timed "preamble" do
    kernelEq (ns ++ `preamble) (← `(macrosOf (joinLines (List.take $(id `bodyLine) $(id `source)))))
      (← `(some $(id `macros)))
  timed "paragraphs" do
    kernelEq (ns ++ `paragraphs)
      (← `(blocksOf (List.drop ($(id `bodyLine) + 1) $(id `source))
        (linesOffset (List.take ($(id `bodyLine) + 1) $(id `source))) none []))
      (← `($(id `blocks)))
  if stages ≤ 3 then return
  -- lexing and segmentation, block by block
  let mut mode : List Bool := []
  let mut seg : Segment.St := {}
  let segTy := Lean.mkConst ``Segment.St
  defineLiteral (ns ++ nm "mode0") mode
  defineExpr (ns ++ nm "seg0") segTy (toExpr seg)
  let mut sss : Array (List Sentence) := #[]
  let mut cached := 0
  for i in [0:bs.length] do
    let text := joinLines bs[i]!.2
    defineLiteral (ns ++ nm s!"b{i}") text
    timed s!"joining block {i}" do
      kernelEq (ns ++ nm s!"join{i}") (← `(joinLines $(id (nm s!"l{i}")))) (← `($(id (nm s!"b{i}"))))
    let some (t, m') := lexBlock ms text mode | throwError "block {i} could not be lexed"
    -- a certificate for the same macros, mode and text, from a cache module
    let cacheNs := `Proofread.LexCache ++ nm ("l" ++ lexKey ms mode text)
    let useCache := (← getEnv).contains (cacheNs ++ `lex)
    if useCache then
      cached := cached + 1
      let tyT := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``PTok)
      let tyM := mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Bool)
      defineExpr (ns ++ nm s!"t{i}") tyT (Lean.mkConst (cacheNs ++ `t))
      defineExpr (ns ++ nm s!"mode{i+1}") tyM (Lean.mkConst (cacheNs ++ `next))
      -- the cached statement is about the cache's literals: the kernel compares them with the article's
      timed s!"lexing block {i} (cached)" do
        let lhs ← `(lexBlock $(id `macros) $(id (nm s!"b{i}")) $(id (nm s!"mode{i}")))
        let rhs ← `(some ($(id (nm s!"t{i}")), $(id (nm s!"mode{i+1}"))))
        let (l, ty) ← elabClosed lhs
        let (r, _) ← elabClosed rhs
        let u := Level.succ Level.zero
        let eqTy := mkApp3 (Lean.mkConst ``Eq [u]) ty l r
        let hm ← liftTermElabM <| mkEqRefl (c `macros)
        let _ := hm
        liftCoreM <| addDecl <| Declaration.thmDecl
          { name := ns ++ nm s!"lex{i}", levelParams := [], type := eqTy, value := Lean.mkConst (cacheNs ++ `lex) }
    else
      defineLiteral (ns ++ nm s!"t{i}") t
      defineLiteral (ns ++ nm s!"mode{i+1}") m'
      timed s!"lexing block {i}" do
        kernelEq (ns ++ nm s!"lex{i}")
          (← `(lexBlock $(id `macros) $(id (nm s!"b{i}")) $(id (nm s!"mode{i}"))))
          (← `(some ($(id (nm s!"t{i}")), $(id (nm s!"mode{i+1}")))))
    let (ss, seg') := segBlock bs[i]!.1 (t ++ blockBreak m') seg
    defineLiteral (ns ++ nm s!"ss{i}") ss
    defineExpr (ns ++ nm s!"seg{i+1}") segTy (toExpr seg')
    timed s!"segmenting block {i}" do
      kernelEq (ns ++ nm s!"seg{i}Eq")
        (← `(segBlock $(quote bs[i]!.1) ($(id (nm s!"t{i}")) ++ blockBreak $(id (nm s!"mode{i+1}")))
          $(id (nm s!"seg{i}"))))
        (← `(($(id (nm s!"ss{i}")), $(id (nm s!"seg{i+1}")))))
    sss := sss.push ss
    mode := m'
    seg := seg'
  let n := bs.length
  if cached > 0 then logInfo m!"{cached} of {n} blocks lexed from the cache"
  -- the chain of blocks, from the last one
  let appendFn ← liftTermElabM do
    let e ← Term.elabTerm (← `(fun (a b : List Sentence) => a ++ b)) none
    Term.synthesizeSyntheticMVarsNoPostponing; instantiateMVars e
  let sentTy := Lean.mkConst ``Sentence
  timed "lexing composition" do
    let mut tail : Expr := mkApp (Lean.mkConst ``List.nil [Level.zero]) pairTy
    let mut rest : Expr := mkApp (Lean.mkConst ``List.nil [Level.zero]) sentTy
    let mut chain : Expr := mkApp3 (Lean.mkConst ``lexSeg_nil) (c `macros) (c (nm s!"mode{n}")) (c (nm s!"seg{n}"))
    for j in [0:n] do
      let i := n - 1 - j
      chain := mkAppN (Lean.mkConst ``lexSeg_cons) #[c `macros, mkRawNatLit bs[i]!.1, c (nm s!"l{i}"),
        c (nm s!"b{i}"), tail, c (nm s!"mode{i}"), c (nm s!"mode{i+1}"), c (nm s!"mode{n}"), c (nm s!"seg{i}"),
        c (nm s!"seg{i+1}"), c (nm s!"seg{n}"), c (nm s!"t{i}"), c (nm s!"ss{i}"), rest,
        c (nm s!"join{i}"), c (nm s!"lex{i}"), c (nm s!"seg{i}Eq"), chain]
      tail := mkApp3 (Lean.mkConst ``List.cons [Level.zero]) pairTy (blockE i) tail
      rest := (mkApp2 appendFn (c (nm s!"ss{i}")) rest).headBeta
    defineExpr (ns ++ `sentencesRaw) (mkApp (Lean.mkConst ``List [Level.zero]) sentTy) rest
    let stTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero])
      (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Bool)) segTy
    let resTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) (mkApp (Lean.mkConst ``List [Level.zero]) sentTy) stTy
    let lhs := mkApp4 (Lean.mkConst ``lexSeg) (c `macros) (c `blocks) (c `mode0) (c `seg0)
    let rhs := mkApp2 (Lean.mkConst ``Option.some [Level.zero]) resTy
      (mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) (mkApp (Lean.mkConst ``List [Level.zero]) sentTy) stTy
        (c `sentencesRaw) (mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero])
          (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Bool)) segTy (c (nm s!"mode{n}")) (c (nm s!"seg{n}"))))
    let ty ← liftTermElabM <| mkEq lhs rhs
    liftCoreM <| addDecl <| Declaration.thmDecl { name := ns ++ `lexSegmented, levelParams := [], type := ty, value := chain }
  let ss := sss.toList.flatten ++ segFinish seg
  defineLiteral (ns ++ `sentences) ss
  timed "segmentation end" do
    kernelEq (ns ++ `segFinished) (← `($(id `sentencesRaw) ++ segFinish $(id (nm s!"seg{n}"))))
      (← `($(id `sentences)))
  if stages ≤ 5 then return
  -- assembly, in chunks of sentences
  let envs := envTable ss
  defineLiteral (ns ++ `envs) envs
  kernelEq (ns ++ `envsEq) (← `(envTable $(id `sentences))) (← `($(id `envs)))
  let size := max 1 (proofread.chunk.get (← getOptions))
  let m := max 1 ((ss.length + size - 1) / size)
  let vocabE := Lean.mkConst (ns ++ `vocab)
  let cstateTy := Lean.mkConst ``CState
  let mut cs : CState := { st := { vocab := V } }
  defineExpr (ns ++ nm "cstate0") cstateTy (cstateExpr vocabE cs)
  for i in [0:m] do
    let part := (ss.drop (i * size)).take size
    defineLiteral (ns ++ nm s!"sents{i}") part
    cs := compileAll envs cs part
    defineExpr (ns ++ nm s!"cstate{i+1}") cstateTy (cstateExpr vocabE cs)
    timed s!"sentences chunk {i}" do
      kernelEq (ns ++ nm s!"run{i}")
        (← `(compileAll $(id `envs) $(id (nm s!"cstate{i}")) $(id (nm s!"sents{i}"))))
        (← `($(id (nm s!"cstate{i+1}"))))
  let sentParts := (List.range m).map fun i => id (nm s!"sents{i}")
  kernelEq (ns ++ `sentsSplit) (← `($(id `sentences))) (← chainT sentParts)
  -- the composition of the chunks, as an explicit proof term (no unification on literals)
  timed "assembly composition" do
    let tails ← (List.range m).mapM fun j => do
      let (e, _) ← elabClosed (← chainT (sentParts.drop j))
      pure e
    let envsE := Lean.mkConst (ns ++ `envs)
    let cE (j : Nat) : Expr := Lean.mkConst (ns ++ nm s!"cstate{j}")
    let sE (j : Nat) : Expr := Lean.mkConst (ns ++ nm s!"sents{j}")
    let runE (j : Nat) : Expr := Lean.mkConst (ns ++ nm s!"run{j}")
    let compileAllE (c r : Expr) : Expr := mkApp3 (Lean.mkConst ``compileAll) envsE c r
    let mut chain := runE (m - 1)
    for k in [0:m - 1] do
      let j := m - 2 - k
      let r := tails[j + 1]!
      let step1 := mkApp4 (Lean.mkConst ``compileAll_append) envsE (cE j) (sE j) r
      let f ← liftTermElabM do
        withLocalDeclD `c (Lean.mkConst ``CState) fun c => mkLambdaFVars #[c] (compileAllE c r)
      let step2 ← liftTermElabM <| mkCongrArg f (runE j)
      chain ← liftTermElabM <| do mkEqTrans step1 (← mkEqTrans step2 chain)
    let ty ← liftTermElabM <| mkEq (compileAllE (cE 0) tails[0]!) (cE m)
    liftCoreM <| addDecl <| Declaration.thmDecl
      { name := ns ++ `ranChain, levelParams := [], type := ty, value := chain }
    let split ← liftTermElabM <|
      mkCongrArg (mkApp2 (Lean.mkConst ``compileAll) envsE (cE 0)) (Lean.mkConst (ns ++ `sentsSplit))
    let pf ← liftTermElabM <| mkEqTrans split (Lean.mkConst (ns ++ `ranChain))
    let ty ← liftTermElabM <| mkEq (compileAllE (cE 0) (Lean.mkConst (ns ++ `sentences))) (cE m)
    liftCoreM <| addDecl <| Declaration.thmDecl
      { name := ns ++ `ranAll, levelParams := [], type := ty, value := pf }
  let d := finish ss cs
  defineLiteral (ns ++ `doc) d
  timed "closing" do
    kernelEq (ns ++ `finished) (← `(finish $(id `sentences) $(id (nm s!"cstate{m}")))) (← `($(id `doc)))
  let thm ← `(command| theorem $(mkIdent (ns ++ `assembled)) :
      assemble $(id `vocab) $(id `sentences) = $(id `doc) := by
        unfold assemble; rw [$(id `envsEq):term]
        exact (congrArg (finish $(id `sentences)) $(id `ranAll)).trans $(id `finished))
  elabCommand thm
  let fin ← `(command| theorem $(mkIdent (ns ++ `compiled)) :
      compileArticle $(id `vocab) $(id `source) = some $(id `doc) :=
    compileArticle_eq $(id `start) $(id `preamble) $(id `paragraphs) $(id `lexSegmented)
      $(id `segFinished) $(id `assembled))
  elabCommand fin

/-! ## The lexing cache

`#proofread_lex_cache "macros" "mode" "text"` certifies the lexing of one block,
independently of any article, as `Proofread.LexCache.l<key>.lex`. Cache modules
consisting of such commands are written by `proofread prepare`, grouped by
section and named after their content. `#proofread_article` uses a cached
certificate for a block with the same key: the kernel then only compares the
article's literals with the cache's. Lake rebuilds a cache module only when its
text changes, so editing one section relexes only that section. -/

/-- Macros as a single string: `name␂body` pairs separated by `␁` (as in `lexKey`). -/
def encodeMacros (ms : Macros) : String :=
  String.intercalate "\u0001" (ms.map fun (n, b) => Codes.toString n ++ "\u0002" ++ Codes.toString b)

def decodeMacros (s : String) : Macros :=
  if s.isEmpty then [] else
  (s.splitOn "\u0001").map fun p => match p.splitOn "\u0002" with
    | [n, b] => (Codes.ofString n, Codes.ofString b)
    | _ => ([], [])

syntax (name := proofreadLexCache) "#proofread_lex_cache " str str str : command

@[command_elab proofreadLexCache] def elabProofreadLexCache : CommandElab := fun stx => do
  let some msS := stx[1].isStrLit? | throwUnsupportedSyntax
  let some modeS := stx[2].isStrLit? | throwUnsupportedSyntax
  let some text := stx[3].isStrLit? | throwUnsupportedSyntax
  let ms := decodeMacros msS
  let mode := modeS.toList.map (· == '1')
  let b := Codes.ofString text
  let cns := `Proofread.LexCache ++ Name.mkSimple ("l" ++ lexKey ms mode b)
  if (← getEnv).contains (cns ++ `lex) then return
  let some (t, m') := lexBlock ms b mode | throwError "the block could not be lexed"
  defineLiteral (cns ++ `macros) ms
  defineLiteral (cns ++ `mode) mode
  defineLiteral (cns ++ `b) b
  defineLiteral (cns ++ `t) t
  defineLiteral (cns ++ `next) m'
  let id (n : Name) : Term := mkIdent (cns ++ n)
  kernelEq (cns ++ `lex) (← `(lexBlock $(id `macros) $(id `b) $(id `mode)))
    (← `(some ($(id `t), $(id `next))))

/-- `#proofread_check "article.tex" with V` compiles the article natively and
reports the sentences without a reading, as warnings. It certifies nothing; it
is the fast loop while writing. -/
syntax (name := proofreadCheck) "#proofread_check " str (" with " ident)? : command

@[command_elab proofreadCheck] def elabProofreadCheck : CommandElab := fun stx => do
  let some rel := stx[1].isStrLit? | throwUnsupportedSyntax
  let vocabName ← match withClause stx[2] with
    | some v => liftCoreM <| realizeGlobalConstNoOverloadWithInfo v
    | none => pure ``Vocab.core
  let V ← liftCoreM <| evalVocab vocabName
  let path ← liftCoreM (resolvePath rel)
  let lines ← readLines path
  match compileArticle V lines with
  | none => throwError "{rel} could not be read (no \\begin\{document}, or unbalanced math)"
  | some d =>
    let (out, cov) := diagnostics V rel lines d true false
    for l in out do logWarning l
    logInfo m!"{d.globs.length} definitions, {d.claims.length} claims\n{cov.render}"

end Proofread
