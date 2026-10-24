import Proofread.Render

/-! # Reading the article file and certifying its compilation

`#proofread_article Foo "article.tex"` reads the article at elaboration time,
evaluates the compiler natively to *propose* each stage's result, and adds those
results as literals together with theorems `lhs = rhs` proved by `Eq.refl`.
Such a theorem is checked only by Lean's kernel, which evaluates the compiler
itself. The stages compose to `Foo.compiled : compileArticle Foo.source = some Foo.doc`.
No `native_decide` or other trusted evaluation is used. -/
namespace Proofread
open Lean Elab Term Meta Command

/-- The file contents as lines of code points (CRLF normalized). -/
def readLines (path : System.FilePath) : IO (List (List Nat)) := do
  let s ← IO.FS.readFile path
  let s := s.replace "\r\n" "\n"
  let lines := s.splitOn "\n"
  let lines := if lines.getLast? == some "" then lines.dropLast else lines
  pure (lines.map fun l => l.toList.map Char.toNat)

def resolvePath (rel : String) : CoreM System.FilePath := do
  let file ← getFileName
  let dir := (System.FilePath.mk file).parent.getD "."
  pure (dir / rel)

/-- A list literal built from `List.cons`/`List.nil` (no elaboration of elements). -/
def listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (Lean.mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (Lean.mkConst ``List.nil [Level.zero]) ty)

def packedExpr (lines : List (List Nat)) : Expr :=
  let nat := Lean.mkConst ``Nat
  let pairTy := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) nat nat
  listExpr pairTy (lines.map fun l =>
    mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) nat nat (mkRawNatLit l.length)
      (mkRawNatLit (packLine l)))

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

def kernelEq (n : Name) (lhs rhs : Term) : CommandElabM Unit := do
  let (l, ty) ← elabClosed lhs
  let (r, _) ← elabClosed rhs
  kernelRefl n ty l r

/-- `#proofread_article Foo "article.tex" "fnv1a64:…"` compiles the article, records each
stage's result as a literal and proves every stage with Lean's kernel, then proves
`Foo.compiled : compileArticle Foo.source = some Foo.doc`. The last argument pins
the article's contents (see `sourcePin`): Lake does not track the article file,
so a changed article must change this Lean file to be recompiled. -/
syntax (name := proofreadArticle) "#proofread_article " ident str str : command

@[command_elab proofreadArticle] def elabProofreadArticle : CommandElab := fun stx => do
  let ns := stx[1].getId
  let some rel := stx[2].isStrLit? | throwUnsupportedSyntax
  let some pin := stx[3].isStrLit? | throwUnsupportedSyntax
  let path ← liftCoreM (resolvePath rel)
  let now := sourcePin (← IO.FS.readFile path)
  unless now == pin do
    throwError "{rel} is pinned as {pin} but its contents are {now}: if the article changed \
      on purpose, update the pin to \"{now}\""
  let lines ← readLines path
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `sourceHash, levelParams := [], type := Lean.mkConst ``String, value := .lit (.strVal pin),
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let src : Packed := lines.map fun l => (l.length, packLine l)
  liftCoreM <| addDecl <| Declaration.defnDecl
    { name := ns ++ `source, levelParams := [], type := Lean.mkConst ``Packed, value := packedExpr lines,
      hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe }
  let some k := src.findIdx? (fun (len, n) => isBeginDocument len n) | throwError "the article has no \\begin\{document}"
  let some ms := macrosOf (Packed.join (src.take k)) | throwError "the preamble macros could not be read"
  let bs := blocksOf (src.drop (k + 1)) (Packed.offset (src.take (k + 1))) none []
  let some (ts, stEnd) := lexBlocks ms bs [] | throwError "the source could not be lexed"
  let ss := sentences ts
  let d := assemble ss
  let id (n : Name) : Term := mkIdent (ns ++ n)
  let nm (s : String) : Name := Name.mkSimple s
  defineLiteral (ns ++ `bodyLine) k
  defineLiteral (ns ++ `macros) ms
  defineLiteral (ns ++ `blocks) bs
  kernelEq (ns ++ `start) (← `(List.findIdx? (fun (p : Nat × Nat) => isBeginDocument p.1 p.2) $(id `source)))
    (← `(some $(id `bodyLine)))
  kernelEq (ns ++ `preamble) (← `(macrosOf (Packed.join (List.take $(id `bodyLine) $(id `source)))))
    (← `(some $(id `macros)))
  kernelEq (ns ++ `paragraphs)
    (← `(blocksOf (List.drop ($(id `bodyLine) + 1) $(id `source))
      (Packed.offset (List.take ($(id `bodyLine) + 1) $(id `source))) none []))
    (← `($(id `blocks)))
  -- lexing in chunks of paragraph blocks; the mode stack is carried between chunks
  let chunk := 24
  let n := (bs.length + chunk - 1) / chunk
  let mut stk : List Bool := []
  for i in [0:n] do
    let part := (bs.drop (i * chunk)).take chunk
    let some (t, st') := lexBlocks ms part stk | throwError "lexing failed in chunk {i}"
    defineLiteral (ns ++ nm s!"blocks{i}") part
    defineLiteral (ns ++ nm s!"tokens{i}") t
    defineLiteral (ns ++ nm s!"mode{i}") stk
    stk := st'
  defineLiteral (ns ++ nm s!"mode{n}") stk
  for i in [0:n] do
    kernelEq (ns ++ nm s!"lex{i}")
      (← `(lexBlocks $(id `macros) $(id (nm s!"blocks{i}")) $(id (nm s!"mode{i}"))))
      (← `(some ($(id (nm s!"tokens{i}")), $(id (nm s!"mode{i+1}")))))
  -- composition of the chunks (right-nested appends)
  let rec chainT (xs : List Term) : CommandElabM Term := do
    match xs with
    | [] => `([])
    | [x] => pure x
    | x :: rest => do let r ← chainT rest; `($x ++ $r)
  let blockParts := (List.range n).map fun i => id (nm s!"blocks{i}")
  let tokParts := (List.range n).map fun i => id (nm s!"tokens{i}")
  defineLiteral (ns ++ `tokens) ts
  let _ := stEnd
  kernelEq (ns ++ `blocksSplit) (← `($(id `blocks))) (← chainT blockParts)
  kernelEq (ns ++ `tokensJoin) (← chainT tokParts) (← `($(id `tokens)))
  -- lexing the whole body, from the chunk certificates and `lexBlocks_append`
  let rec lexAll : Nat → CommandElabM Term
    | j => do
      if j + 1 ≥ n then `($(id (nm s!"lex{j}")))
      else do
        let rest ← lexAll (j + 1)
        `(lexBlocks_append _ _ _ _ _ _ _ _ $(id (nm s!"lex{j}")) $rest)
  termination_by j => n - j
  let lexProof ← lexAll 0
  let thm ← `(command| theorem $(mkIdent (ns ++ `lexed)) :
      lexBlocks $(id `macros) $(id `blocks) [] = some ($(id `tokens), $(id (nm s!"mode{n}"))) := by
        rw [$(id `blocksSplit):term, ← $(id `tokensJoin):term]; exact $lexProof)
  elabCommand thm
  defineLiteral (ns ++ `sentences) ss
  defineLiteral (ns ++ `doc) d
  kernelEq (ns ++ `segments) (← `(sentences $(id `tokens))) (← `($(id `sentences)))
  kernelEq (ns ++ `assembled) (← `(assemble $(id `sentences))) (← `($(id `doc)))
  let fin ← `(command| theorem $(mkIdent (ns ++ `compiled)) :
      compileArticle $(id `source) = some $(id `doc) :=
    compileArticle_eq $(id `start) $(id `preamble) $(id `paragraphs) $(id `lexed) $(id `segments) $(id `assembled))
  elabCommand fin

end Proofread
