import Proofread.Codes

/-! # Lexing TeX source

A total lexer from code points to tokens. It distinguishes text mode from math
mode, expands the article's own parameterless `\newcommand` macros, reads
labels, references and citations, and records the source offset of every token.
Typesetting-only material (spacing, delimiter sizes, emphasis) is dropped.
Anything it does not understand becomes an ordinary token, so that the grammar,
not the lexer, decides whether a sentence has a mathematical reading. -/
namespace Proofread

inductive RefKind where
  | label | ref | eqref | cite
  deriving DecidableEq, Repr, Lean.ToExpr

inductive Tok where
  | word (w : Codes)
  | punct (c : Nat)
  | par
  | mopen | mclose
  | mvar (c : Nat)
  | mnum (n : Nat)
  | msym (c : Nat)
  | cmd (name : Codes)
  | csym (c : Nat)
  | lbrace | rbrace
  | begin (env : Codes)
  | finish (env : Codes)
  | ref (kind : RefKind) (arg : Codes)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure PTok where
  tok : Tok
  pos : Nat
  math : Bool
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

abbrev Macros := List (Codes × Codes)

namespace Lex

def isLetter (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def isSpace (c : Nat) : Bool := c == 32 || c == 9 || c == 13 || c == 10 || c == 126
/-- Letters of text words: ASCII letters, digits, apostrophes and accented Latin letters. -/
def isWordChar (c : Nat) : Bool :=
  isLetter c || isDigit c || c == 39 || c == 8217 || (192 ≤ c && c ≤ 591)

def takeWhile (p : Nat → Bool) : Codes → Codes × Codes
  | [] => ([], [])
  | c :: cs => if p c then let (a, b) := takeWhile p cs; (c :: a, b) else ([], c :: cs)

/-- Read a balanced `{...}` group (the opening brace already consumed). -/
def group : Nat → Nat → Codes → Codes → Option (Codes × Codes × Nat)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | f + 1, depth, c :: cs, acc =>
    if c == 92 then
      match cs with
      | d :: ds => group f depth ds (d :: c :: acc)
      | [] => none
    else if c == 123 then group f (depth + 1) cs (c :: acc)
    else if c == 125 then
      if depth == 0 then some (acc.reverse, cs, acc.length + 1) else group f (depth - 1) cs (c :: acc)
    else group f depth cs (c :: acc)

/-- Skip whitespace, returning the number of skipped code points. -/
def spaces : Codes → Codes × Nat
  | c :: cs => if isSpace c then let (r, n) := spaces cs; (r, n + 1) else (c :: cs, 0)
  | [] => ([], 0)

/-- An optional `[...]` argument (without nesting), skipped. -/
def optArg : Codes → Codes × Nat
  | 91 :: cs =>
    let (a, b) := takeWhile (· != 93) cs
    match b with
    | 93 :: r => (r, a.length + 2)
    | _ => (91 :: cs, 0)
  | cs => (cs, 0)

def wDisplayEnvs : List Codes :=
  [w!"equation", w!"equation*", w!"align", w!"align*", w!"gather", w!"gather*", w!"multline",
   w!"multline*", w!"displaymath"]
def wListEnvs : List Codes := [w!"enumerate", w!"itemize", w!"description"]
def wDropText : List Codes :=
  [w!"emph", w!"textit", w!"textbf", w!"textup", w!"noindent", w!"centering", w!"medskip",
   w!"smallskip", w!"bigskip", w!"par", w!"newline", w!"protect", w!"relax", w!"null"]
def wDropMath : List Codes :=
  [w!"bigl", w!"bigr", w!"Bigl", w!"Bigr", w!"biggl", w!"biggr", w!"big", w!"Big", w!"left",
   w!"right", w!"displaystyle", w!"textstyle", w!"limits", w!"nolimits"]
/-- Commands whose braced arguments are layout or metadata, skipped with the command kept. -/
def wSkipArgs : List Codes :=
  [w!"section", w!"subsection", w!"subsubsection", w!"section*", w!"caption", w!"includegraphics",
   w!"bibliographystyle", w!"bibliography", w!"vspace", w!"hspace", w!"thanks", w!"title",
   w!"author", w!"date", w!"address", w!"email", w!"keywords", w!"maketitle", w!"Needspace",
   w!"texorpdfstring"]

/-- Lexer state: the remaining input, its offset and the mode stack (`true` entries
are math modes opened by `$`, `false` by other delimiters). -/
def lexAux (macros : Macros) : Nat → Codes → Nat → List Bool → List PTok →
    Option (List PTok × List Bool)
  | 0, _, _, _, _ => none
  | _ + 1, [], _, st, out => some (out.reverse, st)
  | f + 1, c :: cs, pos, st, out =>
    let math := !st.isEmpty
    let emit (t : Tok) (rest : Codes) (n : Nat) (st' : List Bool) :=
      lexAux macros f rest (pos + n) st' (⟨t, pos, math⟩ :: out)
    -- comments
    if c == 37 then
      let (_, rest) := takeWhile (· != 10) cs
      lexAux macros f (rest.drop 1) (pos + 1 + (cs.length - rest.length) + (if rest.isEmpty then 0 else 1)) st out
    else if isSpace c then
      -- a blank line in text mode is a paragraph break
      if c == 10 && !math then
        let (rest, n) := spaces cs
        let blank := (cs.take n).any (· == 10)
        if blank then lexAux macros f rest (pos + 1 + n) st (⟨.par, pos, false⟩ :: out)
        else lexAux macros f rest (pos + 1 + n) st out
      else lexAux macros f cs (pos + 1) st out
    else if c == 36 then
      match st with
      | true :: st' => lexAux macros f cs (pos + 1) st' (⟨.mclose, pos, true⟩ :: out)
      | _ => lexAux macros f cs (pos + 1) (true :: st) (⟨.mopen, pos, true⟩ :: out)
    else if c == 92 then
      match cs with
      | [] => none
      | d :: ds =>
        if !isLetter d then
          -- control symbols
          if d == 40 then lexAux macros f ds (pos + 2) (false :: st) (⟨.mopen, pos, true⟩ :: out)
          else if d == 91 then
            lexAux macros f ds (pos + 2) (false :: st) (⟨.begin w!"displaymath", pos, math⟩ :: out)
          else if d == 41 then
            match st with
            | false :: st' => lexAux macros f ds (pos + 2) st' (⟨.mclose, pos, true⟩ :: out)
            | _ => none
          else if d == 93 then
            match st with
            | false :: st' => lexAux macros f ds (pos + 2) st' (⟨.finish w!"displaymath", pos, true⟩ :: out)
            | _ => none
          else if d == 44 || d == 33 || d == 59 || d == 58 || d == 32 || d == 10 then
            lexAux macros f ds (pos + 2) st out
          else if d == 92 then
            let (rest, n) := optArg ds
            emit (.csym 92) rest (2 + n) st
          else emit (.csym d) ds 2 st
        else
          let (name0, rest0) := takeWhile isLetter cs
          let (name, rest) := match rest0 with
            | 42 :: r => if name0 == w!"section" then (name0 ++ [42], r) else (name0, rest0)
            | _ => (name0, rest0)
          let n := name.length + 1
          match macros.lookup name with
          | some body =>
            match lexAux macros f body pos st [] with
            | some (ts, st') => if st' == st then
                lexAux macros f rest (pos + n) st (ts.reverse ++ out) else none
            | none => none
          | none =>
          if name == w!"begin" || name == w!"end" then
            match rest with
            | 123 :: r =>
              let (env, r') := takeWhile (· != 125) r
              let len := n + env.length + 2
              let isDisplay := wDisplayEnvs.contains env
              if name == w!"begin" then
                -- the options of a list environment are layout
                let (r'', k) := if wListEnvs.contains env then optArg (r'.drop 1) else (r'.drop 1, 0)
                emit (.begin env) r'' (len + k) (if isDisplay then false :: st else st)
              else
                let st' := if isDisplay then st.drop 1 else st
                lexAux macros f (r'.drop 1) (pos + len) st' (⟨.finish env, pos, math⟩ :: out)
            | _ => none
          else if name == w!"label" || name == w!"ref" || name == w!"eqref" || name == w!"cite"
              || name == w!"citep" || name == w!"citet" then
            let (r1, n1) := optArg rest
            match r1 with
            | 123 :: r =>
              let (arg, r') := takeWhile (· != 125) r
              let kind := if name == w!"label" then RefKind.label else if name == w!"ref" then .ref
                else if name == w!"eqref" then .eqref else .cite
              emit (.ref kind arg) (r'.drop 1) (n + n1 + arg.length + 2) st
            | _ => none
          else if wSkipArgs.contains name then
            -- skip an optional argument and all directly following braced groups
            let rec skip : Nat → Codes → Nat → Option (Codes × Nat)
              | 0, r, k => some (r, k)
              | g + 1, r, k =>
                let (r1, n1) := optArg r
                match r1 with
                | 123 :: r2 =>
                  match group 100000 0 r2 [] with
                  | some (_, r3, n3) => skip g r3 (k + n1 + 1 + n3)
                  | none => none
                | _ => some (r1, k + n1)
            match skip 4 rest 0 with
            | some (r, k) => emit (.cmd name) r (n + k) st
            | none => none
          else if !math && wDropText.contains name then lexAux macros f rest (pos + n) st out
          else if math && wDropMath.contains name then lexAux macros f rest (pos + n) st out
          else emit (.cmd name) rest n st
    else if c == 123 then
      if math then emit .lbrace cs 1 st else lexAux macros f cs (pos + 1) st out
    else if c == 125 then
      if math then emit .rbrace cs 1 st else lexAux macros f cs (pos + 1) st out
    else if math then
      if isLetter c then emit (.mvar c) cs 1 st
      -- digits are separate tokens, as in TeX (`\frac14`); the grammar groups numerals
      else if isDigit c then emit (.mnum (c - 48)) cs 1 st
      else emit (.msym c) cs 1 st
    else if isWordChar c then
      let (w, rest) := takeWhile isWordChar (c :: cs)
      emit (.word w) rest w.length st
    else emit (.punct c) cs 1 st

/-- Parameterless `\newcommand{\name}{body}` definitions of a preamble. -/
def macrosAux : Nat → Codes → Macros → Option Macros
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | f + 1, c :: cs, acc =>
    if c == 92 then
      let (name, rest) := takeWhile isLetter cs
      if name == w!"newcommand" then
        match rest with
        | 123 :: 92 :: r =>
          let (m, r') := takeWhile isLetter r
          let (m, r') := if m.isEmpty then (r.take 1, r.drop 1) else (m, r')
          match r' with
          | 125 :: 123 :: body =>
            match group 100000 0 body [] with
            | some (b, r'', _) => macrosAux f r'' ((m, b) :: acc)
            | none => none
          | _ => macrosAux f r' acc
        | _ => macrosAux f rest acc
      else macrosAux f rest acc
    else macrosAux f cs acc

end Lex

def macrosOf (preamble : Codes) : Option Macros := Lex.macrosAux (preamble.length + 1) preamble []

def lex (macros : Macros) (input : Codes) (offset : Nat := 0) : Option (List PTok) :=
  match Lex.lexAux macros (4 * input.length + 16) input offset [] [] with
  | some (ts, []) => some ts
  | _ => none

/-! ## Source and paragraph blocks

The source is the list of its lines, each a list of code points. Blank lines
separate paragraph blocks. Each block is lexed on its own, with positions
relative to the block's start, so that the lexing of a block depends only on
its text, the preamble macros and the math mode it starts in. -/

abbrev Source := List Codes

/-- The text of lines, each followed by a newline. -/
def joinLines (ls : List Codes) : Codes := (ls.map fun l => l ++ [10]).flatten

/-- Offset just after the given lines (each followed by a newline). -/
def linesOffset (ls : List Codes) : Nat := ls.foldl (fun a l => a + l.length + 1) 0

def blankLine (l : Codes) : Bool := l.all Lex.isSpace

/-- Group lines into paragraph blocks (start offset, lines); blank lines separate
blocks. -/
def blocksOf : List Codes → Nat → Option (Nat × List Codes) → List (Nat × List Codes) → List (Nat × List Codes)
  | [], _, cur, acc => (cur.toList ++ acc).reverse
  | l :: ls, pos, cur, acc =>
    if blankLine l then blocksOf ls (pos + l.length + 1) none (cur.toList ++ acc)
    else match cur with
      | none => blocksOf ls (pos + l.length + 1) (some (pos, [l])) acc
      | some (p, c) => blocksOf ls (pos + l.length + 1) (some (p, c ++ [l])) acc

/-- Lex one paragraph block (positions relative to its start), continuing the
math-mode stack. -/
def lexBlock (macros : Macros) (block : Codes) (st : List Bool) : Option (List PTok × List Bool) :=
  Lex.lexAux macros (4 * block.length + 16) block 0 st []

/-- The paragraph break after a block (none inside an open formula). -/
def blockBreak (st : List Bool) : List PTok := if st.isEmpty then [⟨.par, 0, false⟩] else []

/-- The key of a block's lexing: the macros, the math-mode stack it starts in and
its text determine its tokens. Equal keys name the same cached certificate (the
kernel still compares the literals, so a collision cannot cause harm). -/
def lexKey (macros : Macros) (st : List Bool) (block : Codes) : String :=
  let enc (c : Codes) : String := Codes.toString c
  let ms := String.intercalate "\u0001" (macros.map fun (n, b) => enc n ++ "\u0002" ++ enc b)
  let s := ms ++ "\u0003" ++ String.ofList (st.map fun b => if b then '1' else '0') ++ "\u0003" ++ enc block
  let h := s.toUTF8.foldl (fun (h : UInt64) b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325
  let hex := String.ofList (Nat.toDigits 16 h.toNat)
  String.ofList (List.replicate (16 - hex.length) '0') ++ hex

/-- Shift token positions by a block's start offset. -/
def PTok.shift (base : Nat) (t : PTok) : PTok := { t with pos := t.pos + base }

end Proofread
