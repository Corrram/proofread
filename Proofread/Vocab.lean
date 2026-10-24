import Proofread.Math
import Proofread.Syntax

/-! # Vocabularies

A vocabulary supplies the meanings that an article does not define itself:
base types, constants, nouns (`probability measure $\gamma$ on $[0,1]^2$`),
modifiers (`with uniform marginals`) and named notions (`Lebesgue measure on
$[0,1]$`). Each entry pairs a fixed phrase with a closed core term. The phrases
are matched literally; there is no other source of meaning.

A vocabulary is reviewed once, together with its `Model` (the Lean meaning of
its base types and constants), and shared by every article that uses it. The
core vocabulary `Vocab.core` covers real analysis on `[0,1]`; subject
vocabularies extend it (`Vocab.append`). -/

namespace Proofread

/-- An item of a vocabulary phrase: a lower-case word, a fixed formula (matched
token for token), or the variable that the phrase binds (`$x$`). -/
inductive PItem where
  | w (word : Codes)
  | m (toks : List MTok)
  | v
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

abbrev Phrase := List PItem

/-- A noun: a class of objects of one type. `pred` is a closed predicate on `ty`. -/
structure Noun where
  sing : Phrase
  plural : Phrase
  ty : Ty
  pred : Tm
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A modifier restricts a noun of the same type: prenominal adjectives
(`Borel measurable`) and postnominal phrases (`with uniform marginals`). -/
structure Modifier where
  phrase : Phrase
  prenominal : Bool
  ty : Ty
  pred : Tm
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

/-- A named notion, for `NAME is denoted by $S$` and `let $S$ denote NAME`. -/
structure Notion where
  name : Phrase
  value : Tm
  ty : Ty
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

structure Vocab where
  /-- Names of the base types (for readings). -/
  types : List Codes := []
  /-- Types of the constants (`Tm.const i`). -/
  consts : List Ty := []
  /-- Readable names of the constants (for readings). -/
  constNames : List Codes := []
  nouns : List Noun := []
  mods : List Modifier := []
  notions : List Notion := []
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Vocab

/-- Shift base-type indices of a type by `k`. -/
def shiftTy (k : Nat) : Ty → Ty
  | .base i => .base (i + k)
  | .fn a b => .fn (shiftTy k a) (shiftTy k b)
  | t => t

/-- Base-type shifts inside terms (binder annotations). -/
def shiftTm (k : Nat) : Tm → Tm
  | .lam t d b => .lam (shiftTy k t) (shiftTm k d) (shiftTm k b)
  | .all t b => .all (shiftTy k t) (shiftTm k b)
  | .ex t b => .ex (shiftTy k t) (shiftTm k b)
  | .the t b => .the (shiftTy k t) (shiftTm k b)
  | .undef t => .undef (shiftTy k t)
  | .app f x => .app (shiftTm k f) (shiftTm k x)
  | .ofUnit x => .ofUnit (shiftTm k x)
  | .toUnit x => .toUnit (shiftTm k x)
  | .add x y => .add (shiftTm k x) (shiftTm k y)
  | .sub x y => .sub (shiftTm k x) (shiftTm k y)
  | .mul x y => .mul (shiftTm k x) (shiftTm k y)
  | .div x y => .div (shiftTm k x) (shiftTm k y)
  | .neg x => .neg (shiftTm k x)
  | .abs x => .abs (shiftTm k x)
  | .powNat x n => .powNat (shiftTm k x) n
  | .cases p v r => .cases (shiftTm k p) (shiftTm k v) (shiftTm k r)
  | .eq x y => .eq (shiftTm k x) (shiftTm k y)
  | .lt x y => .lt (shiftTm k x) (shiftTm k y)
  | .le x y => .le (shiftTm k x) (shiftTm k y)
  | .not p => .not (shiftTm k p)
  | .and p q => .and (shiftTm k p) (shiftTm k q)
  | .or p q => .or (shiftTm k p) (shiftTm k q)
  | .imp p q => .imp (shiftTm k p) (shiftTm k q)
  | .iff p q => .iff (shiftTm k p) (shiftTm k q)
  | .integral b => .integral (shiftTm k b)
  | .guard p e => .guard (shiftTm k p) (shiftTm k e)
  | t => t

/-- `V ++ W`: the entries of `W` follow those of `V`; its base types and
constants are renumbered. -/
def append (V W : Vocab) : Vocab :=
  let kt := V.types.length
  let kc := V.consts.length
  let tm (t : Tm) : Tm := (shiftTm kt t).shiftConst kc
  { types := V.types ++ W.types
    consts := V.consts ++ W.consts.map (shiftTy kt)
    constNames := V.constNames ++ W.constNames
    nouns := V.nouns ++ W.nouns.map fun n => { n with ty := shiftTy kt n.ty, pred := tm n.pred }
    mods := V.mods ++ W.mods.map fun m => { m with ty := shiftTy kt m.ty, pred := tm m.pred }
    notions := V.notions ++ W.notions.map fun n => { n with ty := shiftTy kt n.ty, value := tm n.value } }

instance : Append Vocab := ⟨append⟩

end Vocab

/-! ## Writing phrases

`phrase!"probability measure $v$ on $[0,1]^2$"` is the phrase literal: words are
lower-cased, `$v$` is the bound variable and any other formula is fixed. The
lexer runs when the vocabulary is elaborated, so that the kernel never lexes
vocabulary phrases. -/

open Lean Elab Term Meta in
/-- The phrase items of a string (run by the elaborator of `phrase!`). -/
def phraseOf (s : String) : Except String Phrase := do
  let some toks := lex [] (Codes.ofString s) | throw s!"cannot lex phrase {s}"
  let rec go : Nat → List PTok → Phrase → Except String Phrase
    | 0, _, _ => throw "phrase too long"
    | _ + 1, [], acc => pure acc.reverse
    | f + 1, t :: ts, acc =>
      match t.tok with
      | .word w => go f ts (.w (w.map fun x => if 65 ≤ x && x ≤ 90 then x + 32 else x) :: acc)
      | .mopen =>
        let body := ts.takeWhile (fun p => p.tok != .mclose)
        let rest := ts.drop (body.length + 1)
        match Math.simplify (body.length + 1) body with
        | some [.id [118]] => go f rest (.v :: acc)
        | some ms => go f rest (.m ms :: acc)
        | none => throw s!"cannot read the formula in phrase {s}"
      | .punct 39 => go f ts acc
      | _ => throw s!"unexpected token in phrase {s}"
  go (toks.length + 1) toks []

syntax:max "phrase!" str : term

open Lean Elab Term Meta in
elab_rules : term
  | `(phrase! $s:str) => do
    match phraseOf s.getString with
    | .ok p => pure (toExpr p)
    | .error e => throwError e

/-! ## The core vocabulary

Real analysis on `[0,1]`: functions and maps with a signature, Borel
measurability and Lebesgue measure. -/

namespace Vocab

def core : Vocab where
  mods := [
    { phrase := phrase!"Borel measurable", prenominal := true, ty := Ty.self,
      pred := .lam Ty.self .tt (.app (.prim .borel) (.loc 0)) }]
  notions := [
    { name := phrase!"Lebesgue measure on $[0,1]$", value := .prim .leb, ty := Ty.set1 ⟶ .real }]

end Vocab

end Proofread
