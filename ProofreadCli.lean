import Proofread.Check
import Proofread.Library.UnitSquare

/-! `proofread check ARTICLE.tex [--vocab core|unitsquare] [--prose] [--claims]`

Compiles the article natively and prints its diagnostics. Projects with their own
vocabulary define a three-line executable calling `Proofread.checkArticle`. -/

open Proofread

def usage : String :=
  "usage: proofread check ARTICLE.tex [--vocab core|unitsquare] [--prose] [--claims]"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: path :: opts =>
    let vocab := match opts.dropWhile (· != "--vocab") with
      | _ :: "unitsquare" :: _ => Vocab.core ++ UnitSquare.vocab
      | _ => Vocab.core
    let failed ← checkArticle vocab path (opts.contains "--prose") (opts.contains "--claims")
    pure (if failed == 0 then 0 else 1)
  | _ => IO.eprintln usage; pure 2
