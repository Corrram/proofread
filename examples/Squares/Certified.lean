import Squares.Proofs
import Proofread.Certify

/-! # The certified example

The kernel checks `Squares.certificate`: every claim of `article.tex` holds, the
definition of `q` is well defined, and the sentences of the proof of Theorem 2
use only what they cite. `Squares.verified1` is Theorem 2, as stated in the
text. `#proofread_certify` also writes `article.proofread.json` (for the reader
and the diagnostics) and `article.proofread.tex` (for the PDF margin marks). -/

#proofread_certify Squares "article.tex" using Squares.Proofs

/-- Theorem 2, as compiled from the article. -/
example : ∀ x y : ℝ, 2 * x * y ≤ Squares.q x + Squares.q y := Squares.verified1.2
