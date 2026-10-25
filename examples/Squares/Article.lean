import Squares.Compiled
import Proofread.Readable

/-! # The example's definitions and claims as Lean

`#proofread_semantics` states the definition `Squares.q` and the claims
`Squares.claim0` … `Squares.claim3` as ordinary Lean, each tied to the compiled
document by a kernel-checked `rfl` theorem, and the proof obligations
`Squares.obligationK`. -/

#proofread_semantics Squares "article.tex"
