import Means.Compiled
import Proofread.Readable

/-! # The definitions and claims of `article.tex` as Lean

For every definition, a Lean definition with the symbol's name, and for every
claim `K`: `claimK` (what the sentence says), `meaningfulK` (every term in it is
defined) and `obligationK` (its premises imply both). Each is tied to the
compiled document by a kernel-checked `rfl` theorem. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_semantics Means "article.tex"
