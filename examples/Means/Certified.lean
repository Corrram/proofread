import Means.Proofs
import Proofread.Certify

/-! # The certified article

The kernel checks `Means.certificate`: every verified claim of `article.tex` holds and
every definition is well defined. `Means.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`article.proofread.json` (for the reader and the diagnostics) and `article.proofread.tex` (for the
margin marks of `proofread.sty`). -/

#proofread_certify Means "article.tex" using Means.Proofs
