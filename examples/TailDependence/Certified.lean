import TailDependence.Proofs
import Proofread.Certify

/-! # The certified article

The kernel checks `TailDependence.certificate`: every verified claim of `article.tex` holds and
every definition is well defined. `TailDependence.verifiedK : meaningfulK ∧ claimK` is then
claim `K`, as stated in the text. The command also writes
`article.proofread.json` (for the reader and the diagnostics) and `article.proofread.tex` (for the
margin marks of `proofread.sty`). -/

#proofread_certify TailDependence "article.tex" using TailDependence.Proofs
