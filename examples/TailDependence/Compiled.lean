import Proofread.Meta
import Proofread.Library.UnitSquare

/-! # `article.tex`, compiled by the kernel

`TailDependence.compiled : compileArticle TailDependence.vocab TailDependence.source = some TailDependence.doc` is checked
by the kernel from the contents of `article.tex`. The last string pins those contents:
after editing the article, run

    lake exe proofread prepare examples/TailDependence/article.tex --lean examples/TailDependence/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article TailDependence "article.tex" "fnv1a64:5b3614412bb69d39" with Proofread.UnitSquare.withCore
