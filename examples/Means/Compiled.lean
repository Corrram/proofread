import Proofread.Meta

/-! # `article.tex`, compiled by the kernel

`Means.compiled : compileArticle Means.vocab Means.source = some Means.doc` is checked
by the kernel from the contents of `article.tex`. The last string pins those contents:
after editing the article, run

    lake exe proofread prepare examples/Means/article.tex --lean examples/Means/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article Means "article.tex" "fnv1a64:6fd2ac2450336377"
