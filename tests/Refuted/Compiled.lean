import Proofread.Meta

/-! # `article.tex`, compiled by the kernel

`Refuted.compiled : compileArticle Refuted.vocab Refuted.source = some Refuted.doc` is checked
by the kernel from the contents of `article.tex`. The last string pins those contents:
after editing the article, run

    lake exe proofread prepare tests/Refuted/article.tex --lean tests/Refuted/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article Refuted "article.tex" "fnv1a64:dd5f6ee2c77e9a20"
