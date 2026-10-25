import Proofread.Meta

/-! # `article.tex`, compiled by the kernel

`Demo.compiled : compileArticle Demo.vocab Demo.source = some Demo.doc` is checked
by the kernel from the contents of `article.tex`. The last string pins those contents:
after editing the article, run

    lake exe proofread prepare examples/Demo/article.tex --lean examples/Demo/Compiled.lean

and then `lake build`. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article Demo "article.tex" "fnv1a64:8affdddcd9b98b6a"
