import Proofread.Meta

/-! # The example article, compiled by the kernel

`Squares.compiled : compileArticle Squares.vocab Squares.source = some Squares.doc`
is checked by the kernel from the contents of `article.tex`. The article needs
only the core vocabulary. -/

#proofread_article Squares "article.tex" "fnv1a64:0c002009385c7f01"
