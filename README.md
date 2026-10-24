# Proofread

One LaTeX source, read twice: typeset as the paper you submit, and compiled by
Lean into kernel-checked statements and proofs.

Proofread compiles an ordinary mathematical article, written in good
mathematical English, to Lean. Every symbol must be defined in the article
before it is used, every sentence has one fixed reading, and a proof step may
use only the results it cites. The kernel checks the compilation of the file,
the readable Lean form of every definition and claim, every justification and
the final certificate. There is no second, hand-written formal version that
could drift away from the paper.

```latex
For a copula $C$, the population version of Blest's rank correlation is
\begin{equation}
  \label{eq:nu-def}
  \nu(C)\coloneqq24\int_0^1\!\int_0^1(1-u)\,C(u,v)\de u\de v-2,
\end{equation}
```

becomes the Lean definition

```lean
def nu : (I → I → ℝ) → ℝ := fun x => 24 * ∫ y, ∫ z, (1 - ↑z) * x z y - 2
```

and the first sentence of Corollary 3.2,

```latex
Every $C\in\CC$ satisfies $|\nu(C)-\rho(C)|\le\frac14$.
```

becomes `claim14 : ∀ x : I → I → ℝ, copulas x → |nu x - rho x| ≤ 1 / 4`,
derived in Lean from exactly the sentences of its proof and the results they
cite.

## The exemplar

*Rank weighting and asymmetry in Blest's rank correlation: two exact regions*
(arXiv:2609.27634) is compiled in
[lean-verifications](https://github.com/Corrram/lean-verifications)
(`Papers/Rockel2026ExactBlest/Source`). Its `article-edits.diff` lists every
edit the conventions asked for. See its README for the current coverage.

## Use

Add the package to `lakefile.toml`:

```toml
[[require]]
name = "proofread"
git = "https://github.com/Corrram/proofread.git"
rev = "<commit>"
```

Then, next to `article.tex`:

```lean
-- Compiled.lean: the kernel compiles the article
import Proofread.Meta
import Proofread.Library.UnitSquare
def vocab : Proofread.Vocab := .core ++ Proofread.UnitSquare.vocab
#proofread_article Foo "article.tex" "fnv1a64:…" with vocab

-- Article.lean: every definition and claim as readable Lean
import Proofread.Readable
import Proofread.Library.UnitSquareModel
#proofread_semantics Foo "article.tex" with Proofread.UnitSquare.model

-- Proofs.lean: your proofs `proofK : Foo.obligationK`, `definedI : Foo.wellDefinedI`

-- Certified.lean: the certificate, `Foo.verifiedK`, and the reports
import Proofread.Certify
#proofread_certify Foo "article.tex" using Proofs
```

While writing, `lake exe proofread check article.tex --vocab unitsquare
--claims` compiles the article natively in about a second and prints each
undefined symbol, each sentence that does not compile, and the formal reading
of every claim. `editors/vscode/tasks.json` shows the findings in the editor.

## Documentation

* [Writing for Proofread](docs/writing.md): the house style and the
  constructions of the grammar, with examples.
* [From the `.tex` file to the certificate](docs/pipeline.md): the stages,
  incremental compilation, definedness, the citation audit, the reports and
  the trust boundary.
* [Vocabularies and models](docs/vocabularies.md): where the meaning of words
  that the article does not define comes from.

## Layout

| Path | Contents |
| --- | --- |
| `Proofread/Lex.lean`, `Segment.lean`, `Math.lean` | Lexing (macros, blocks), sentence segmentation, formulas |
| `Proofread/Grammar.lean`, `Elab.lean`, `Doc.lean` | Sentence constructions and their readings, compilation of an article (`compileArticle`) |
| `Proofread/Syntax.lean`, `Denote.lean` | The core language and its Lean denotation |
| `Proofread/Vocab.lean`, `Library/` | Vocabularies, `phrase!`, the unit-square vocabulary and its model |
| `Proofread/Meta.lean`, `Readable.lean`, `Certify.lean` | The commands `#proofread_article`, `#proofread_semantics`, `#proofread_certify` |
| `Proofread/Check.lean`, `ProofreadCli.lean` | The native checker `lake exe proofread` |
| `reader/` | The web reader: the article rendered from its source with the status of every sentence |
| `tex/proofread.sty` | Optional margin marks in the PDF (`\usepackage[status]{proofread}`) |
| `scripts/proofread_diagnostics.py` | Findings from the certificate report, for editors and CI |

## Build

```sh
lake exe cache get
lake build
npm ci && npm test
```

Lean 4.34.0 with the mathlib revision in `lake-manifest.json`. The generic code
is licensed under Apache-2.0.
