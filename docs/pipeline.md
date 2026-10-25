# From the `.tex` file to the certificate

Proofread compiles an ordinary LaTeX article and verifies it in Lean. Readers
and Lean work from one text: the definitions, statements and proof sentences
that people read are the ones the kernel checks. There is no second,
hand-written formal version that could drift away from the paper.

## Stages

| Stage | Command | What the kernel checks |
| --- | --- | --- |
| compile | `#proofread_article Foo "article.tex" "fnv1a64:…" with V` | `Foo.compiled : compileArticle V Foo.source = some Foo.doc`, by `Eq.refl` on literals, stage by stage (preamble, lexing and segmentation per block, sentences in chunks, assembly). No `native_decide`. |
| state | `#proofread_semantics Foo "article.tex" with M` | Every definition as a Lean constant (`Foo.nu`, `Foo.D`, …), every claim as a proposition (`Foo.claimK`) with its definedness condition (`Foo.meaningfulK`), each tied to the compiled document by an `rfl` theorem (`Foo.env`, `Foo.holdsK`, `Foo.welldefI`). It also states the proof obligations `Foo.obligationK`. |
| justify | your Lean proofs `J.proofK : Foo.obligationK`, `J.definedI : Foo.wellDefinedI` | Ordinary Lean proofs. |
| certify | `#proofread_certify Foo "article.tex" using J` | `Foo.certificate`: every justified claim holds, premises are verified and acyclic, every definition is well defined, and claims derived in the text pass the citation audit. Exports `Foo.verifiedK : Foo.meaningfulK ∧ Foo.claimK` and writes the reports. |

`compileArticle` is an ordinary, total Lean function. The kernel evaluates it on
the file's contents, so the readable statements depend on nothing but the text
(and the reviewed vocabulary, see [vocabularies](vocabularies.md)).

The pin `"fnv1a64:…"` is the hash of the article. Lake does not track the
`.tex` file, so an edited article must change the Lean file to be recompiled.
`lake exe proofread prepare article.tex --lean Compiled.lean` updates the pin.

## Incremental compilation

The kernel's work is split so that an edit is checked where it happened:

* **Blocks.** The body is cut at blank lines outside math and environments.
  Each block is lexed and segmented on its own, with positions relative to the
  block, and the kernel checks each block's stage separately.
* **Lexing cache.** `proofread prepare article.tex --lean Compiled.lean
  --cache LexCache --module Foo.LexCache` writes one Lean module per section,
  named after its content, with the lexing certificate of each block
  (`#proofread_lex_cache`). `#proofread_article` reuses a certificate whose key
  (macros, mode and text) matches, and the kernel only compares literals. Lake
  rebuilds a cache module only when its text changes, so an edit relexes only
  its own section.
* **Sentences** are compiled in chunks (`set_option proofread.chunk 8`), each
  a separate kernel check, and composed by explicit proof terms.

For the Blest article (90 blocks in 5 sections, 351 sentences, 37 definitions
and 48 claims) the kernel-checked compilation takes about 70 s with the lexing
cache and peaks at 2.6 GB, and stating its semantics another 30 s. After an
edit, the cache modules of the unchanged sections are reused.
`set_option proofread.timing "file"` records the time of every stage.

## Definedness

Partial operations are total in Lean, as in mathlib. Every compiled term
therefore has a syntactic definedness condition, `Tm.defined`, in the style of
TCCs. A claim means `defined ∧ claim`. The condition includes:

* nonzero denominators and nonnegative bases of real powers;
* points in `[0,1]`, and arguments in the domain a definition states;
* integrability of integrands and measurability of measured sets;
* coverage of `cases`, and agreement where two conditions overlap;
* the body of a map `v ↦ e` at the points of the domain it is used on;
* integrability of the derivative of a function given by its value at a point and
  its derivative (`φ(x) = φ(a) + ∫_a^x φ'`);
* disjoint parameter domains of a family defined twice (`κ_w`, then `κ_b`);
* exactly one solution of a definite description ("the $b$ with $e_b=e$").

So `1/0 = 0` cannot make a claim true for a conventional reason.

## Justifications and the citation audit

`obligationK` is `P_{j₁} → … → P_{jₙ} → meaningfulK ∧ claimK`, where the `jᵢ`
are the premises the text gives claim `K`: the citations of its sentence, and
for a proof sentence the earlier sentences of the proof. Two tactics help:

* `intro_premises` introduces each premise `J` as `mJ`/`cJ`;
* `definedness [facts]` proves definedness conditions.

A claim is *derived in the text* when it is a proof sentence, or a statement
closed by a compiled proof. For such a claim, `#proofread_certify` audits the
justification. Every constant it uses must come from Lean or mathlib, from
Proofread, from the compiled article, or from helper declarations in the
justification modules, which are audited recursively. A proof sentence
therefore cannot be justified by a result it does not cite. Claims without a
compiled proof (cited theorems, displayed formulas) may use any Lean proof:
typically a companion development, connected by proved bridge theorems. The
certificate permits only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Reports

`#proofread_certify` writes, next to the article:

* `article.proofread.json`: every sentence (position, environment, outcome),
  definition and claim (formal reading, Lean statement, premises, status,
  justification). Read by the web reader and by
  `scripts/proofread_diagnostics.py`.
* `article.proofread.tex`: the status of every labelled result, read by
  `\usepackage[status]{proofread}` to mark results in the margin of the PDF.
  Without the `status` option the PDF is unchanged.

## Reading

`reader/reader.mjs` renders the article from its source (`reader/article.mjs`)
with the status of every sentence:

* derived from its citations;
* checked by a companion development;
* definition, well defined;
* compiled, not yet verified;
* not compiled;
* prose.

Selecting a marker shows the sentence's formal reading, its Lean statement, its
definedness condition, its premises and its justification.

## Trust boundary

The kernel checks the compilation of the file, the identity of the readable
definitions and claims with the compiled semantics, every justification and the
certificate. Outside the proof are: the fixed readings of the grammar's
constructions (documented in `Proofread/Grammar.lean` and `Proofread/Doc.lean`),
the vocabulary and its model (a short, reviewable list), the native evaluation
that proposes stage results (the kernel re-checks them), and the presentation
(the PDF, KaTeX typesetting of formal readings and the HTML reader).
