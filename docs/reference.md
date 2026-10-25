# Commands and files

Everything Proofread provides, in the order a project uses it. The
[tutorial](getting-started.md) shows each in context.

## The command line

`lake exe proofread` runs natively. Its first run builds the executable.

### `proofread check`

```sh
lake exe proofread check ARTICLE.tex [--vocab core|unitsquare] [--claims] [--prose]
```

Compiles the article natively, in about a second, and prints findings in the
`file:line:column: severity: message` format of editors. It certifies nothing.

| Finding | Severity |
| --- | --- |
| a sentence that did not compile (an undefined symbol, a type mismatch, an unsupported construction, …) | warning |
| a sentence of a theorem, lemma, proposition or corollary without a reading | warning |
| with `--claims`: every definition and the formal reading of every claim | info |
| with `--prose`: every sentence of a proof without a reading | info |

The last lines count the compiled, failed and prose sentences of the text, the
results and the proofs. The exit status is 1 if a sentence failed to compile.
`--vocab unitsquare` adds the vocabulary of copulas and probability on the unit
square ([Vocabularies and models](vocabularies.md)).

### `proofread init`

```sh
lake exe proofread init ARTICLE.tex [--name NAME] [--vocab core|unitsquare]
```

Writes four Lean files next to the article and prints the `lean_lib` entry for
`lakefile.toml`. `NAME`, the Lean namespace, is by default the name of the
article's folder. An existing file is never overwritten.

| File | Contents |
| --- | --- |
| `Compiled.lean` | `#proofread_article NAME "article.tex" "fnv1a64:…"` |
| `Article.lean` | `#proofread_semantics NAME "article.tex"` |
| `Proofs.lean` | `namespace NAME.Proofs` with `definedI` for every definition and a stub `proofK` for every claim, each with the claim's reading, place and premises |
| `Certified.lean` | `#proofread_certify NAME "article.tex" using NAME.Proofs` |

### `proofread prepare`

```sh
lake exe proofread prepare ARTICLE.tex --lean COMPILED.lean [--cache DIR --module PREFIX]
```

Run it after every edit of the article. It updates the pin, the hash of the
article in `COMPILED.lean`, so that Lake recompiles the article. With
`--cache`, it also writes the lexing cache, one Lean module per section of the
article, so that the kernel relexes only the sections that changed
([Incremental compilation](pipeline.md#incremental-compilation)).

## The Lean commands

| Command | Declares |
| --- | --- |
| `#proofread_article NS "article.tex" "fnv1a64:…" [with V]` | `NS.source`, `NS.doc` and `NS.compiled : compileArticle NS.vocab NS.source = some NS.doc`, checked by the kernel. It fails if the pin does not match the file. `with V` names the vocabulary (default: the core vocabulary). |
| `#proofread_semantics NS "article.tex" [with M]` | For every definition `I`: a Lean definition named after its symbol and `wellDefinedI`. For every claim `K`: `claimK` (what the sentence says), `meaningfulK` (every term in it is defined) and `obligationK` (its premises imply `meaningfulK ∧ claimK`). Each is tied to the compiled document by a kernel-checked `rfl` theorem. `with M` names the model of the vocabulary. |
| `#proofread_certify NS "article.tex" using J` | `NS.certificate`, checked by the kernel, `NS.verifiedK : NS.meaningfulK ∧ NS.claimK` for every verified claim and `NS.refutedK` for every refuted one. It writes the reports below and logs a summary. |

### What `#proofread_certify` reads

In namespace `J`:

| Declaration | Type | Required |
| --- | --- | --- |
| `J.definedI` | `NS.wellDefinedI` | for every definition, without `sorry` |
| `J.proofK` | `NS.obligationK` | for each claim to verify |
| `J.refuteK` | `NS.meaningfulK ∧ ¬ NS.claimK` | for a claim that is false as stated |

A claim is verified when it has a proof without `sorry` and every claim it rests
on is verified. A claim the text derives (a proof step, or a result whose proof
compiled) is audited: its proof may use Lean, mathlib, Proofread, the compiled
article and helper declarations of the justification modules, which are audited
in turn. The certificate and every refutation may use only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

### Tactics

| Tactic | Does |
| --- | --- |
| `intro_premises` | Unfolds `obligationK` and introduces every premise `J` as `mJ : meaningfulJ` and `cJ : claimJ`. |
| `definedness [h₁, …]` | Proves a definedness condition (`meaningfulK`, `wellDefinedI`): divisions by nonzero terms, arguments in their domains. Give it the facts it cannot find. |

### Options

| Option | Effect |
| --- | --- |
| `set_option proofread.chunk n` | Sentences per kernel-checked chunk of the compilation. |
| `set_option proofread.timing "file"` | Appends the time of every stage of `#proofread_article` to `file`. |

Long articles need `set_option maxRecDepth 100000` and
`set_option maxHeartbeats 0` before `#proofread_article`, as `init` writes them.

## The reports

`#proofread_certify` writes two files next to the article.

`article.proofread.json` records every sentence (position, environment, outcome
and, if it failed, why), every definition (name, symbol, Lean value,
well-definedness condition, justification) and every claim (reading, Lean
statement, definedness condition, premises, status, justification, and for an
unverified claim why it is not verified). The status of a claim is `text`
(derived from its citations), `companion` (proved without a compiled proof in
the text), `unverified` or `refuted`. `sourceHash` pins the article.

`article.proofread.tex` holds the status of every labelled result and a
summary, for `proofread.sty`.

### `proofread_diagnostics.py`

```sh
python .lake/packages/proofread/scripts/proofread_diagnostics.py article.proofread.json \
    [--verified] [--strict] [--prose] [--pin Compiled.lean] [--relative-to DIR]
```

Prints the findings of a report in editor format: a refuted claim is an error,
an unverified claim and a sentence that did not compile are warnings. The exit
status is 1 if the article changed after it was certified, if a claim is
refuted, with `--verified` if a compiled claim is not verified, and with
`--strict` on any warning. `--pin` updates the pin in the Lean file instead.

## The PDF: `proofread.sty`

```latex
\usepackage{proofread}           % loads mathtools and amssymb, changes nothing
\usepackage[status]{proofread}   % marks every labelled result in the margin
\proofreadmodule{Note.Certified} % optional: the module that certifies the article
\proofreadreport                 % optional: a one-line summary, where it appears
```

With `status`, the margin of every labelled result shows *derived* (every
sentence compiled and derived in the text), *checked* (every sentence compiled
and verified), *partly checked*, *compiled* (not yet verified) or *false* (a
claim is refuted). The marks are read from `\jobname.proofread.tex`. Without
the option the typeset article is unchanged, which is what you submit.

## The web reader

```sh
npm ci --prefix .lake/packages/proofread
node .lake/packages/proofread/reader/build.mjs ARTICLE.tex \
    [--out DIR] [--title TITLE] [--bbl FILE.bbl] [--date YYYY-MM-DD] [--home URL]
```

Writes `DIR/index.html` (default `article-reader/` next to the article) with its
stylesheet, script and fonts, a copy of the article and of its report. The page
renders the article from its source, with the status of every sentence. It
refuses a report whose pin does not match the article. `--home` adds a link
back to a page of yours.

## Editors and CI

`editors/vscode/tasks.json` has two VS Code tasks, *quick check* (the native
check of the open file) and *certify* (update the pin, build, report), whose
findings appear as squiggles in the `.tex` file. A GitHub Actions workflow that
certifies an article on every push is in
[step 9 of the tutorial](getting-started.md#9-check-in-ci).
