# Live demo

These pages are the web reader of three example articles, built from the
reports their certificates wrote. Each renders the article from its LaTeX
source with a marker at the start of every sentence. Select a marker to see what
Lean checked for that sentence: its formal reading, its Lean statement, its
definedness condition, the premises it rests on and the declaration that
justifies it.

<div class="grid cards pr-one" markdown>

-   :material-check-decagram:{ .lg .middle } **The certified note**

    ---

    *A number and its reciprocal*, the note of the [tutorial](getting-started.md):
    every one of its 7 claims is derived in the text from what it cites.

    [:octicons-arrow-right-24: Open the reader](demo/note/index.html)

-   :material-alert-decagram-outline:{ .lg .middle } **The draft with a false theorem**

    ---

    The same note at step 6 of the tutorial: the theorem says `f(x) > 2`, Lean
    refutes it at `x = 1`, and the corollary that rests on it is not verified.

    [:octicons-arrow-right-24: Open the reader](demo/refuted/index.html)

-   :material-square-outline:{ .lg .middle } **The smallest example**

    ---

    *Two inequalities for squares*: one definition, a lemma, and a theorem with
    a two-sentence proof.

    [:octicons-arrow-right-24: Open the reader](demo/squares/index.html)

</div>

![The reader of the draft: Theorem 2 is selected, its reading is shown with the three premises it rests on and the refutation](images/demo-reader-refuted.png){ .pr-shot }

## The markers

| Marker | Status of the sentence |
| --- | --- |
| <span class="pr-dot derived"></span> | Derived from its citations: a proof step, or a result whose proof compiled, proved in Lean from exactly what it rests on |
| <span class="pr-dot companion"></span> | Checked by a companion development: a result stated without a compiled proof, proved in Lean |
| <span class="pr-dot definition"></span> | A definition, well defined |
| <span class="pr-dot unverified"></span> | Compiled, not yet verified: no proof yet, or it rests on a claim that is not verified |
| <span class="pr-dot refuted"></span> | False as stated: refuted in Lean |
| <span class="pr-dot failed"></span> | Not compiled: an undefined symbol or a construction the grammar does not read |
| <span class="pr-dot prose"></span> | Prose: it asserts nothing checked |

The summary at the top of each page counts the claims by status, and the legend
filters the markers.

## The files behind the pages

| Page | Folder | Files |
| --- | --- | --- |
| The certified note | [`examples/Demo`](../examples/Demo) | [article](../examples/Demo/article.tex) · [proofs](../examples/Demo/Proofs.lean) · [report](../examples/Demo/article.proofread.json) · [draft](../examples/Demo/draft.tex) |
| The draft with a false theorem | [`tests/Refuted`](../tests/Refuted) | [article](../tests/Refuted/article.tex) · [proofs](../tests/Refuted/Proofs.lean) · [report](../tests/Refuted/article.proofread.json) |
| The smallest example | [`examples/Squares`](../examples/Squares) | [article](../examples/Squares/article.tex) · [proofs](../examples/Squares/Proofs.lean) · [report](../examples/Squares/article.proofread.json) |

CI certifies all three on every push, so the reports cannot go stale. To build
the reader of your own article, see
[step 8 of the tutorial](getting-started.md#8-read-and-share-the-result).
