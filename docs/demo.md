# Live demo

These pages are the web reader of four example articles, built from the
reports their certificates wrote. Each is a short paper in the usual style,
with an abstract, an introduction and references, and each renders from its
LaTeX source with a marker at the start of every sentence. Select a marker to
see what Lean checked for that sentence: its formal reading, its Lean
statement, its definedness condition, the premises it rests on and the
declaration that justifies it.

<div class="grid cards pr-two" markdown>

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

-   :material-function-variant:{ .lg .middle } **Three means**

    ---

    *The harmonic, geometric and arithmetic mean of two numbers*: symbols
    defined inside a theorem, in a `where`-clause and in apposition, and an
    equality case read as "if and only if". 16 claims, all verified.

    [:octicons-arrow-right-24: Open the reader](demo/means/index.html)

-   :material-chart-bell-curve:{ .lg .middle } **Tail monotone copulas**

    ---

    *Tail monotone copulas are positively quadrant dependent*: the notions LTD,
    RTI and PQD are defined in the running text, the way a paper defines them,
    and used by their abbreviations. 8 claims, all derived in the text.

    [:octicons-arrow-right-24: Open the reader](demo/tail/index.html)

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
| Three means | [`examples/Means`](../examples/Means) | [article](../examples/Means/article.tex) · [proofs](../examples/Means/Proofs.lean) · [report](../examples/Means/article.proofread.json) |
| Tail monotone copulas | [`examples/TailDependence`](../examples/TailDependence) | [article](../examples/TailDependence/article.tex) · [proofs](../examples/TailDependence/Proofs.lean) · [report](../examples/TailDependence/article.proofread.json) |

CI certifies all four on every push, so the reports cannot go stale. To build
the reader of your own article, see
[step 8 of the tutorial](getting-started.md#8-read-and-share-the-result).
