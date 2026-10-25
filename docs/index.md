---
hide:
  - navigation
  - toc
---

<div class="pr-hero" markdown>

# Proofread

<p class="pr-lead">One LaTeX source, read twice: typeset as the paper you submit, and compiled by
Lean into kernel-checked statements and proofs.</p>

[Get started](getting-started.md){ .md-button .md-button--primary }
[See the live demo](demo.md){ .md-button }

</div>

Proofread compiles an ordinary mathematical article, written in good
mathematical English, to Lean. Every symbol must be defined in the article
before it is used, every sentence has one fixed reading, and a proof step may
use only the results it cites. The Lean kernel checks the compilation, every
definition, every claim and every step of every compiled proof. There is no
second, hand-written formal version that could drift away from the paper.

## From a sentence to a theorem

<div class="pr-pair" markdown>
<div markdown>

The article

```latex
Define $f:(0,\infty)\to\mathbb{R}$ by
$f(x)\coloneqq x+\frac1x$.

\begin{theorem}\label{thm:bound}
For every $x\in(0,\infty)$, $f(x)\ge2$.
\end{theorem}
```

</div>
<div markdown>

compiles to

```lean
def f : ℝ → ℝ := fun x => x + 1 / x

-- f is defined on (0,∞), where 1/x makes sense
def wellDefined0 : Prop := ∀ (x : ℝ), 0 < x → ¬x = 0

def claim2 : Prop := ∀ (x : ℝ), 0 < x → 2 ≤ f x
```

</div>
</div>

The theorem's proof compiles sentence by sentence, so Lean derives `claim2` from
exactly the steps of that proof and the lemma they cite, and each step from what
it rests on. A draft that said `$f(x)>2$` is refuted at `x = 1`, and the reader,
the diagnostics and the margin of the PDF mark it false.

## What you get

<div class="grid cards pr-two" markdown>

-   :material-spellcheck:{ .lg .middle } **Feedback while you write**

    ---

    `lake exe proofread check` reads the article in about a second: undefined
    symbols, statements without a reading, and the formal reading of every
    claim.

-   :material-certificate-outline:{ .lg .middle } **A certificate**

    ---

    `lake build` has the kernel check every definition, claim and proof step.
    Certify while proofs are still `sorry`, and refute claims that are false as
    stated.

-   :material-file-document-outline:{ .lg .middle } **The paper, unchanged**

    ---

    The same `.tex` file typesets as before. `\usepackage[status]{proofread}`
    adds the status of every result in the margin.

-   :material-web:{ .lg .middle } **A reader for your readers**

    ---

    A web page of the article with a marker at every sentence: its status,
    formal reading, Lean statement, premises and justification.
    [Try it](demo.md).

</div>

## In three commands

```sh
lake exe proofread check Note/article.tex --claims   # what Proofread reads, in a second
lake exe proofread init Note/article.tex             # the Lean files, with a stub proof per claim
lake build Note.Certified                            # the kernel checks the article and your proofs
```

The [tutorial](getting-started.md) takes a one-page note from a draft with four
mistakes to a certificate, with the real output of every step.

## Research articles

Two published articles are compiled from their LaTeX sources in
[lean-verifications](https://github.com/Corrram/lean-verifications):

* *Rank weighting and asymmetry in Blest's rank correlation: two exact regions*
  ([arXiv:2609.27634](https://arxiv.org/abs/2609.27634)): 37 definitions and 48
  claims, all certified. The proof of Corollary 3.2 is checked sentence by
  sentence against what it cites.
  [Source](https://github.com/Corrram/lean-verifications/tree/main/Papers/Rockel2026ExactBlest/Source)
* *The exact region determined by Spearman's rho and Gini's gamma*
  ([arXiv:2609.19890](https://arxiv.org/abs/2609.19890)): 11 definitions and 8
  claims, all certified.
  [Source](https://github.com/Corrram/lean-verifications/tree/main/Papers/AnsariRockelSteinmassl2026RhoGamma/Source)

What the grammar reads today, and what comes next, is in
[Status and roadmap](roadmap.md).
