# Writing for Proofread

Proofread reads an article the way a careful referee does: every symbol has to
be defined before it is used, every sentence has one meaning, and a proof step
may use only what it cites. The conventions below are ordinary good style for
mathematical writing. Following them is what lets the same `.tex` file be
typeset for a journal and compiled to Lean.

A sentence that matches none of the constructions is *prose*. Prose is fine:
motivation, remarks and proof sketches stay prose. It is shown in the reader
and in the diagnostics, but it asserts nothing checked. Inside results and
proofs, prose is reported, so uncompiled mathematics stays visible.

The examples are from *Rank weighting and asymmetry in Blest's rank
correlation* (arXiv:2609.27634) and *The exact region determined by Spearman's
rho and Gini's gamma* (arXiv:2609.19890), compiled in `lean-verifications`
(`Papers/Rockel2026ExactBlest/Source`,
`Papers/AnsariRockelSteinmassl2026RhoGamma/Source`). Each folder's
`article-edits.diff` shows every edit that the conventions asked for.

## House style

1. **Define before use.** The defining sentence of a symbol comes before its
   first use. Its definition is its only meaning, so defining a symbol twice is
   an error. Preamble macros (`\newcommand`, `\DeclareMathOperator`) are
   expanded first.
2. **Write definitions with `\coloneqq`.** `\nu(C)\coloneqq24\int…` defines
   `\nu`. `\nu(C)=24\int…` is a claim about a `\nu` that must already exist.
3. **One definition or claim per sentence.** Move side remarks into their own
   sentence. "We refer to \cite{…} for background." is a sentence of its own,
   and so is "This normalization makes $\nu(M)=1$, …".
4. **Name the class of the argument.** Write "For a copula $C$, the
   population version of Blest's rank correlation is …", "For $c\in[0,1]$, let
   $D_c$ denote …". A family gets its parameter domain in the sentence that
   introduces it: "For $w\in[0,1]$, let $A_w$ be the copula associated with
   $\gamma_{T_w}$", not "indexed by $w\in[0,1]$: let …".
5. **Give every map its signature.** "where $T_w:[0,1]\to[0,1]$ is given by
   …", "define $\Phi:[-1,1]\to[-1,1]$ by …". A parametrized piece states its
   parameter range on the same line: `e_b\coloneqq…,\qquad b\in(0,\tfrac12]`.
6. **Make every quantifier explicit.** "for every $r\in[-1,1]$" instead of a
   free $r$. A variable bound at the start of a result ("For $w\in[0,1]$, …")
   stays bound in the result's later sentences that use it.
7. **Cite what a step uses.** "By Lemma~\ref{…}, …", "…, by \eqref{…}",
   "\eqref{…} gives …". A proof sentence may use the earlier sentences of its
   proof and the results it cites, and nothing else. The citation audit rejects
   a Lean justification that uses anything more.
8. **Split a statement into its claims.** "Both constants are sharp. The
   maximum $\frac{27}{128}$ of $\nu-\eta$ is attained only by $A_{3/4}$, …" is
   two sentences: a remark and a claim.
9. **Decimal values are approximations.** Write `g_*\coloneqq\frac{173-16\sqrt3}{363}\approx0.4002`,
   not `=0.4002\ldots`: an `\approx` value is an illustration and asserts
   nothing.
10. **Image sets name the class of their variable.** Write
    `\{\rho(C):C\in\CC,\ \gamma(C)=0\}`, not `\{\rho(C):\gamma(C)=0\}`.
11. **No semicolons in prose.** A semicolon joins two claims without saying how
    they relate. Use a period, ", and", ", so" or ", whereas".
12. **Fixed variables stay fixed.** "fix $b\in(0,\frac12)$" binds `b` for the
    following sentences of the section, and "Let $w\in[\frac12,1)$." at the
    start of a result binds `w` for the rest of the result. A symbol defined
    under a binder whose name does not show the variable (`z_-(x)` under "For
    $b\in(0,\frac12]$") depends on it implicitly: each use takes the `b` of its
    context.
13. **Overloading needs disjoint domains.** A family defined again on a further
    parameter domain (`\kappa_w` for `w\in[\frac12,1)`, later `\kappa_b` for
    `b\in(0,\frac12)`) is one family on the union. Its well-definedness asks
    that the domains do not overlap, which is the paper's "no confusion can arise".

## Definitions

| Form | Example |
| --- | --- |
| class | `let $\CC$ denote the class of bivariate copulas, that is, distribution functions on $[0,1]^2$ with uniform marginals.` |
| quantity of an object | `For a copula $C$, the population version of Blest's rank correlation is \begin{equation}\nu(C)\coloneqq…\end{equation}` |
| several quantities | `For a copula $C$, the transpose of $C$ is $C^\top(u,v)\coloneqq C(v,u)$, and the survival copula of $C$ is …` |
| map with signature | `define $\Phi:[-1,1]\to[-1,1]$ by \[…\]` (a `cases` display is a piecewise definition; a piece may follow as `on $(-1,-\frac34)$, parametrically by \[…\]`) |
| definition with an observation | `… and observe that $2r-\Phi(r)=-\Phi(-r)$ for every $r\in[-1,1]$.` (the observation is a claim) |
| family | `For $c\in[0,1]$, let $D_c$ denote the copula associated with $\gamma_{\zeta_c}$ from Section~\ref{sec:preliminaries}.` |
| family with a local map | `For $w\in[0,1]$, let $A_w$ be the copula associated with $\gamma_{T_w}$, where $T_w:[0,1]\to[0,1]$ is given by \begin{equation}…\end{equation}` |
| auxiliary symbol | `For $b\in(0,\frac12]$, set $z_b\coloneqq\frac{b}{2(1-b)}$ and let $B_b$ be …` |
| named map | `For $c\in[0,1]$, the corresponding rank map $\zeta_c:[0,1]\to[0,1]$ reads \[…\]` |
| notion of the vocabulary | `Lebesgue measure on $[0,1]$ is denoted by $\mathrm{Leb}$.` |
| relation | `We say that a copula $C$ is \emph{supported on the graph} of a Borel measurable $f:[0,1]\to[0,1]$ if $C(u,v)=…$ for all $u,v\in[0,1]$.` |
| class of the vocabulary | `Let $\CC$ denote the class of bivariate copulas.`, `We denote by $\mathcal{C}$ the set of bivariate copulas.` |
| two quantities at once | `For a copula $C$, Spearman's rho and Gini's gamma are \begin{equation}\rho(C)\coloneqq…,\qquad\gamma(C)\coloneqq….\end{equation}` |
| constants | `Set $r_0\coloneqq\frac{144+9\sqrt6}{500}\approx0.33209$.`, `Define \begin{equation}d_0\coloneqq…,\qquad\Delta_0\coloneqq….\end{equation}` |
| a named set | `The exact region between Spearman's rho and Gini's gamma is \begin{equation}\Om\coloneqq\{(\rho(C),\gamma(C)):C\in\CC\}.\end{equation}` |
| a maximum | `For $g\in[-1,1]$, set \begin{align}\rhoup(g)\coloneqq\max\{\rho(C):C\in\CC,\ \gamma(C)=g\}.\end{align}` (a definite description: well defined when the maximum exists) |
| a fixed variable | `To describe the supporting lines of the region, fix $\kappa>0$ and define \[d_\kappa(x,z)\coloneqq x^2z-\kappa\,xz^2.\]`, `For the second regime, fix $b\in(0,\frac12)$ and put $\kappa_b\coloneqq\frac{2(1-b)}{b}$.` |
| an implicit parameter | `For $b\in(0,\frac12]$, set \begin{equation}z_-(x)\coloneqq\frac{x+b-1}{2(1-b)},\qquad z_+(x)\coloneqq\frac{1-b-(1-2b)x}{2(1-b)}.\end{equation}` |
| value and derivative | `define continuous functions $\varphi_w,\psi_w:[0,1]\to\R$ by $\varphi_w(1-w)=0$, $\psi_w(0)=0$, and DISPLAY` with `\varphi_w'(x)=\begin{cases}…\end{cases}` in the display, or `Let $\varphi_b,\psi_b:[0,1]\to\R$ be continuous, normalized by $\varphi_b(1-b)=0$ and $\psi_b(0)=0$, with derivatives DISPLAY` (read as `φ(x) = φ(a) + ∫_a^x φ'`; the derivative may be given on open pieces) |
| a set of pairs | `For $w\in[\frac12,1)$, the support of $\gamma_{T_w}$ is \[S_w\coloneqq\{(x,1-x):0\le x\le1-w\}\cup\{(x,x+w-1):1-w\le x\le1\}.\]` (unions `\cup`, products `[a,b]\times\{c\}`) |
| the variable of a result | `Let $w\in[\frac12,1)$.` |
| law of a construction | `For a Borel measurable $T:[0,1]\to[0,1]$, let $\gamma_T$ denote the law of $(X,T(X))$ for $X$ uniformly distributed on $[0,1]$.` |

## Claims

A claim sentence is an optional discourse marker ("Hence", "In particular",
"Consequently", …), optional binders ("For every $x\in A$,", "For a copula
$C$,", "On $I$,"), and clauses joined by ", and" or ", so", each with its
citations.

| Form | Example |
| --- | --- |
| formula, chain, equivalence | `$\lvert\nu(C)-\rho(C)\rvert\le\frac14$`, `$0\le\Upsilon(e)\le\frac{27}{128}$ for every $e\in[-1,1]$` |
| exact region | `It holds that \[\bigl\{(\rho(C),\nu(C)):C\in\CC\bigr\}=\bigl\{(r,n)\in[-1,1]^2:2r-\Phi(r)\le n\le\Phi(r)\bigr\}.\]` |
| unique attainment | `exactly one copula $C$ with $\rho(C)=r$ satisfies $\nu(C)=\Phi(r)$` |
| the only one | `its survival copula is the only copula with $\rho=r$ and $\nu=2r-\Phi(r)$` |
| extremum | `The maximum $\frac{27}{128}$ of $\nu-\eta$ is attained only by $A_{3/4}$, at which $(\eta,\nu)=(-\frac{5}{32},\frac{7}{128})$, and the minimum $-\frac{27}{128}$ only by $A_{3/4}^\top$.` |
| monotone bijection | `$c\mapsto\rho(D_c)$ increases bijectively from $[0,1]$ onto $[-1,1]$` |
| monotone maps, ranges | `Both parameter maps $w\mapsto\eta(A_w)$ and $b\mapsto\eta(B_b)$ are strictly increasing. For $w\in[\frac12,1]$, the first ranges over $[-\frac34,1]$, …` |
| derivative | `whose derivative $1-(1+r)^{1/3}$ is positive for $r<0$` |
| relation | `$D_{1/2}$ is supported on the graph of the tent map $u\mapsto\min\{2u,2-2u\}$` |
| transformation | `the map $C\mapsto\widehat C$ sends $\nu-\rho$ to $\rho-\nu$ by \eqref{eq:survival-transform}` |
| condition | `If $-1\le g\le g_*$, then \begin{equation}\rhoup(g)=\frac{144+420g+(9+65g)\sqrt{6-10g}}{500}.\end{equation}` |
| maximum of a quantity | `Then \begin{equation}\max_{C\in\CC}|\rho(C)-\gamma(C)|=\Delta_0.\end{equation}` |
| image sets | `\{\rho(C):C\in\CC,\ \gamma(C)=0\}=[-r_0,r_0]` |
| extrema at a fixed value | `For every $n\in[-1,1]$, the maximum $\Lambda(n)$ and the minimum $\Lambda^{-1}(n)$ of $\nu(C^\top)$ over all copulas $C$ with $\nu(C)=n$ are each attained by exactly one copula.` |
| an inequality on a square | `Then every $(x,z)\in[0,1]^2$ satisfies \begin{equation}\varphi_w(x)+\psi_w(z)\ge d_{\kappa_w}(x,z).\end{equation}` |
| sharpness | `Both constants are sharp.` (after a claim `a\le c` about every element of a domain: for every `ε > 0` some element has `c - a < ε`) |
| shape | `Moreover, $\Om$ is compact, convex and centrally symmetric, and $\rhoup$ is continuous, concave and strictly increasing.` (a function on the domain its definition states) |
| equality sets | `If $w>\frac12$, equality holds exactly on $S_w$, and if $w=\frac12$, it holds exactly on $S_{1/2}\cup([\frac12,1]\times\{\frac12\})$.`, `…, and equality holds exactly when $x=R_b(z)$.` (about the preceding inequality, for every point of its domain) |

The readings are fixed and documented next to each construction in
`Proofread/Grammar.lean` (parsing) and `Proofread/Doc.lean` (meaning). Run
`lake exe proofread check article.tex --claims` to see the formal reading of
every claim while you write.

## Proofs

Inside `\begin{proof}`, a sentence may use the earlier sentences of the same
proof and the results cited so far in it. When every sentence of a proof
compiles, the result it proves gets those sentences and citations as its
premises, and the result is *derived in the text*. Sentences that only
organize the argument ("Nonnegativity away from that set is proved rectangle by
rectangle.") are prose and assert nothing.

## Checking while writing

```sh
lake exe proofread check article.tex --vocab unitsquare            # undefined symbols, failed sentences
lake exe proofread check article.tex --vocab unitsquare --claims   # and the reading of every claim
lake exe proofread check article.tex --vocab unitsquare --prose    # and the prose inside results and proofs
```

The check takes about a second and certifies nothing. `lake build` of the
certifying module checks everything in the kernel. `editors/vscode/tasks.json`
shows both as problems in the `.tex` file.
