# Status and next constructions

## Where the exemplars stand

| Article | Definitions | Claims | Verified | Not read yet |
| --- | ---: | ---: | ---: | --- |
| Blest (`Papers/Rockel2026ExactBlest/Source`) | 37 | 48 | 48 | Lemmas 2.1, 2.2 and 4.2, the last two sentences of Corollary 4.6 |
| Rho-gamma (`Papers/AnsariRockelSteinmassl2026RhoGamma/Source`) | 11 | 8 | 8 | the parametrization `G`, `P` of Theorem 1.1, the lemmas of Sections 3–5 |

Every result of the Blest article whose statement is about copulas, the
coefficients and the families of Section 4 is compiled and certified: Theorems
1.1 and 1.2, Lemmas 3.1 and 4.1, Propositions 4.3 and 4.4, Corollaries 3.2 (with
its proof, sentence by sentence) and 4.5. What remains needs constructions the
grammar does not have yet.

## Next constructions

1. **Random pairs and expectations under a coupling.** Lemma 2.1 ("If $(X,Z)$
   follows the coupling associated with $C\in\CC$, then $\rho(C)=12\,\E[XZ]-3$")
   and part (a) of Lemma 4.2 ("Every $\gamma\in\Gam$ satisfies
   $\E_\gamma[c(X,Z)]\le\int_0^1\varphi+\int_0^1\psi$"). Reading: `E_γ[f(X,Z)]` is
   the integral of `f` against the measure `γ`; "the coupling associated with `C`"
   is the definite description inverse to "the copula associated with `γ`".
2. **Results that quantify over functions with properties.** Lemma 4.2 begins
   "Let $c:[0,1]^2\to\R$ and $\varphi,\psi:[0,1]\to\R$ be continuous functions
   such that …". Binders of function type with hypotheses, and finite sets
   (`N_1, N_2`).
3. **Arbitrary probability spaces.** Lemma 2.2 speaks of random variables on "the
   same probability space". Its reading quantifies over all probability spaces,
   which needs a vocabulary whose model is parametric in the space.
4. **Anaphora to extremizers.** Corollary 4.6: "For $n=-1$, this copula is $W$."
   and the identification of the maximizer as `A_w^\top` or `B_b^\top`. This also
   needs the defining sentence of `M`, `W`, `\Pi` in the introduction.
5. **Local hypotheses in proofs.** The proofs of Propositions 4.3 and 4.4 argue
   rectangle by rectangle ("On the first rectangle, …"). A proof step about a
   region of the square needs the region as a scoped hypothesis.
6. **Parametric families of copulas defined by a construction**: the extremizers
   `C_\theta` of the rho-gamma article (Section 3, `def:extremizers`), which
   Theorem 1.1 uses through `G(\theta)` and `P(\theta)`.
7. **Markov kernels of copulas.** "We call a copula $C$ \emph{stochastically
   increasing} (\emph{SI}) if its Markov kernel can be chosen such that, for
   every $v\in(0,1)$, the map $t\mapsto K_C(t,[0,v])$ is non-increasing." The
   sentence is a notion in the running text, which the grammar reads, but its
   condition needs the Markov kernel `K_C` in the vocabulary, as a kernel
   determined up to null sets, with "can be chosen such that" read as an
   existential over its versions. Tail monotonicity (LTD, RTI) needs no kernel
   and is read today ([`examples/TailDependence`](../examples/TailDependence)).

Each construction gets one documented reading in `Proofread/Grammar.lean` and
`Proofread/Doc.lean`, an example in `docs/writing.md`, and an exemplar sentence
that compiles and is certified.
