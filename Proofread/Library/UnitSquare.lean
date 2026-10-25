import Proofread.Vocab

/-! # Vocabulary: probability on the unit square

Distribution functions and probability measures on `[0,1]^2`, uniform
marginals, and (bivariate) copulas: distribution functions on `[0,1]^2` with
uniform marginals. The meanings of the four constants are given in
`Proofread.Library.UnitSquareModel` (`UnitSquare.model`). -/

namespace Proofread.UnitSquare

/-- Constant indices (in this vocabulary). -/
def distFn : Nat := 0
def distFnUniform : Nat := 1
def probMeasure : Nat := 2
def measUniform : Nat := 3

def vocab : Vocab where
  consts := [Ty.sq ⟶ .prop, Ty.sq ⟶ .prop, Ty.meas2 ⟶ .prop, Ty.meas2 ⟶ .prop]
  constNames := [w!"\\operatorname{DistFn}_{[0,1]^2}", w!"\\operatorname{UnifMarg}",
    w!"\\operatorname{Prob}_{[0,1]^2}", w!"\\operatorname{UnifMarg}"]
  nouns := [
    { sing := phrase!"distribution function on $[0,1]^2$",
      plural := phrase!"distribution functions on $[0,1]^2$", ty := Ty.sq, pred := .const 0 },
    { sing := phrase!"probability measure $v$ on $[0,1]^2$",
      plural := phrase!"probability measures $v$ on $[0,1]^2$", ty := Ty.meas2, pred := .const 2 },
    -- a (bivariate) copula: a distribution function on `[0,1]^2` with uniform marginals
    { sing := phrase!"bivariate copula", plural := phrase!"bivariate copulas", ty := Ty.sq,
      pred := .lam Ty.sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))) },
    { sing := phrase!"copula", plural := phrase!"copulas", ty := Ty.sq,
      pred := .lam Ty.sq .tt (.and (.app (.const 0) (.loc 0)) (.app (.const 1) (.loc 0))) }]
  mods := [
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.sq, pred := .const 1 },
    { phrase := phrase!"with uniform marginals", prenominal := false, ty := Ty.meas2, pred := .const 3 }]

/-- The core vocabulary followed by this one: what an article about probability on
the unit square is compiled with. -/
def withCore : Vocab := Vocab.core ++ vocab

end Proofread.UnitSquare
