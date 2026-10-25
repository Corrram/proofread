import Refuted.Article

/-! # Proofs of the definitions and claims of `article.tex`

* `definedI : wellDefinedI`: definition `I` makes sense (no division by zero, every
  argument in its domain). `definedness [h₁, …]` proves most of these; give it the
  facts it cannot find.
* `proofK : obligationK`: claim `K` holds. `intro_premises` introduces
  `cJ : claimJ` for each premise `J` (in a proof, the earlier steps and the cited
  results). A claim the text derives (a proof step, or a result with a compiled
  proof) may use only its premises, Mathlib and the article: `#proofread_certify`
  audits this.
* `refuteK : meaningfulK ∧ ¬ claimK` instead records that claim `K` is false as
  stated; readers and the PDF margin then mark it.

A proof that still uses `sorry` leaves its claim unverified, and `lake build`
certifies the others. -/

namespace Refuted.Proofs
open Refuted

/-- Definition 0: `f` is well defined. -/
theorem defined0 : wellDefined0 := by
  unfold wellDefined0
  definedness []

/-- Claim 0, statement (lemma at line 31; premises: claim 1):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(x)-2=\frac{{(x-1)}^{2}}{x}` -/
theorem proof0 : obligation0 := by
  intro_premises
  refine ⟨by unfold meaningful0; definedness [], fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := c1 x hx
  rw [h1, h2, h3]

/-- Claim 1, proof step (proof at line 36; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(x)-2=x+\frac{1}{x}-2\land x+\frac{1}{x}-2=\frac{{x}^{2}-2\,x+1}{x}\land \frac{{x}^{2}-2\,x+1}{x}=\frac{{(x-1)}^{2}}{x}` -/
theorem proof1 : obligation1 := by
  intro_premises
  refine ⟨by unfold meaningful1; definedness [], fun x hx => ⟨by simp only [f], ?_, by ring⟩⟩
  field_simp
  ring

/-- Claim 2, statement (theorem at line 40; premises: claim 3, claim 4, claim 0):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 2<f(x)` -/
theorem refute2 : meaningful2 ∧ ¬ claim2 := by
  refine ⟨by unfold meaningful2; definedness [], fun h => ?_⟩
  -- at x = 1 the two sides are equal
  have h1 := h 1 one_pos
  norm_num [f] at h1

/-- Claim 3, proof step (proof at line 45; no premises):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow 0\le \frac{{(x-1)}^{2}}{x}` -/
theorem proof3 : obligation3 := by
  intro_premises
  refine ⟨by unfold meaningful3; definedness [], fun x hx => ?_⟩
  positivity

/-- Claim 4, proof step (proof at line 46; premises: claim 0, claim 3):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(x)-2=\frac{{(x-1)}^{2}}{x}\land 0\le \frac{{(x-1)}^{2}}{x}` -/
theorem proof4 : obligation4 := by
  intro_premises
  exact ⟨by unfold meaningful4; definedness [], fun x hx => ⟨c0 x hx, c3 x hx⟩⟩

/-- Claim 5, statement (corollary at line 50; premises: claim 6, claim 2):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(1)\le f(x)` -/
theorem proof5 : obligation5 := by
  intro_premises
  refine ⟨by unfold meaningful5; definedness [], fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := c6 x hx
  rw [h1]
  exact h2

/-- Claim 6, proof step (proof at line 54; premises: claim 2):
`\forall x\in \mathbb{R},\ 0<x\Rightarrow f(1)=2\land 2\le f(x)` -/
theorem proof6 : obligation6 := by
  intro_premises
  refine ⟨by unfold meaningful6; definedness [], fun x hx => ⟨?_, (c2 x hx).le⟩⟩
  norm_num [f]

end Refuted.Proofs
