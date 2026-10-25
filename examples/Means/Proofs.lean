import Means.Article

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

namespace Means.Proofs
open Means

/-! Square roots in the article are powers `x ^ (1/2)`. -/

theorem rpow_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

/-- The arithmetic mean of two positive numbers is positive, so it may divide. -/
theorem A_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < A x y := by
  unfold A
  positivity

/-! ## Definitions: `d`, `A`, `G`, `H`, `Q` -/

theorem defined0 : wellDefined0 := by
  unfold wellDefined0
  definedness []

theorem defined1 : wellDefined1 := by
  unfold wellDefined1
  definedness []

theorem defined2 : wellDefined2 := by
  unfold wellDefined2
  definedness []

theorem defined3 : wellDefined3 := by
  unfold wellDefined3
  definedness []

theorem defined4 : wellDefined4 := by
  unfold wellDefined4
  definedness []

/-! ## Lemma 1 and its proof -/

/-- `We have $(\sqrt a)^2=a$, …` -/
theorem proof1 : obligation1 := by
  intro_premises
  exact ⟨by unfold meaningful1; definedness [], fun x hx => rpow_half_sq hx.le⟩

/-- `…, $(\sqrt b)^2=b$ …` -/
theorem proof2 : obligation2 := by
  intro_premises
  exact ⟨by unfold meaningful2; definedness [], fun x hx => rpow_half_sq hx.le⟩

/-- `… and $\sqrt a\sqrt b=\sqrt{ab}$.` -/
theorem proof3 : obligation3 := by
  intro_premises
  exact ⟨by unfold meaningful3; definedness [], fun x hx y hy => (Real.mul_rpow hx.le hy.le).symm⟩

/-- `Hence $\frac{d^2}{2}=\frac{a-2\sqrt{ab}+b}{2}=\frac{a+b}{2}-\sqrt{ab}$.` -/
theorem proof4 : obligation4 := by
  intro_premises
  refine ⟨by unfold meaningful4; definedness [], fun x hx y hy => ⟨?_, by ring⟩⟩
  simp only [d]
  rw [show (x ^ (1 / 2 : ℝ) - y ^ (1 / 2 : ℝ)) ^ 2 =
      (x ^ (1 / 2 : ℝ)) ^ 2 - 2 * (x ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ)) + (y ^ (1 / 2 : ℝ)) ^ 2 by ring,
    c1 x hx, c2 y hy, c3 x hx y hy]

/-- Lemma 1, from its proof. -/
theorem proof0 : obligation0 := by
  intro_premises
  exact ⟨by unfold meaningful0; definedness [], fun x hx y hy =>
    ((c4 x hx y hy).1.trans (c4 x hx y hy).2).symm⟩

/-! ## Theorem 2 and its proof -/

/-- `By Lemma 1, $A-G=\frac{(\sqrt a-\sqrt b)^2}{2}\ge0$.` -/
theorem proof7 : obligation7 := by
  intro_premises
  refine ⟨by unfold meaningful7; definedness [], fun x hx y hy => ⟨?_, by positivity⟩⟩
  have h := c0 x hx y hy
  simp only [d] at h
  simp only [A, GDef]
  exact h

/-- `Hence $G\le A$, …` -/
theorem proof8 : obligation8 := by
  intro_premises
  refine ⟨by unfold meaningful8; definedness [], fun x hx y hy => ?_⟩
  obtain ⟨h, h'⟩ := c7 x hx y hy
  linarith

/-- `… and $G=A$ if and only if $\sqrt a=\sqrt b$.` -/
theorem proof9 : obligation9 := by
  intro_premises
  refine ⟨by unfold meaningful9; definedness [], fun x hx y hy => ?_⟩
  obtain ⟨h, -⟩ := c7 x hx y hy
  constructor
  · intro hGA
    have : (x ^ (1 / 2 : ℝ) - y ^ (1 / 2 : ℝ)) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  · intro hxy
    rw [hxy, sub_self] at h
    linarith

/-- `Moreover, $\sqrt a=\sqrt b$ if and only if $a=b$, …` -/
theorem proof10 : obligation10 := by
  intro_premises
  refine ⟨by unfold meaningful10; definedness [], fun x hx y hy => ?_⟩
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_inj hx.le hy.le

/-- `Finally, $H=\frac{G^2}{A}$.` -/
theorem proof11 : obligation11 := by
  intro_premises
  refine ⟨by unfold meaningful11; definedness [(A_pos ‹_› ‹_›).ne'], fun x hx y hy => ?_⟩
  simp only [H, GDef, A]
  rw [rpow_half_sq (by positivity)]
  field_simp

/-- `Since $G\le A$ …` -/
theorem proof12 : obligation12 := by
  intro_premises
  exact ⟨by unfold meaningful12; definedness [], c8⟩

/-- `… and $G>0$, …` -/
theorem proof13 : obligation13 := by
  intro_premises
  refine ⟨by unfold meaningful13; definedness [], fun x hx y hy => ?_⟩
  simp only [GDef]
  positivity

/-- `… it follows that $H=G\cdot\frac{G}{A}\le G$.` -/
theorem proof14 : obligation14 := by
  intro_premises
  refine ⟨by unfold meaningful14; definedness [(A_pos ‹_› ‹_›).ne'], fun x hx y hy => ⟨?_, ?_⟩⟩
  · rw [c11 x hx y hy]
    ring
  · have hG := c13 x hx y hy
    have hA : 0 < A x y := lt_of_lt_of_le hG (c12 x hx y hy)
    have hq : GDef x y / A x y ≤ 1 := (div_le_one hA).mpr (c12 x hx y hy)
    nlinarith

/-- Theorem 2, `$H\le G\le A$`, from its proof. -/
theorem proof5 : obligation5 := by
  intro_premises
  refine ⟨by unfold meaningful5; definedness [], fun x hx y hy => ⟨?_, c8 x hx y hy⟩⟩
  obtain ⟨h, h'⟩ := c14 x hx y hy
  rw [h]
  exact h'

/-- Theorem 2, the case of equality, from its proof. -/
theorem proof6 : obligation6 := by
  intro_premises
  exact ⟨by unfold meaningful6; definedness [], fun x hx y hy => (c9 x hx y hy).trans (c10 x hx y hy)⟩

/-! ## Remark 3 (stated without proof) -/

theorem proof15 : obligation15 := by
  intro_premises
  refine ⟨by unfold meaningful15; definedness [], fun x hx y hy => ?_⟩
  simp only [Q]
  rw [← Real.sqrt_eq_rpow]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (x - y)]

end Means.Proofs
