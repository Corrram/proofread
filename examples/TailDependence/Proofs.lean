import TailDependence.Article

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

namespace TailDependence.Proofs
open TailDependence
open scoped unitInterval

/-! ## Two facts about copulas

A copula of the model is the distribution function of a probability measure on
`[0,1]^2` with uniform marginals. It vanishes on the left edge of the square, and
its value on the right edge is the second coordinate. -/

theorem copula_zero_left {C : I → I → ℝ} (hC : copulas C) (v : I) : C 0 v = 0 := by
  obtain ⟨⟨μ, hμ, hF⟩, hu, -⟩ := hC
  have h01 : C 0 1 = 0 := by simpa using hu 0
  have hmono : μ (Set.Iic 0 ×ˢ Set.Iic v) ≤ μ (Set.Iic 0 ×ˢ Set.Iic 1) :=
    MeasureTheory.measure_mono (Set.prod_mono le_rfl (Set.Iic_subset_Iic.mpr unitInterval.le_one'))
  have hle := ENNReal.toReal_mono (MeasureTheory.measure_ne_top μ _) hmono
  rw [hF] at h01 ⊢
  linarith [ENNReal.toReal_nonneg (a := μ (Set.Iic 0 ×ˢ Set.Iic v))]

theorem copula_one_left {C : I → I → ℝ} (hC : copulas C) (v : I) : C 1 v = v := hC.2.2 v

theorem projIcc_one : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : I) := by
  rw [Set.projIcc_right]; rfl

theorem projIcc_zero : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : I) := by
  rw [Set.projIcc_left]; rfl

theorem projIcc_coe (u : I) : Set.projIcc (0 : ℝ) 1 zero_le_one u = u := Set.projIcc_val zero_le_one u

/-! ## Definitions -/

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

/-! ## Proposition 1: every LTD copula is PQD -/

/-- `If $u=0$, then $C(u,v)=0=uv$.` -/
theorem proof1 : obligation1 := by
  intro_premises
  refine ⟨by unfold meaningful1; definedness [], fun C ⟨hC, _⟩ u v hu => ?_⟩
  have h : u = 0 := Subtype.ext hu
  subst h
  exact ⟨copula_zero_left hC v, by simp⟩

/-- `If $u>0$, then $\frac{C(u,v)}{u}\ge C(1,v)=v$ by \eqref{eq:ltd}.` -/
theorem proof2 : obligation2 := by
  intro_premises
  refine ⟨by unfold meaningful2; definedness [], fun C ⟨hC, hL⟩ u v hu => ?_⟩
  have h := hL v u ⟨hu, u.2.2⟩ 1 ⟨one_pos, le_rfl⟩ u.2.2
  rw [projIcc_one, projIcc_coe, div_one] at h
  rw [projIcc_one]
  exact ⟨h, copula_one_left hC v⟩

/-- `Hence $C(u,v)\ge uv$.` -/
theorem proof3 : obligation3 := by
  intro_premises
  refine ⟨by unfold meaningful3; definedness [], fun C hCL u v => ?_⟩
  rcases (unitInterval.nonneg u).eq_or_lt with h0 | hpos
  · obtain ⟨h1, h2⟩ := c1 C hCL u v h0.symm
    linarith
  · obtain ⟨h1, h2⟩ := c2 C hCL u v hpos
    rw [h2, le_div_iff₀ hpos] at h1
    linarith

/-- Proposition 1, from its proof. -/
theorem proof0 : obligation0 := by
  intro_premises
  exact ⟨by unfold meaningful0; definedness [], fun C hCL u v => c3 C hCL u v⟩

/-! ## Proposition 2: every RTI copula is PQD -/

/-- `If $u=1$, then $C(u,v)=v=uv$.` -/
theorem proof5 : obligation5 := by
  intro_premises
  refine ⟨by unfold meaningful5; definedness [], fun C ⟨hC, _⟩ u v hu => ?_⟩
  have h : u = 1 := Subtype.ext hu
  subst h
  exact ⟨copula_one_left hC v, by simp⟩

/-- `If $u<1$, then $\frac{1-u-v+C(u,v)}{1-u}\ge1-v+C(0,v)=1-v$ by \eqref{eq:rti}.` -/
theorem proof6 : obligation6 := by
  intro_premises
  refine ⟨by unfold meaningful6; definedness [], fun C ⟨hC, hR⟩ u v hu => ?_⟩
  have h := hR v 0 ⟨le_rfl, one_pos⟩ u ⟨u.2.1, hu⟩ u.2.1
  rw [projIcc_zero, projIcc_coe, sub_zero, div_one] at h
  rw [projIcc_zero, copula_zero_left hC v]
  rw [copula_zero_left hC v] at h
  exact ⟨by linarith, by ring⟩

/-- `Hence $C(u,v)\ge uv$.` -/
theorem proof7 : obligation7 := by
  intro_premises
  refine ⟨by unfold meaningful7; definedness [], fun C hCR u v => ?_⟩
  rcases (unitInterval.le_one u).eq_or_lt with h1 | hlt
  · obtain ⟨h, h'⟩ := c5 C hCR u v h1
    linarith
  · obtain ⟨h, h'⟩ := c6 C hCR u v hlt
    rw [h', le_div_iff₀ (by linarith)] at h
    nlinarith

/-- Proposition 2, from its proof. -/
theorem proof4 : obligation4 := by
  intro_premises
  exact ⟨by unfold meaningful4; definedness [], fun C hCR u v => c7 C hCR u v⟩

end TailDependence.Proofs
