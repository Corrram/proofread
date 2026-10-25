import Squares.Article
import Mathlib.Tactic.Ring

/-! # Proofs of the example's obligations

* claim 0 (Lemma 1) has no proof in the text, so any Lean proof will do;
* claims 2 and 3 are the two sentences of the proof of Theorem 2: each follows
  from what it cites (claim 3 cites Lemma 1);
* claim 1 (Theorem 2) is closed by its compiled proof, so it follows from the
  two proof sentences alone.

`#proofread_certify` audits the last three: their proofs may use only Lean,
mathlib, Proofread and the compiled article. -/

namespace Squares.Proofs
open Squares

theorem defined0 : wellDefined0 := by unfold wellDefined0; definedness []

theorem proof0 : obligation0 := by
  intro_premises
  exact ⟨by unfold meaningful0; definedness [], fun x => sq_nonneg x⟩

theorem proof2 : obligation2 := by
  intro_premises
  refine ⟨by unfold meaningful2; definedness [], fun x y => ?_⟩
  simp only [q]
  ring

theorem proof3 : obligation3 := by
  intro_premises
  exact ⟨by unfold meaningful3; definedness [], fun x y => c0 (x - y)⟩

theorem proof1 : obligation1 := by
  intro_premises
  refine ⟨by unfold meaningful1; definedness [], fun x y => ?_⟩
  have h2 := c2 x y
  have h3 := c3 x y
  linarith

end Squares.Proofs
