import Lean
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Tauto

/-! # Tactics for writing justifications of compiled claims -/
namespace Proofread
open Lean Elab Tactic Meta

/-- The number `K` in a generated name `claimK`. -/
def claimIndex? (n : Name) : Option Nat :=
  match n with
  | .str _ s => if s.startsWith "claim" then (String.ofList (s.toList.drop 5)).toNat? else none
  | _ => none

/-- `intro_premises` unfolds a goal `obligationK` and introduces its premises:
the premise `meaningfulJ ∧ claimJ` becomes `mJ : meaningfulJ` and `cJ : claimJ`. -/
elab "intro_premises" : tactic => do
  let ty ← instantiateMVars (← (← getMainGoal).getType)
  if let .const n _ := ty then
    evalTactic (← `(tactic| unfold $(mkIdent n):ident))
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | fuel + 1 => do
      let ty ← instantiateMVars (← (← getMainGoal).getType)
      match ty with
      | .forallE _ (.app (.app (.const ``And _) (.const _ _)) (.const c _)) _ _ =>
        match claimIndex? c with
        | some k =>
          let mI := mkIdent (Name.mkSimple s!"m{k}")
          let cI := mkIdent (Name.mkSimple s!"c{k}")
          evalTactic (← `(tactic| rintro ⟨$mI:ident, $cI:ident⟩))
          loop fuel
        | none => pure ()
      | _ => pure ()
  loop 1000

/-- `definedness [t₁, …]` proves a definedness condition (`meaningfulK`, `wellDefinedI`):
a tree of `∧`, `→` and `∀` whose leaves are hypotheses, numeric side conditions
or the given facts, and whose impossible branches (contradictory case
conditions) are closed by `linarith` or `tauto`. -/
elab "definedness" " [" ts:term,* "]" : tactic => do
  let leaf ← ts.getElems.foldlM (fun acc t => do
    let accS ← `(Lean.Parser.Tactic.tacticSeq| $acc:tactic)
    `(tactic| first | $accS | exact $t)) (← `(tactic| assumption))
  let step ← `(tactic| first
    | $leaf:tactic
    | (norm_num; done)
    | (intro _; try casesm* _ ∧ _)
    | refine ⟨?_, ?_⟩
    | (linarith; done)
    -- a branch whose case conditions contradict each other
    | (exfalso; tauto; done)
    -- uncovered cases: the negated case conditions contradict the domain
    | (exfalso; (try simp only [not_and_or, not_le, not_lt, ← ne_eq, ne_iff_lt_or_gt] at *);
        (casesm* _ ∨ _) <;> linarith))
  let stepS ← `(Lean.Parser.Tactic.tacticSeq| $step:tactic)
  evalTactic (← `(tactic| repeat' $stepS))

end Proofread
