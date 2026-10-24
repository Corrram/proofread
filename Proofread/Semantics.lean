import Proofread.Doc

/-! # What a compiled article asserts, and when it is verified

`Doc.holds d G k`: claim `k` is meaningful and true, where `G` are the values of
the article's definitions. A `Certificate` states that the definitions evaluate
to `G` and are well defined, that every verified claim follows from its
premises, and that premises are ranked below the claims that use them (so the
premise structure has no cycles). `Certificate.sound` then gives every verified
claim. -/
namespace Proofread

namespace Doc

noncomputable def env (d : Doc) : Option (List Val) := evalDefs [] d.values

def premisesOf (d : Doc) (k : Nat) : List Nat := (d.claims[k]?.map (·.premises)).getD []

noncomputable def holds (d : Doc) (G : List Val) (k : Nat) : Prop :=
  match d.claims[k]? with
  | some c => Val.prop (denote G [] c.body.sound)
  | none => False

noncomputable def welldef (d : Doc) (G : List Val) (i : Nat) : Prop :=
  match d.values[i]? with
  | some v => Val.prop (denote G [] v.defined)
  | none => False

/-- Premises of verified claims are verified and of lower rank. -/
def ranked (d : Doc) (verified : List Nat) (rank : List Nat) : Bool :=
  verified.all fun k => (d.premisesOf k).all fun j =>
    verified.contains j && decide (rank.getD j 0 < rank.getD k 0)

end Doc

structure Certificate (d : Doc) (G : List Val) (verified rank : List Nat) : Prop where
  env : d.env = some G
  defs : ∀ i, i < d.values.length → d.welldef G i
  ranked : d.ranked verified rank = true
  step : ∀ k ∈ verified, (∀ j ∈ d.premisesOf k, d.holds G j) → d.holds G k

theorem Certificate.sound {d : Doc} {G : List Val} {verified rank : List Nat}
    (c : Certificate d G verified rank) : ∀ k ∈ verified, d.holds G k := by
  have key : ∀ n, ∀ k ∈ verified, rank.getD k 0 < n → d.holds G k := by
    intro n
    induction n with
    | zero => intro k _ h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro k hk hlt
      apply c.step k hk
      intro j hj
      have hr := c.ranked
      simp only [Doc.ranked, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.contains_iff_mem] at hr
      obtain ⟨hjv, hjr⟩ := hr k hk j hj
      exact ih j hjv (by omega)
  intro k hk
  exact key _ k hk (Nat.lt_succ_self _)

/-- `P k` for every `k` of a list, as nested conjunctions (for generated proofs). -/
def allList (P : Nat → Prop) : List Nat → Prop
  | [] => True
  | k :: ks => P k ∧ allList P ks

theorem allList_mem {P : Nat → Prop} : ∀ {ks : List Nat}, allList P ks → ∀ k ∈ ks, P k
  | [], _, _, hk => absurd hk List.not_mem_nil
  | _ :: _, ⟨h, hs⟩, k, hk => by
    rcases List.mem_cons.mp hk with rfl | hk
    · exact h
    · exact allList_mem hs k hk

/-- A certificate from one proof per definition and one step per verified claim. -/
theorem Certificate.ofLists {d : Doc} {G : List Val} {verified rank : List Nat} {n : Nat}
    (hn : d.values.length = n) (env : d.env = some G)
    (defs : allList (fun i => d.welldef G i) (List.range n))
    (ranked : d.ranked verified rank = true)
    (step : allList (fun k => (∀ j ∈ d.premisesOf k, d.holds G j) → d.holds G k) verified) :
    Certificate d G verified rank where
  env := env
  defs i hi := allList_mem defs i (List.mem_range.mpr (hn ▸ hi))
  ranked := ranked
  step k hk := allList_mem step k hk

end Proofread
