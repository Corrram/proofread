import Proofread.Syntax
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Function

/-! # The meaning of core terms

`denote M G L t` is the value of the term `t`, where `M` interprets the
vocabulary (its base types and constants), `G` are the values of the article's
definitions and `L` those of the bound variables. -/

namespace Proofread
open MeasureTheory
open scoped unitInterval

/-- The meaning of a type, given the meanings `B` of the vocabulary's base types. -/
@[reducible] def Ty.denote (B : Nat → Type) : Ty → Type
  | .real => ℝ
  | .unit => I
  | .prop => Prop
  | .fn a b => a.denote B → b.denote B
  | .base k => B k

/-- A value of every type (used for ill-typed or undefined terms). -/
def Ty.default {B : Nat → Type} (d : (k : Nat) → B k) : (t : Ty) → t.denote B
  | .real => (0 : ℝ)
  | .unit => (0 : I)
  | .prop => False
  | .fn _ b => fun _ => Ty.default d b
  | .base k => d k

/-- A typed value. -/
abbrev Val (B : Nat → Type) := Σ t : Ty, t.denote B

/-- The interpretation of a vocabulary: the Lean types of its base types and the
Lean values of its constants. A vocabulary without base types uses `B k = Unit`. -/
structure Model where
  base : Nat → Type
  default : (k : Nat) → base k
  consts : List (Val base)

/-- The model of an empty vocabulary. -/
def Model.empty : Model := ⟨fun _ => Unit, fun _ => (), []⟩

namespace Prelude
noncomputable def leb (A : I → Prop) : ℝ := (volume {x : I | A x}).toReal
def measurableSet1 (A : I → Prop) : Prop := MeasurableSet {x : I | A x}
def measurableSet2 (A : I → I → Prop) : Prop := MeasurableSet {p : I × I | A p.1 p.2}
def integrable (f : I → ℝ) : Prop := Integrable f
def hasDerivWithin (f : ℝ → ℝ) (S : ℝ → Prop) (x d : ℝ) : Prop :=
  HasDerivWithinAt f d {y | S y} x
noncomputable def intervalIntegral (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in a..b, f t
def intervalIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop := IntervalIntegrable f volume a b
def compact2 (S : ℝ → ℝ → Prop) : Prop := IsCompact {p : ℝ × ℝ | S p.1 p.2}
def convex2 (S : ℝ → ℝ → Prop) : Prop := Convex ℝ {p : ℝ × ℝ | S p.1 p.2}
def symm2 (S : ℝ → ℝ → Prop) : Prop := ∀ a b, S a b → S (-a) (-b)
def continuousOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ContinuousOn f {x | D x}
def concaveOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := ConcaveOn ℝ {x | D x} f
def strictMonoOn (f : ℝ → ℝ) (D : ℝ → Prop) : Prop := StrictMonoOn f {x | D x}
end Prelude

noncomputable def Prim.denote {B : Nat → Type} : (p : Prim) → p.ty.denote B
  | .rpow => fun x y => x ^ y
  | .min => fun x y => Min.min x y
  | .max => fun x y => Max.max x y
  | .leb => Prelude.leb
  | .borel => fun T => Measurable T
  | .measurableSet1 => Prelude.measurableSet1
  | .measurableSet2 => Prelude.measurableSet2
  | .integrable => Prelude.integrable
  | .hasDerivWithin => Prelude.hasDerivWithin
  | .intervalIntegral => Prelude.intervalIntegral
  | .intervalIntegrable => Prelude.intervalIntegrable
  | .compact2 => Prelude.compact2
  | .convex2 => Prelude.convex2
  | .symm2 => Prelude.symm2
  | .continuousOn => Prelude.continuousOn
  | .concaveOn => Prelude.concaveOn
  | .strictMonoOn => Prelude.strictMonoOn

/-- Numerals: `0`, `1` and `(n : ℝ)` for larger `n`. -/
def numVal : Nat → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n + 2 : ℕ) : ℝ)

section
variable {B : Nat → Type}

def Val.cast (d : (k : Nat) → B k) (b : Ty) : Option (Val B) → b.denote B
  | some ⟨a, v⟩ => if h : a = b then h ▸ v else Ty.default d b
  | none => Ty.default d b

def Val.prop : Option (Val B) → Prop
  | some ⟨.prop, P⟩ => P
  | _ => False

private def real2 (x y : Option (Val B)) (f : ℝ → ℝ → ℝ) : Option (Val B) :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.real, f a b⟩
  | _, _ => none

private def rel2 (x y : Option (Val B)) (f : ℝ → ℝ → Prop) : Option (Val B) :=
  match x, y with
  | some ⟨.real, a⟩, some ⟨.real, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none

private def prop2 (x y : Option (Val B)) (f : Prop → Prop → Prop) : Option (Val B) :=
  match x, y with
  | some ⟨.prop, a⟩, some ⟨.prop, b⟩ => some ⟨.prop, f a b⟩
  | _, _ => none
end

/-- The meaning of a core term, given the vocabulary model, the values of article
definitions and of locals. -/
noncomputable def denote (M : Model) (G : List (Val M.base)) : List (Val M.base) → Tm → Option (Val M.base)
  | _, .glob i => G[i]?
  | L, .loc i => L[i]?
  | _, .prim p => some ⟨p.ty, p.denote⟩
  | _, .const i => M.consts[i]?
  | L, .app f x =>
    match denote M G L f, denote M G L x with
    | some ⟨.fn a b, F⟩, some ⟨a', X⟩ => if h : a' = a then some ⟨b, F (h ▸ X)⟩ else none
    | _, _ => none
  | L, .lam t _ body =>
    match typeOf (M.consts.map (·.1)) (G.map (·.1)) (t :: L.map (·.1)) body with
    | some b => some ⟨.fn t b, fun x => Val.cast M.default b (denote M G (⟨t, x⟩ :: L) body)⟩
    | none => none
  | _, .num n => some ⟨.real, numVal n⟩
  | L, .ofUnit x =>
    match denote M G L x with
    | some ⟨.unit, u⟩ => some ⟨.real, (u : ℝ)⟩
    | _ => none
  | L, .toUnit x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.unit, Set.projIcc 0 1 zero_le_one r⟩
    | _ => none
  | L, .add x y => real2 (denote M G L x) (denote M G L y) (· + ·)
  | L, .sub x y => real2 (denote M G L x) (denote M G L y) (· - ·)
  | L, .mul x y => real2 (denote M G L x) (denote M G L y) (· * ·)
  | L, .div x y => real2 (denote M G L x) (denote M G L y) (· / ·)
  | L, .neg x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, -r⟩
    | _ => none
  | L, .abs x =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, |r|⟩
    | _ => none
  | L, .powNat x n =>
    match denote M G L x with
    | some ⟨.real, r⟩ => some ⟨.real, r ^ n⟩
    | _ => none
  | L, .cases c v rest =>
    match denote M G L c, denote M G L v, denote M G L rest with
    | some ⟨.prop, P⟩, some ⟨a, x⟩, some ⟨b, y⟩ =>
      if h : b = a then some ⟨a, @ite _ P (Classical.propDecidable P) x (h ▸ y)⟩ else none
    | _, _, _ => none
  | _, .undef t => some ⟨t, Ty.default M.default t⟩
  | L, .eq x y =>
    match denote M G L x, denote M G L y with
    | some ⟨a, u⟩, some ⟨b, v⟩ => if h : b = a then some ⟨.prop, u = h ▸ v⟩ else none
    | _, _ => none
  | L, .lt x y => rel2 (denote M G L x) (denote M G L y) (· < ·)
  | L, .le x y => rel2 (denote M G L x) (denote M G L y) (· ≤ ·)
  | _, .tt => some ⟨.prop, True⟩
  | L, .not p =>
    match denote M G L p with
    | some ⟨.prop, P⟩ => some ⟨.prop, ¬P⟩
    | _ => none
  | L, .and p q => prop2 (denote M G L p) (denote M G L q) (· ∧ ·)
  | L, .or p q => prop2 (denote M G L p) (denote M G L q) (· ∨ ·)
  | L, .imp p q => prop2 (denote M G L p) (denote M G L q) (· → ·)
  | L, .iff p q => prop2 (denote M G L p) (denote M G L q) (· ↔ ·)
  | L, .all t body => some ⟨.prop, ∀ x : t.denote M.base, Val.prop (denote M G (⟨t, x⟩ :: L) body)⟩
  | L, .ex t body => some ⟨.prop, ∃ x : t.denote M.base, Val.prop (denote M G (⟨t, x⟩ :: L) body)⟩
  | L, .integral body =>
    some ⟨.real, ∫ x : I, Val.cast M.default .real (denote M G (⟨.unit, x⟩ :: L) body)⟩
  | L, .guard _ e => denote M G L e
  | L, .the t body =>
    some ⟨t, @Classical.epsilon (t.denote M.base) ⟨Ty.default M.default t⟩
      (fun x => Val.prop (denote M G (⟨t, x⟩ :: L) body))⟩

/-- The values of an article's definitions, evaluated in order. Definition `i`
is `Tm.glob i`; it may refer only to earlier definitions. -/
noncomputable def evalDefs (M : Model) : List (Val M.base) → List Tm → Option (List (Val M.base))
  | G, [] => some G
  | G, d :: ds =>
    match denote M G [] d with
    | some v => evalDefs M (G ++ [v]) ds
    | none => none

end Proofread
