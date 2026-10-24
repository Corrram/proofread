import Lean

/-! Source text as Unicode code points.

Lean's kernel reduces operations on `String` literals slowly, so compiled source
is represented by lists of natural numbers (code points), which the kernel
handles with arbitrary-precision literals. `w!"word"` writes such a list. -/
namespace Proofread

abbrev Codes := List Nat

/-- A code-point list literal with raw natural-number literals. -/
syntax:max "w!" str : term

open Lean Elab Term Meta in
elab_rules : term
  | `(w! $s:str) => do
    let cs := s.getString.toList.map (fun c => mkRawNatLit c.toNat)
    mkListLit (mkConst ``Nat) cs

def Codes.toString (c : Codes) : String := String.ofList (c.map Char.ofNat)
def Codes.ofString (s : String) : Codes := s.toList.map Char.toNat

end Proofread
