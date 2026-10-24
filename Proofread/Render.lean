import Proofread.Doc

/-! # Formal readings

Renders compiled terms as explicit mathematics: quantifiers, domains and
definedness guards are written out. This rendering is for reading only; it is
not part of any certificate. -/
namespace Proofread

def Ty.tex : Ty → String
  | .real => "\\mathbb{R}"
  | .unit => "[0,1]"
  | .prop => "\\mathrm{Prop}"
  | .fn a b => (match a with | .fn .. => "(" ++ a.tex ++ ")" | _ => a.tex) ++ "\\to " ++ b.tex
  | .base k => s!"\\mathsf\{T}_\{{k}}"

def varNames : List String := ["x", "y", "z", "s", "t", "a", "b", "p", "q", "w", "k", "m"]

def Prim.tex : Prim → String
  | .rpow => "\\operatorname{pow}" | .min => "\\min" | .max => "\\max"
  | .leb => "\\lambda" | .borel => "\\operatorname{Borel}"
  | .measurableSet1 | .measurableSet2 => "\\operatorname{Meas}"
  | .integrable => "\\operatorname{Int}" | .hasDerivWithin => "\\operatorname{HasDeriv}"

/-- Binding strength for parentheses: propositions (1–4), relations (5), sums (6),
products (7), signs (8), atoms (9). -/
def Tm.prec : Tm → Nat
  | .iff .. => 1 | .imp .. => 2 | .or .. => 3 | .and .. => 4
  | .all .. | .ex .. | .the .. => 0
  -- a predicate applied to an argument is read as its body
  | .app (.app (.lam _ _ (.lam _ _ b)) _) _ => b.prec
  | .app (.lam _ _ b) _ => b.prec
  | .eq .. | .lt .. | .le .. => 5
  | .add .. | .sub .. => 6
  | .mul .. | .div .. => 7
  | .neg .. => 8
  | _ => 9

/-- A numeral or a quotient of numerals (displayed without its coercion to `[0,1]`). -/
def Tm.isNumeral : Tm → Bool
  | .num _ => true
  | .div x y => x.isNumeral && y.isNumeral
  | _ => false

partial def Tm.tex (cs gs : List String) (ls : List String) : Tm → String
  | .glob i => gs.getD i s!"g_{i}"
  | .loc i => ls.getD i s!"v_{i}"
  | .prim p => p.tex
  | .const i => cs.getD i s!"c_{i}"
  | .app (.app (.prim .rpow) x) y => "{" ++ wrap 9 x ++ "}^{" ++ y.tex cs gs ls ++ "}"
  | .app (.app (.prim .min) x) y => "\\min\\{" ++ x.tex cs gs ls ++ "," ++ y.tex cs gs ls ++ "\\}"
  | .app (.app (.prim .max) x) y => "\\max\\{" ++ x.tex cs gs ls ++ "," ++ y.tex cs gs ls ++ "\\}"
  | .app (.app (.app (.app (.prim .hasDerivWithin) f) s) x) d =>
      "(" ++ f.tex cs gs ls ++ ")'(" ++ x.tex cs gs ls ++ ")=" ++ d.tex cs gs ls ++ "\\text{ within }" ++ s.tex cs gs ls
  | .app (.prim .leb) s => "\\lambda\\bigl(" ++ s.tex cs gs ls ++ "\\bigr)"
  -- a domain predicate applied to an argument: read it about the argument
  | .app (.app (.lam _ _ (.lam _ _ b)) x) y => b.tex cs gs (y.tex cs gs ls :: x.tex cs gs ls :: ls)
  | .app (.lam _ _ b) x => b.tex cs gs (x.tex cs gs ls :: ls)
  | .app (.glob i) x =>
    let n := gs.getD i s!"g_{i}"
    if n.startsWith "^" then "{" ++ wrap 9 x ++ "}" ++ n
    else if n == "\\widehat" then "\\widehat{" ++ x.tex cs gs ls ++ "}"
    else n ++ "(" ++ x.tex cs gs ls ++ ")"
  | .app f x => (match f with
      | .lam .. => "(" ++ f.tex cs gs ls ++ ")"
      | _ => f.tex cs gs ls) ++ "(" ++ x.tex cs gs ls ++ ")"
  | .lam t d b =>
    let v := varNames.getD ls.length "v"
    let dom := match d with | .tt => "" | d => "\\,[" ++ d.tex cs gs (v :: ls) ++ "]"
    "(" ++ v ++ "\\in " ++ t.tex ++ dom ++ "\\mapsto " ++ b.tex cs gs (v :: ls) ++ ")"
  | .num n => toString n
  | .ofUnit x => x.tex cs gs ls
  | .toUnit x => if x.isNumeral then x.tex cs gs ls else "\\langle " ++ x.tex cs gs ls ++ "\\rangle_{[0,1]}"
  | .add x y => wrap 6 x ++ "+" ++ wrap 7 y
  | .sub x y => wrap 6 x ++ "-" ++ wrap 7 y
  | .mul x y => wrap 7 x ++ "\\," ++ wrap 8 y
  | .div x y => "\\frac{" ++ x.tex cs gs ls ++ "}{" ++ y.tex cs gs ls ++ "}"
  | .neg x => "-" ++ wrap 8 x
  | .abs x => "\\lvert " ++ x.tex cs gs ls ++ "\\rvert"
  | .powNat x n => "{" ++ wrap 9 x ++ "}^{" ++ toString n ++ "}"
  | .cases c v r => "\\begin{cases}" ++ v.tex cs gs ls ++ "&" ++ c.tex cs gs ls ++ "\\\\" ++
      (cases r) ++ "\\end{cases}"
  | .undef _ => "\\bot"
  | .eq x y => wrap 1 x ++ "=" ++ wrap 1 y
  | .lt x y => wrap 1 x ++ "<" ++ wrap 1 y
  | .le x y => wrap 1 x ++ "\\le " ++ wrap 1 y
  | .tt => "\\top"
  | .not p => "\\neg " ++ wrap 9 p
  | .and p q => wrap 5 p ++ "\\land " ++ wrap 4 q
  | .or p q => wrap 4 p ++ "\\lor " ++ wrap 3 q
  | .imp p q => wrap 3 p ++ "\\Rightarrow " ++ wrap 2 q
  | .iff p q => wrap 2 p ++ "\\Leftrightarrow " ++ wrap 2 q
  | .all t b => let v := varNames.getD ls.length "v"
    "\\forall " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex cs gs (v :: ls)
  | .ex t b => let v := varNames.getD ls.length "v"
    "\\exists " ++ v ++ "\\in " ++ t.tex ++ ",\\ " ++ b.tex cs gs (v :: ls)
  | .integral b => let v := varNames.getD ls.length "v"
    let s := b.tex cs gs (v :: ls)
    "\\int_0^1 " ++ (if b.prec < 7 then "(" ++ s ++ ")" else s) ++ "\\,d" ++ v
  | .guard _ e => e.tex cs gs ls
  | .the t b => let v := varNames.getD ls.length "v"
    "\\iota " ++ v ++ "\\in " ++ t.tex ++ ".\\ " ++ b.tex cs gs (v :: ls)
where
  /-- `t`, parenthesized when it binds more loosely than `p`. -/
  wrap (p : Nat) (t : Tm) : String :=
    let s := t.tex cs gs ls
    if t.prec < p then "(" ++ s ++ ")" else s
  cases : Tm → String
    | .cases c v r => v.tex cs gs ls ++ "&" ++ c.tex cs gs ls ++ "\\\\" ++ cases r
    | _ => ""

def Doc.globNames (d : Doc) : List String :=
  (d.globs.zip (List.range d.globs.length)).map fun (g, i) =>
    if g.key.isEmpty then
      match d.names.find? (·.2 == i) with
      | some (ws, _) => "\\operatorname{" ++ String.intercalate "\\," (ws.map Codes.toString) ++ "}"
      | none => s!"\\mathrm\{op}_\{{i}}"
    else Codes.toString g.key

/-- A Lean-identifier name for a definition: from the phrase that introduced it
(`the transpose of $C$` gives `transpose`, the class of `bivariate copulas`
gives `copulas`), or else from its symbol (`\nu` gives `nu`). -/
def defNameRaw (d : Doc) (i : Nat) : String :=
  let g := (d.globs[i]?).getD default
  let key := Codes.toString g.key
  let clean (s : String) : String := String.ofList ((s.replace "*" "Star").toList.filter Char.isAlphanum)
  let phrase := (d.names.find? (·.2 == i)).map (·.1.map (fun w => clean (Codes.toString w)))
  let camel (ps : List String) : String := match ps with
    | [] => s!"def{i}"
    | p :: ps => String.join (p :: ps.map String.capitalize)
  if key.isEmpty then (phrase.map camel).getD s!"def{i}"
  else if key.startsWith "^" || key == "\\widehat" || key == "\\hat" || key == "\\overline" then
    match phrase with
    | some (w :: _) => w
    | _ => clean key
  -- a decorated symbol: `\overline{\rho}` is `rhoBar`
  else if key.startsWith "\\overline{" || key.startsWith "\\bar{" then
    clean ((key.dropWhile (· != '{')).toString) ++ "Bar"
  else if key.startsWith "\\tilde{" then clean ((key.dropWhile (· != '{')).toString) ++ "Tilde"
  else if key.contains '{' then
    match phrase with
    | some ws@(_ :: _) => ws.getLast!
    | _ => clean key
  -- `\gamma^T` next to `\gamma_T`
  else if key.endsWith "^" then clean key ++ "Upper"
  else clean key

/-- The Lean name of definition `i`: its symbol, or its phrase, made unique by the
definition's index when an earlier definition has the same name. -/
def defName (d : Doc) (i : Nat) : String :=
  let n := defNameRaw d i
  if (List.range i).any (fun j => defNameRaw d j == n) then s!"{n}{i}" else n

end Proofread
