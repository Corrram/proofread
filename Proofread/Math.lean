import Proofread.Lex

/-! # Parsing mathematical formulas

A total precedence parser from math-mode tokens to formula trees. It follows TeX
argument conventions (`\frac14`, `c^3`, `D_{1/2}`), standard precedence, and
reads juxtaposition as multiplication or application. Whether `f(x)` is an
application or a product is decided later by types. -/
namespace Proofread

inductive Rel where
  | eq | lt | le | gt | ge | mem | defeq | ne
  deriving DecidableEq, Repr, Lean.ToExpr

inductive MT where
  | id (n : Codes)
  | num (n : Nat)
  | sub (b i : MT)
  | sup (b e : MT)
  | hat (x : MT)
  | app (f : MT) (args : List MT)
  | add (x y : MT) | minus (x y : MT) | mul (x y : MT) | div (x y : MT)
  | neg (x : MT) | abs (x : MT) | frac (x y : MT)
  | minm (args : List MT) | maxm (args : List MT)
  | int (lo hi body : MT) (v : Codes)
  | tuple (xs : List MT)
  | interval (a b : MT)
  /-- An interval with open ends: `(a,b]` is `ival a b true false`. -/
  | ival (a b : MT) (lopen ropen : Bool)
  | setOf (pat dom : MT) (conds : List MT)
  /-- `{pat : conds}`: the variables of `pat` that are not yet bound range over
  the real numbers subject to `conds`. -/
  | setCond (pat : MT) (conds : List MT)
  | image (elem : MT) (v : Codes) (dom : MT)
  | mapsto (pat body : MT)
  | chain (x : MT) (rest : List (Rel × MT))
  | cases (rows : List (MT × MT))
  | sig (name dom cod : MT)
  | conj (xs : List MT)
  /-- `φ, equivalently ψ` in a display: `φ`, and `φ ↔ ψ`. -/
  | equiv (x y : MT)
  /-- `\text{word}` between the formulas of a display (e.g. `where`). -/
  | text (w : Codes)
  deriving Repr, Inhabited, Lean.ToExpr

/-- Math tokens after removing typesetting. -/
inductive MTok where
  | id (n : Codes)
  | digit (d : Nat)
  | sym (c : Nat)
  | cmd (n : Codes)
  | lb | rb
  | setl | setr
  | row
  | diff
  /-- `\text{words}` (letters only). -/
  | text (w : Codes)
  | begin (e : Codes) | finish (e : Codes)
  deriving DecidableEq, Repr, Lean.ToExpr, Inhabited

namespace Math

def wFonts : List Codes := [w!"mathcal", w!"mathbb", w!"mathbf", w!"mathrm", w!"operatorname", w!"mathit"]

/-- Join font commands with their letters; `\mathrm{d}` is a differential. -/
def simplify : Nat → List PTok → Option (List MTok)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, t :: ts =>
    match t.tok with
    | .mvar c => (MTok.id [c] :: ·) <$> simplify f ts
    | .mnum d => (MTok.digit d :: ·) <$> simplify f ts
    | .msym c => (MTok.sym c :: ·) <$> simplify f ts
    | .lbrace => (MTok.lb :: ·) <$> simplify f ts
    | .rbrace => (MTok.rb :: ·) <$> simplify f ts
    | .csym 123 => (MTok.setl :: ·) <$> simplify f ts
    | .csym 125 => (MTok.setr :: ·) <$> simplify f ts
    | .csym 124 => (MTok.sym 124 :: ·) <$> simplify f ts
    | .csym 92 => (MTok.row :: ·) <$> simplify f ts
    | .begin e => (MTok.begin e :: ·) <$> simplify f ts
    | .finish e => (MTok.finish e :: ·) <$> simplify f ts
    | .ref _ _ => simplify f ts
    | .cmd n =>
      if n == w!"text" then
        match ts with
        | ⟨.lbrace, _, _⟩ :: rest =>
          let inner := rest.takeWhile (fun p => p.tok != .rbrace)
          let word := inner.filterMap (fun p => match p.tok with | .mvar c => some c | _ => none)
          if word.length != inner.length then none
          else (MTok.text word :: ·) <$> simplify f (rest.drop (inner.length + 1))
        | _ => none
      else if wFonts.contains n then
        match ts with
        | ⟨.lbrace, _, _⟩ :: rest =>
          let letters := rest.takeWhile (fun p => match p.tok with | .mvar _ => true | _ => false)
          let word := letters.filterMap (fun p => match p.tok with | .mvar c => some c | _ => none)
          match rest.drop letters.length with
          | ⟨.rbrace, _, _⟩ :: rest' =>
            if n == w!"mathrm" && word == w!"d" then (MTok.diff :: ·) <$> simplify f rest'
            else if n == w!"mathrm" || n == w!"operatorname" then (MTok.id word :: ·) <$> simplify f rest'
            else (MTok.id ([92] ++ n ++ [123] ++ word ++ [125]) :: ·) <$> simplify f rest'
          | _ => none
        | _ => none
      else if n == w!"tfrac" || n == w!"dfrac" then (MTok.cmd w!"frac" :: ·) <$> simplify f ts
      else (MTok.cmd n :: ·) <$> simplify f ts
    | _ => none

def isDigitTok : MTok → Bool | .digit _ => true | _ => false

def relOf : MTok → Option Rel
  | .sym 61 => some .eq
  | .sym 60 => some .lt
  | .sym 62 => some .gt
  | .cmd n =>
    if n == w!"le" || n == w!"leq" then some .le
    else if n == w!"ge" || n == w!"geq" then some .ge
    else if n == w!"in" then some .mem
    else if n == w!"coloneqq" then some .defeq
    else if n == w!"neq" || n == w!"ne" then some .ne
    else none
  | _ => none

/-- Tokens that may begin an implicit product factor. -/
def startsFactor : MTok → Bool
  | .id _ | .digit _ | .lb | .setl => true
  | .sym 40 => true
  | .cmd n => n == w!"frac" || n == w!"int" || n == w!"min" || n == w!"max" || n == w!"widehat"
      || n == w!"hat" || (!(relOf (.cmd n)).isSome && n != w!"mapsto" && n != w!"to" &&
        n != w!"cdot" && n != w!"qquad" && n != w!"quad" && n != w!"times" && n != w!"top" && n != w!"perp")
  | _ => false

/-- Heads that may be applied to a parenthesized argument list. -/
def appHead : MT → Bool
  | .id _ | .sub _ _ | .hat _ | .app _ _ => true
  | .sup _ (.id n) => n == w!"\\top" || n == w!"\\perp"
  -- the inverse function `f^{-1}`
  | .sup (.id _) (.neg (.num 1)) => true
  | _ => false

inductive Mode where
  | top              -- relations, chains, mapsto
  | additive (bar : Bool)
  | product (bar : Bool)
  | factor (bar : Bool)
  | postfix (bar : Bool) (x : MT)
  | atom (bar : Bool)
  | number (acc : Nat)
  | args (acc : List MT)
  | group              -- a braced group or single token (TeX argument)
  | casesRows (acc : List (MT × MT))
  | list (sep : Nat) (acc : List MT)   -- comma separated items until a closer
  deriving Inhabited

abbrev R := Option (MT × List MTok)

def expect (t : MTok) : List MTok → Option (List MTok)
  | u :: us => if u == t then some us else none
  | [] => none

/-- One structurally recursive parser with explicit modes (kernel-reducible). -/
def run : Nat → Mode → List MTok → R
  | 0, _, _ => none
  | f + 1, .top, ts => do
    let (x, rest) ← run f (.additive false) ts
    match rest with
    | .cmd n :: rest' =>
      if n == w!"mapsto" then
        let (b, rest'') ← run f .top rest'
        some (.mapsto x b, rest'')
      else if n == w!"to" then none
      else chainRest f x [] rest
    | _ => chainRest f x [] rest
  | f + 1, .additive bar, ts => do
    let (x, rest) ← run f (.product bar) ts
    addRest f bar x rest
  | f + 1, .product bar, ts => do
    let (x, rest) ← run f (.factor bar) ts
    mulRest f bar x rest
  | f + 1, .factor bar, ts =>
    match ts with
    | .sym 45 :: rest => do
      let (x, rest') ← run f (.product bar) rest
      some (.neg x, rest')
    | _ => do
      let (x, rest) ← run f (.atom bar) ts
      run f (.postfix bar x) rest
  | f + 1, .postfix bar x, ts =>
    match ts with
    | .sym 94 :: rest => do
      let (e, rest') ← run f .group rest
      run f (.postfix bar (.sup x e)) rest'
    | .sym 95 :: rest => do
      let (i, rest') ← run f .group rest
      run f (.postfix bar (.sub x i)) rest'
    | .sym 40 :: rest =>
      if !appHead x then some (x, ts) else do
        let (m, rest') ← run f (.list 41 []) rest
        match m with
        | .conj as => run f (.postfix bar (.app x as)) rest'
        | _ => none
    | _ => some (x, ts)
  | f + 1, .atom bar, ts =>
    match ts with
    | .digit d :: rest => run f (.number d) rest
    | .id n :: rest => some (.id n, rest)
    | .sym 40 :: rest =>
      (do
        let (m, rest') ← run f (.list 41 []) rest
        match m with
        | .conj [x] => some (x, rest')
        | .conj xs => some (.tuple xs, rest')
        | _ => none) <|>
      (do
        -- `(a,b]`
        let (a, r1) ← run f (.additive false) rest
        let r2 ← expect (.sym 44) r1
        let (b, r3) ← run f (.additive false) r2
        let r4 ← expect (.sym 93) r3
        some (.ival a b true false, r4))
    | .sym 91 :: rest => do
      let (a, r1) ← run f (.additive false) rest
      let r2 ← expect (.sym 44) r1
      let (b, r3) ← run f (.additive false) r2
      match r3 with
      | .sym 93 :: r4 => some (.interval a b, r4)
      | .sym 41 :: r4 => some (.ival a b false true, r4)
      | _ => none
    | .sym 124 :: rest =>
      if bar then none else do
        let (x, r1) ← run f (.additive true) rest
        let r2 ← expect (.sym 124) r1
        some (.abs x, r2)
    | .lb :: rest => do
      let (x, r1) ← run f .top rest
      let r2 ← expect .rb r1
      some (x, r2)
    | .setl :: rest => setBuilder f rest
    | .cmd n :: rest =>
      if n == w!"frac" then do
        let (a, r1) ← run f .group rest
        let (b, r2) ← run f .group r1
        some (.frac a b, r2)
      else if n == w!"widehat" || n == w!"hat" then do
        let (a, r1) ← run f .group rest
        some (.hat a, r1)
      else if n == w!"min" || n == w!"max" then
        match rest with
        | .setl :: r => do
          let (m, r') ← run f (.list 125 []) r
          match m with
          | .conj xs => some (if n == w!"min" then .minm xs else .maxm xs, r')
          | _ => none
        | _ => none
      else if n == w!"int" then
        match rest with
        | .sym 95 :: r => do
          let (lo, r1) ← run f .group r
          let r2 ← expect (.sym 94) r1
          let (hi, r3) ← run f .group r2
          integralBody f lo hi r3
        | _ => none
      else if (relOf (.cmd n)).isSome || n == w!"mapsto" || n == w!"to" || n == w!"qquad" || n == w!"quad" then none
      else some (.id ([92] ++ n), rest)
    | .begin e :: rest =>
      if e == w!"cases" then run f (.casesRows []) rest else none
    | _ => none
  | f + 1, .number acc, ts =>
    match ts with
    | .digit d :: rest => run f (.number (10 * acc + d)) rest
    | _ => some (.num acc, ts)
  | f + 1, .group, ts =>
    match ts with
    | .lb :: rest => do
      let (x, r1) ← run f .top rest
      let r2 ← expect .rb r1
      some (x, r2)
    | .digit d :: rest => some (.num d, rest)
    | .id n :: rest => some (.id n, rest)
    | .cmd n :: rest => some (.id ([92] ++ n), rest)
    | _ => none
  | _ + 1, .args acc, ts => some (.tuple acc.reverse, ts)
  | f + 1, .list close acc, ts => do
    let (x, r1) ← run f .top ts
    match r1 with
    | .sym 44 :: r2 => run f (.list close (x :: acc)) r2
    | t :: r2 =>
      if (close == 41 && t == .sym 41) || (close == 125 && t == .setr) then
        some (MT.conj (x :: acc).reverse, r2)
      else none
    | [] => none
  | f + 1, .casesRows acc, ts =>
    match ts with
    | .finish e :: rest => if e == w!"cases" then some (.cases acc.reverse, rest) else none
    | _ => do
      let (v, r1) ← run f (.additive false) ts
      let r1 := match r1 with | .sym 44 :: r => r | r => r
      let r2 ← expect (.sym 38) r1
      let (c, r3) ← run f .top r2
      let r4 := match r3 with | .sym 44 :: r => r | .sym 46 :: r => r | r => r
      match r4 with
      | .row :: r5 => run f (.casesRows ((v, c) :: acc)) r5
      | _ => run f (.casesRows ((v, c) :: acc)) r4
where
  chainRest : Nat → MT → List (Rel × MT) → List MTok → R
    | 0, _, _, _ => none
    | g + 1, x, acc, ts =>
      match ts with
      | t :: rest =>
        match relOf t with
        | some r => do
          let (y, rest') ← run g (.additive false) rest
          chainRest g x ((r, y) :: acc) rest'
        | none => some (if acc.isEmpty then x else .chain x acc.reverse, ts)
      | [] => some (if acc.isEmpty then x else .chain x acc.reverse, ts)
  addRest : Nat → Bool → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, bar, x, ts =>
      match ts with
      | .sym 43 :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.add x y) rest'
      | .sym 45 :: rest => do
        let (y, rest') ← run g (.product bar) rest
        addRest g bar (.minus x y) rest'
      | _ => some (x, ts)
  mulRest : Nat → Bool → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, bar, x, ts =>
      match ts with
      | .sym 42 :: rest | .cmd [99, 100, 111, 116] :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.mul x y) rest'
      | .sym 47 :: rest => do
        let (y, rest') ← run g (.factor bar) rest
        mulRest g bar (.div x y) rest'
      | t :: _ =>
        if startsFactor t || (t == .sym 124 && !bar) then
          match run g (.atom bar) ts with
          | some (y0, rest') => do
            let (y, rest'') ← run g (.postfix bar y0) rest'
            mulRest g bar (.mul x y) rest''
          | none => some (x, ts)
        else some (x, ts)
      | [] => some (x, ts)
  integralBody : Nat → MT → MT → List MTok → R
    | 0, _, _, _ => none
    | g + 1, lo, hi, ts => do
      let (body, r1) ← run g (.product false) ts
      match r1 with
      | .diff :: .id v :: r2 => some (.int lo hi body v, r2)
      | _ => none
  setBuilder : Nat → List MTok → R
    | 0, _ => none
    | g + 1, ts => do
      -- `{pat ∈ dom : conds}` or `{elem : v ∈ dom}`
      let (head, r1) ← run g (.additive false) ts
      match r1 with
      | .cmd n :: r2 =>
        if n == w!"in" then do
          let (dom, r3) ← run g (.additive false) r2
          let r4 ← expect (.sym 58) r3
          let (conds, r5) ← run g (.list 125 []) r4
          match conds with
          | .conj cs => some (.setOf head dom cs, r5)
          | _ => none
        else none
      | .sym 58 :: r2 =>
        (do
          let (v, r3) ← (match r2 with | .id v :: r => some (v, r) | _ => none : Option (Codes × List MTok))
          let r4 ← expect (.cmd w!"in") r3
          let (dom, r5) ← run g (.additive false) r4
          let r6 ← expect .setr r5
          some (.image head v dom, r6)) <|>
        (do
          let (conds, r3) ← run g (.list 125 []) r2
          match conds with
          | .conj cs => some (.setCond head cs, r3)
          | _ => none)
      | _ => none

/-- Displays: aligned rows and formula lists separated by `,\qquad`.
A row beginning with a relation continues the previous row's chain. -/
def splitTop : Nat → List MTok → List MTok → Nat → List (List MTok) → List (List MTok)
  | 0, cur, _, _, acc => (cur.reverse :: acc).reverse
  | _ + 1, cur, [], _, acc => (cur.reverse :: acc).reverse
  | f + 1, cur, t :: ts, depth, acc =>
    let depth' := match t with
      | .lb | .setl | .sym 40 | .sym 91 | .begin _ => depth + 1
      | .rb | .setr | .sym 41 | .sym 93 | .finish _ => depth - 1
      | _ => depth
    if depth == 0 && (t == .row || t == .cmd w!"qquad") then
      let cur' := match cur with | .sym 44 :: c => c | c => c
      if cur'.isEmpty then splitTop f [] ts depth' acc
      else splitTop f [] ts depth' (cur'.reverse :: acc)
    else if depth == 0 && t == .sym 38 then
      -- `a, & b`: a column of equations; otherwise an alignment point
      match cur with
      | .sym 44 :: c => if c.isEmpty then splitTop f [] ts depth' acc else splitTop f [] ts depth' (c.reverse :: acc)
      | _ => splitTop f cur ts depth' acc
    else if depth == 0 && (match t with | .text _ => true | _ => false) then
      let cur' := match cur with | .sym 44 :: c => c | c => c
      let acc := if cur'.isEmpty then acc else cur'.reverse :: acc
      splitTop f [] ts depth' ([t] :: acc)
    else splitTop f (t :: cur) ts depth' acc

def stripEnv : List MTok → List MTok
  | .begin e :: ts =>
    if e == w!"aligned" || e == w!"gathered" || e == w!"split" then
      match ts.reverse with
      | .finish e' :: r => if e' == e then r.reverse else .begin e :: ts
      | _ => .begin e :: ts
    else .begin e :: ts
  | ts => ts

def parseFormula (ts : List MTok) : Option MT :=
  match run (8 * ts.length + 64) .top ts with
  | some (x, []) => some x
  | _ => none

def joinRows : List MT → Option (List MT)
  | [] => some []
  | x :: rest => do
    let rs ← joinRows rest
    match rs with
    | .chain (.id []) more :: rs' =>
      match x with
      | .chain y acc => some (.chain y (acc ++ more) :: rs')
      | y => some (.chain y more :: rs')
    | _ => some (x :: rs)

/-- Parse the content of a display or inline formula. -/
def parseDisplay (ts : List MTok) : Option MT := do
  let ts := stripEnv ts
  let parts := splitTop (ts.length + 1) [] ts 0 []
  let parts := parts.filter (!·.isEmpty)
  -- `φ, \text{equivalently} ψ`
  match parts with
  | [p, [.text w], q] =>
    if w == w!"equivalently" then do
      let a ← parseFormula p
      let b ← parseFormula q
      some (.equiv a b)
    else none
  | _ => do
  let ms ← parts.mapM fun p =>
    match p with
    | [.text w] => some (MT.text w)
    | t :: _ => if (relOf t).isSome then parseFormula (.id [] :: p) else parseFormula p
    | [] => none
  let ms ← joinRows ms
  match ms with
  | [m] => some m
  | ms => some (.conj ms)

/-- Function signature `f : A \to B`. -/
def parseSig (ts : List MTok) : Option MT := do
  let i ← ts.findIdx? (· == .sym 58)
  let j ← ts.findIdx? (· == .cmd w!"to")
  let name ← parseFormula (ts.take i)
  let dom ← parseFormula ((ts.drop (i + 1)).take (j - i - 1))
  let cod ← parseFormula (ts.drop (j + 1))
  some (.sig name dom cod)

end Math
end Proofread
