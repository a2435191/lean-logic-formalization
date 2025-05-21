import Mathlib.Tactic.Lemma
import Mathlib.Order.Notation
import LogicFormalization.Chapter2.Section1.Prop'

namespace Prop'.Notation

universe u v

declare_syntax_cat prop'

/-! Infix notation for prop'ositions because the syntax is identical to
the base logic that comes with Lean, and ambiguous syntax is hard/annoying.
-/

/-- Bring an external Prop' name into the syntax as a proposition -/
syntax ident : prop'
/-- Bring an external variable into the syntax as an atom. -/
syntax:max "@" term:max : prop'
/-- Bring any external term into the syntax as a proposition -/
syntax:max "{" term "}" : prop'
syntax "⊤" : prop'
syntax "⊥" : prop'
syntax:max "¬" prop':40 : prop'
syntax:30 prop':31 " ∨ " prop':30 : prop' -- right-associative
syntax:35 prop':36 " ∧ " prop':35 : prop' -- right-associative
syntax "(" prop' ")" : prop'
syntax:max "P![" prop' "]" : term

macro_rules
| `(P![$x:ident]) => `($x)
| `(P![@$a:term]) => `(atom $a)
| `(P![{$p:term}]) => `($p)
| `(P![⊤]) => `(true)
| `(P![⊥]) => `(false)
| `(P![¬$q:prop']) => `(not P![$q])
| `(P![$q:prop' ∨ $r:prop']) => `(or P![$q] P![$r])
| `(P![$q:prop' ∧ $r:prop']) => `(and P![$q] P![$r])
| `(P![($q)]) => `(P![$q])

syntax:20 prop':21 " → " prop':20 : prop' -- right-associative
syntax:20 prop':21 " ↔ " prop':20 : prop' -- right-associative (unlike in `Prop`)

macro_rules
| `(P![$q:prop' → $r:prop']) => `(implies P![$q] P![$r])
| `(P![$q:prop' ↔ $r:prop']) => `(iff P![$q] P![$r])

section
open Lean (TSyntax)
open Lean.PrettyPrinter (Unexpander UnexpandM)

inductive Parenthesize
| or | and | implies | iff
deriving BEq, Hashable

/-- This `Unexpander`-like function turns `P![$a ∧ $b]` into `($a ∧ $b)`
(a `TSyntax prop'`), and similarly for `P![$a ∨ $b]`.
The `targets` argument controls exactly which binary operations will be parenthesized. -/
def parenthesize (targets: Std.HashSet (Parenthesize))
    : Lean.TSyntax [`term, `ident] → UnexpandM (TSyntax `prop')
| `(term| P![$p]) => do
  let target?: Option Parenthesize := match p with
  | `(prop'| $_ ∨ $_) => some .or
  | `(prop'| $_ ∧ $_) => some .and
  | `(prop'| $_ → $_) => some .implies
  | `(prop'| $_ ↔ $_) => some .iff
  | _ => none
  match target? with
  | some target =>
    if target ∈ targets then `(prop'| ($p)) else pure p
  | none => pure p
-- We don't delaborate singleton `atom`s or booleans
-- since it looks better
| `(atom $a) => `(prop'| @$a) -- TODO: are these ok?
| `(true) => `(prop'| ⊤)
| `(false) => `(prop'| ⊥)
| `($p) =>
    if p.raw.isIdent then -- this might be jank too idk
      pure ⟨p⟩
    else
      `(prop'| {$p})

@[app_unexpander Prop'.not] def unexpNot : Unexpander
| `($_ $p) => do
  let p' ← parenthesize {.or, .and, .implies, .iff} p
  `(P![¬$p'])
| _ => throw ()

@[app_unexpander Prop'.and] def unexpAnd : Unexpander
| `($_ $p $q) => do
  let p' ← parenthesize {.or, .and, .implies, .iff} p  -- arity ≤ current
  let q' ← parenthesize {.or,       .implies, .iff} q -- right-associative
  `(P![$p' ∧ $q'])
| _ => throw ()

@[app_unexpander Prop'.or] def unexpOr : Unexpander
| `($_ $p $q) => do
  let p' ← parenthesize {.or, .implies, .iff} p
  let q' ← parenthesize {     .implies, .iff} q
  `(P![$p' ∨ $q'])
| _ => throw ()

@[app_unexpander Prop'.implies] def unexpImplies : Unexpander
| `($_ $p $q) => do
  let p' ← parenthesize {.implies, .iff} p -- < 21
  /- exception to the usual < 20 rule, since it's unclear
  that e.g. `P![p → q ↔ r] ≝ P![p → (q ↔ r)]` unless you know the
  order of operations already.
  -/
  let q' ← parenthesize {.iff} q
  `(P![$p' → $q'])
| _ => throw ()

@[app_unexpander Prop'.iff] def unexpIff : Unexpander
| `($_ $p $q) => do
  let p' ← parenthesize {} p
  let q' ← parenthesize {.implies, .iff} q
  `(P![$p' ↔ $q'])
| _ => throw ()

-- TODO: remove unnecessary parentheses around delaborated `P![...]`. For example,
/-- info: id (P![@0 ∧ @1]) : Prop' ℕ -/
#guard_msgs in #check id P![@0 ∧ @1]

-- TODO: get hover working inside `P![·]` syntax
end

section Tests
/-- info: atom 0 : Prop' ℕ -/ -- Represent lonely atoms, `true`, `false`, as they are
#guard_msgs in #check P![@0]
/-- info: true : Prop' ℕ -/
#guard_msgs in #check (P![⊤]: Prop' ℕ)
/-- info: false : Prop' ℕ -/
#guard_msgs in #check (P![⊥]: Prop' ℕ)

/-- info: P![¬(@0 ∧ @1) ∨ @2] : Prop' ℕ -/
#guard_msgs in #check P![¬(@0 ∧ @1) ∨ @2]
/-- info: P![@2 ∨ @0 ∧ @1] : Prop' ℕ -/
#guard_msgs in #check P![@2 ∨ (@0 ∧ @1)]
/-- info: P![@0 ∧ (@0 ∨ @1)] : Prop' ℕ -/
#guard_msgs in #check P![@0 ∧ (@0 ∨ @1)]
/-- info: P![@0 ∧ @1 ∧ @2] : Prop' ℕ -/
#guard_msgs in #check P![@0 ∧ @1 ∧ @2]
/-- info: P![¬(@0 ∧ @1)] : Prop' ℕ -/
#guard_msgs in #check P![¬(@0 ∧ @1)]
inductive α
| a | b | c

open α

/-! Remark right before Lemma 2.1.1 -/

def p := P![(¬@a ∨ @b) ∧ ¬@c]
def q := and (or (not (atom a)) (atom b)) (not (atom c))

example : p = q :=
  rfl

/-- info: P![(¬@a ∨ @b) ∧ ¬@c] : Prop' α -/
#guard_msgs in #check and (or (not (atom a)) (atom b)) (not (atom c))
/-- info: P![p ∧ q] : Prop' α -/
#guard_msgs in #check P![(p ∧ q)]
/-- info: P![p ∧ ¬q] : Prop' α -/
#guard_msgs in #check P![p ∧ ¬q]

/-- info: P![p ↔ q] : Prop' α -/
#guard_msgs in #check Prop'.iff p q
/-- info: P![p ↔ q ∧ q] : Prop' α -/
#guard_msgs in #check P![p ↔ (q ∧ q)]

def r := P![¬p ∨ q]
example : r = P![p → q] ∧ r = implies p q :=
  ⟨rfl, rfl⟩

/-- info: P![p ↔ q ∧ q] : Prop' α -/
#guard_msgs in #check P![p ↔ (q ∧ q)]
/-- info: P![p → q → r] : Prop' α -/
#guard_msgs in #check P![p → (q → r)]
/-- info: P![(p → q) → r] : Prop' α -/
#guard_msgs in #check P![(p → q) → r]
/-- info: P![(p → q) → r → ⊥] : Prop' α -/
#guard_msgs in #check P![(p → q) → (r → ⊥)]
/-- info: P![p ↔ (q ↔ r)] : Prop' α -/
#guard_msgs in #check P![p ↔ q ↔ r]
/-- info: P![p ↔ (q → r)] : Prop' α -/
#guard_msgs in #check P![p ↔ q → r]
/-- info: P![(p ↔ q) → r] : Prop' α -/
#guard_msgs in #check P![(p ↔ q) → r]
/-- info: P![p → (q ↔ r)] : Prop' α -/
#guard_msgs in #check P![p → q ↔ r]
/-- info: P![p ∧ q ↔ r] : Prop' α -/
#guard_msgs in #check P![(p ∧ q) ↔ r]
/-- info: P![p ∧ q ↔ (q → r)] : Prop' α -/
#guard_msgs in #check P![(p ∧ q) ↔ q → r]
/-- info: P![{disj [p, q]} ∧ {disj [q, r]}] : Prop' α -/
#guard_msgs in #check P![{disj [p, q]} ∧ {disj [q, r]}]

/-- info: P![@(0 + 3) ∧ @(-1) ∧ @7 ∧ ⊤] : Prop' ℤ -/
#guard_msgs in #check P![@(0 + 3) ∧ @(-1) ∧ @7 ∧ true]
/-- info: P![@{"abc" ++ "d"} ∧ @∅ ∧ ¬@∅] : Prop' (Set String) -/
#guard_msgs in #check (P![@{"abc" ++ "d"} ∧ @{} ∧ ¬@∅]: Prop' (Set String))
/-- info: P![@() ∧ @() ↔ @()] : Prop' Unit -/
#guard_msgs in #check P![@((((((())))))) ∧ @() ↔ @(())]
/-- info: P![@(1 = 2) ∧ @True] : Prop' Prop -/
#guard_msgs in #check P![@(1 = 2) ∧ @True]

end Tests

variable (α: Sort u) (β: Sort v)

/-- Notation typeclass for the binary ` ⊨` and `|=` relations, e.g. `Σ ⊨ σ`.
  In that example, `Σ: α` and `σ: β`. Prefer `⊨`.
  See also `ModelsLeft`.  -/
class Models where
  models: α → β → Prop

/-- Notation typeclass for the binary `⊭` relation, e.g. `Σ ⊭ σ`.
  In that example, `Σ: α` and `σ: β`. See also `NotModelsLeft`. -/
class NotModels where
  notModels: α → β → Prop

/-- Notation typeclass for the unary `⊨` and `|=` predicate, e.g. `⊨ p`,
  where `p: α`. Prefer `⊨`. -/
class ModelsLeft (α: Sort u) where
  models: α → Prop

/-- Notation typeclass for the unary `⊭` predicate, e.g. `⊭ σ`, where `σ: α`. -/
class NotModelsLeft where
  notModels: α → Prop

attribute [simp] Models.models NotModels.notModels
  ModelsLeft.models NotModelsLeft.notModels

scoped infix:50 " |= " => Models.models
scoped infix:50 " ⊨ " => Models.models
scoped infix:50 " ⊭ " => NotModels.notModels
scoped prefix:50 "|= " => ModelsLeft.models
scoped prefix:50 "⊨ " => ModelsLeft.models
scoped prefix:50 "⊭ " => NotModelsLeft.notModels

variable (A: Type u)

instance: Models (Set (Prop' A)) (Prop' A) := ⟨tautologicalConsequence⟩
instance: NotModels (Set (Prop' A)) (Prop' A) := ⟨fun S p => ¬S ⊨ p⟩
instance: ModelsLeft (Prop' A) := ⟨tautology⟩
instance: NotModelsLeft (Prop' A) := ⟨fun p => ¬⊨ p⟩

-- make ⊤ and ⊥ accessible without P![·]
instance instTop: Top (Prop' A) := ⟨true⟩
instance instBot: Bot (Prop' A) := ⟨false⟩

end Notation

end Prop'
