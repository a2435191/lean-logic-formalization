import Mathlib.Tactic.Lemma
import Mathlib.Order.Notation
import LogicFormalization.Chapter2.Section1.Prop'

namespace Prop'.Notation

universe u v

declare_syntax_cat prop

/-! Infix notation for propositions because the syntax is identical to
the base logic that comes with Lean, and ambiguous syntax is hard/annoying.
-/

scoped syntax ident : prop -- bring an external Prop' name into the syntax
scoped syntax "{" term "}" : prop -- bring any external term into the syntax
scoped syntax:max "@" term:40 : prop -- bring an external variable into the syntax as an atom
scoped syntax "⊤" : prop
scoped syntax "⊥" : prop
scoped syntax:max "¬" prop:40 : prop
scoped syntax:30 prop:30 " ∨ " prop:31 : prop
scoped syntax:35 prop:35 " ∧ " prop:36 : prop
scoped syntax "(" prop ")" : prop
scoped syntax:max "P![" prop "]" : term

macro_rules
| `(P![@ {$a:term}]) => `(atom $a)
| `(P![@ $a:term]) => `(atom $a)
| `(P![$x:ident]) => `($x)
| `(P![{$x:term}]) => `($x)
| `(P![⊤]) => `(true)
| `(P![⊥]) => `(false)
| `(P![¬ $q:prop]) => `(not P![$q])
| `(P![$q:prop ∨ $r:prop]) => `(or P![$q] P![$r])
| `(P![$q:prop ∧ $r:prop]) => `(and P![$q] P![$r])
| `(P![($q:prop)]) => `(P![$q])


/-- Remark right before Lemma 2.1.1 -/
example {A: Type u} (a b c: A): Prop' A :=
  let p₁ := P![(¬@a ∨ @b) ∧ ¬@c]
  let p₂ := and (or (not (atom a)) (atom b)) (not (atom c))
  have: p₁ = p₂ := rfl
  -- and now a couple more examples
  let _ := P![p₁ ∧ {p₂}]
  let _: Prop' ℤ := P![@0 ∧ @-1 ∧ @{2+5} ∧ {true} ∨ {.and (.atom 1) P![@3]}]
  let _: Prop' (Set String) := P![@{{"abc" ++ "d"}} ∧ @{} ∧ ¬@{{}}]
  p₁

scoped syntax:20 prop:21 " → " prop:20 : prop -- right-associative
scoped syntax:20 prop:20 " ↔ " prop:21 : prop

macro_rules
| `(P![$q:prop → $r:prop]) => `(implies P![$q] P![$r])
| `(P![$q:prop ↔ $r:prop]) => `(iff P![$q] P![$r])


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

attribute [simp] Models.models
attribute [simp] NotModels.notModels
attribute [simp] ModelsLeft.models
attribute [simp] NotModelsLeft.notModels

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
