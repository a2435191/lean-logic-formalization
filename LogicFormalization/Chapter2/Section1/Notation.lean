import Mathlib.Tactic.Lemma
import Mathlib.Order.Notation
import LogicFormalization.Chapter2.Section1.Prop'

namespace Prop'.Notation

universe u v

declare_syntax_cat prop

/-! Infix notation for propositions because the syntax is identical to
the base logic that comes with Lean, and ambiguous syntax is hard/annoying.
-/
-- TODO: avoid having to do @ and ↑
scoped syntax:max "@" term:40 : prop -- bring an external variable into the syntax as an atom
scoped syntax "⊤" : prop
scoped syntax "⊥" : prop
scoped syntax:max "¬" prop:40 : prop
scoped syntax:30 prop:30 " ∨ " prop:31 : prop
scoped syntax:35 prop:35 " ∧ " prop:36 : prop
scoped syntax "(" prop ")" : prop
scoped syntax:max "↑" term:40 : prop -- bring an external Prop' into the syntax
scoped syntax:max "p![" prop "]" : term

macro_rules
| `(p![@ $a:term]) => `(atom $a)
| `(p![⊤]) => `(true)
| `(p![⊥]) => `(false)
| `(p![¬ $q:prop]) => `(not p![$q])
| `(p![$q:prop ∨ $r:prop]) => `(or p![$q] p![$r])
| `(p![$q:prop ∧ $r:prop]) => `(and p![$q] p![$r])
| `(p![↑$x:term]) => `($x)
| `(p![($q:prop)]) => `(p![$q])

/-- Remark right before Lemma 2.1.1 -/
example {A: Type u} (a b c: A): Prop' A :=
  let p₁ := p![(¬@a ∨ @b) ∧ ¬@c]
  let p₂ := and (or (not (atom a)) (atom b)) (not (atom c))
  have: p₁ = p₂ := rfl
  p₁

scoped syntax:20 prop:21 " → " prop:20 : prop -- right-associative
scoped syntax:20 prop:20 " ↔ " prop:21 : prop

macro_rules
| `(p![$q:prop → $r:prop]) => `(implies p![$q] p![$r])
| `(p![$q:prop ↔ $r:prop]) => `(iff p![$q] p![$r])

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

-- make ⊤ and ⊥ accessible without p![·]
instance instTop: Top (Prop' A) := ⟨true⟩
instance instBot: Bot (Prop' A) := ⟨false⟩

end Notation

end Prop'
