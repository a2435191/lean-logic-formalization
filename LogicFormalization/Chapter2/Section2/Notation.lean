import LogicFormalization.Chapter2.Section2.Basic

namespace Prop'.Notation

universe u v
variable (α: Sort u) (β: Sort v)

/-- Notation typeclass for the binary `⊢` and `|-` relations, e.g. `Σ ⊢ σ`.
  In that example, `Σ: α` and `σ: β`. Prefer `⊢`.
  See also `ProvesLeft` and `NotProves`. -/
class Proves where
  proves: α → β → Prop

/-- Notation typeclass for the binary `⊬` relation, e.g. `Σ ⊬ σ`.
  In that example, `Σ: α` and `σ: β`. See also `NotProvesLeft`. -/
class NotProves where
  notProves: α → β → Prop

/-- Notation typeclass for the unary `⊢` and `|-` predicate, e.g. `|- p`,
  where `p: α`. Prefer `⊢`. -/
class ProvesLeft where
  proves: α → Prop

/-- Notation typeclass for the unary `⊬` predicate, e.g. `⊬ p`,
  where `p: α`. -/
class NotProvesLeft where
  notProves: α → Prop


attribute [simp, reducible]
  Proves.proves NotProves.notProves
  ProvesLeft.proves NotProvesLeft.notProves

scoped infix:50 " |- " => Proves.proves
scoped infix:50 " ⊢ " => Proves.proves
scoped infix:50 " ⊬ " => NotProves.notProves
scoped prefix:50 "|- " => ProvesLeft.proves
scoped prefix:50 "⊢ " => ProvesLeft.proves
scoped prefix:50 "⊬ " => NotProvesLeft.notProves

variable (A: Type u)
instance: Proves (Set (Prop' A)) (Prop' A) := ⟨proves⟩
instance: NotProves (Set (Prop' A)) (Prop' A) := ⟨fun S p => ¬S ⊢ p⟩
instance: ProvesLeft (Prop' A) := ⟨proves ∅⟩
instance: NotProvesLeft (Prop' A) := ⟨fun p => ¬⊢ p⟩
