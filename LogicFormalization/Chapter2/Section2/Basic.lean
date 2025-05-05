import LogicFormalization.Chapter2.Section1.Prop'Lemmas
import LogicFormalization.Chapter2.Section1.Notation

namespace Prop'

open Notation

universe u
variable {A: Type u}

inductive Axiom : Prop' A → Prop
| trivial: Axiom ⊤
| inl (p q: Prop' A): Axiom P![p → p ∨ q]
| inr (p q: Prop' A): Axiom P![p → q ∨ p]
| notOr (p q: Prop' A): Axiom P![¬p → ¬q → ¬(p ∨ q)]
| left (p q: Prop' A): Axiom P![p ∧ q → p]
| right (p q: Prop' A): Axiom P![p ∧ q → q]
| and (p q: Prop' A): Axiom P![p → q → p ∧ q]
| split (p q r: Prop' A): Axiom P![(p → q → r) → (p → q) → p → r]
| absurd (p: Prop' A): Axiom P![p → ¬p → ⊥]
| contra (p: Prop' A): Axiom P![(¬p → ⊥) → p]

inductive Proof (S: Set (Prop' A)): Prop' A → Type u -- Type so that we can do induction on proofs
| assumption: {p: Prop' A} → p ∈ S → Proof S p
| axiom: {p: Prop' A} → Axiom p → Proof S p
| mp: (p: Prop' A) → {q: Prop' A} → Proof S p
    → Proof S (implies p q) → Proof S q

variable (S: Set (Prop' A)) (p: Prop' A)

@[simp]
abbrev proves :=
  Nonempty (Proof S p)

@[simp, reducible]
def inconsistent :=
  proves S ⊥

@[simp, reducible]
def consistent :=
  ¬(proves S ⊥)

@[simp, reducible]
def complete :=
  consistent S ∧ ∀ p, proves S p ∨ proves S (not p)


open Classical in
/-- The truth assignment t_Sigma as defined on page 23 -/
@[reducible]
noncomputable def proves?: A → Bool :=
  fun a => proves S (.atom a)
