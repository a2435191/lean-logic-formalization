import LogicFormalization.Chapter2.Section1.Notation

namespace Prop'.Tautologies

open Notation

universe u
variable {A: Type u} {p q r: Prop' A}


scoped macro "tauto2": tactic => `(tactic| (
  intro t
  simp only [truth]
  cases (truth t p) <;> cases (truth t q) <;> decide))

scoped macro "tauto3": tactic => `(tactic| (
  intro t
  simp only [truth]
  cases (truth t p) <;> cases (truth t q) <;> cases (truth t r) <;> decide))

lemma trivial: ⊨ (⊤: Prop' A) :=
  fun _ => rfl

lemma em: ⊨ or p (not p) := by
  intro
  simp only [truth, Bool.or_not_self]

lemma inl: ⊨ p![↑p → ↑p ∨ ↑q] := by tauto2
lemma inr: ⊨ p![↑p → ↑q ∨ ↑p] := by tauto2

lemma not_or_intro: ⊨ p![¬↑p → ¬↑q → ¬(↑p ∨ ↑q)] := by tauto2

lemma left: ⊨ p![↑p ∧ ↑q → ↑p] := by tauto2
lemma right: ⊨ p![↑p ∧ ↑q → ↑q] := by tauto2

lemma and: ⊨ p![↑p → ↑q → ↑p ∧ ↑q] := by tauto2

lemma split: ⊨ p![(↑p → ↑q → ↑r) → (↑p → ↑q) → ↑p → ↑r] := by tauto3

lemma absurd: ⊨ p![↑p → ¬↑p → ⊥] := by
  intro t
  simp only [truth, Bool.not_not, Bool.or_false, Bool.not_or_self]

lemma contra: ⊨ p![(¬↑p → ⊥) → ↑p] := by
  intro t
  simp only [truth, Bool.not_not, Bool.or_false, Bool.not_or_self]


end Tautologies
