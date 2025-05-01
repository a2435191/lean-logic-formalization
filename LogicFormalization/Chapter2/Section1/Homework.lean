import LogicFormalization.Chapter2.Section1.NormalForms
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.BigOperators

namespace Homeworks

universe u
variable {A: Type u} {t: A → Bool}

open Prop'

/-! Problems 1 and 2 can be found in NormalForms.lean. -/

section Problem3

/-- As defined in 2.2 #3. -/
@[reducible]
def fₚ (p: Prop' A): (A → Bool) → Bool :=
  fun t => truth t p

variable [Fintype A]

/-- Used in 2.2 #3, #4. Given a predicate on truth assignments, returns
a `Prop'` that is true in exactly the truth assignments that satisfy the predicate.
Noncomputable because the constructed proposition will depend on the order of
the elements in `Fintype.elems.toList (α := A)` (though it will not change in truth value). -/
noncomputable def satisfying (f: (A → Bool) → Bool): Prop' A :=
  let as: List A := Fintype.elems.toList
  let _: Fintype (A → Bool) := .ofFinite _
  let ts: List (A → Bool) := Fintype.elems.toList

  let (pos, neg) := ts.partition f
  and (matchingAtoms as pos) (not (matchingAtoms as neg))
where
  matchingAtoms (as: List A) (ts: List (A → Bool)): Prop' A :=
    disj <| ts.map fun t =>
      conj <| as.map fun a =>
        if t a then .atom a else .not (.atom a)

lemma satisfying.truth_of_matchingAtoms {ts: List (A → Bool)}: truth t (matchingAtoms Fintype.elems.toList ts) = decide (t ∈ ts) := by
  unfold matchingAtoms
  rw [truth_disj, List.any_map, List.any_eq]
  simp only [Function.comp_apply, truth_conj, List.all_map, List.all_eq_true, Finset.mem_toList]
  simp only [Fintype.complete, forall_const]
  symm
  apply Bool.decide_congr
  constructor
  · intro h
    exists t, h
    intro a
    split_ifs with h'
    · exact h'
    · exact Bool.not_iff_not.mpr h'
  · intro ⟨t', ht'₁, ht'₂⟩
    convert ht'₁
    funext a
    have := ht'₂ a
    split_ifs at this with h'
    · rwa [h']
    · simp_all [h', this, truth]

lemma truth_of_satisfying {f: (A → Bool) → Bool}: truth t (satisfying f) = f t := by
  simp [satisfying, truth, satisfying.truth_of_matchingAtoms, Fintype.complete]

/-- 2.2 #3 -/
theorem exists_prop_for_truth_table (f: (A → Bool) → Bool): ∃ p, f = fₚ p :=
  ⟨satisfying f, funext fun _ => truth_of_satisfying.symm⟩

end Problem3

section Problem4

/-- For 2.2 #4, quotient over `Prop' A` by `equivalent`. -/
@[reducible]
def EquivalenceQuotient (A: Type u) :=
  @Quotient (Prop' A) instSetoid

noncomputable local instance [Finite A]: Fintype A :=
  Fintype.ofFinite A

lemma bijective_quotient_satisfying [Fintype A]: Function.Bijective (⟦satisfying ·⟧) (β := EquivalenceQuotient A) := by
  constructor
  · intro f g h
    rw [Quotient.eq] at h
    funext t
    have := h t
    rwa [truth_of_iff, truth_of_satisfying, truth_of_satisfying] at this
  · apply Quotient.ind
    intro p
    use fₚ p
    rw [Quotient.eq]
    intro t
    rw [truth_of_iff, truth_of_satisfying]

instance [Finite A]: Finite (EquivalenceQuotient A) :=
  (Function.Bijective.finite_iff
    bijective_quotient_satisfying).mp inferInstance

/-- 2.2 #4 -/
theorem card_quotient [Finite A]: Fintype.card (EquivalenceQuotient A) = 2 ^ 2 ^ Fintype.card A := by
  classical
  rw [←Fintype.card_of_bijective bijective_quotient_satisfying,
    Fintype.card_fun, Fintype.card_fun, Fintype.card_bool]

end Problem4

-- TODO: Problem 5

end Homeworks
