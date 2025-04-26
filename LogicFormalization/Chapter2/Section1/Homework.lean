import LogicFormalization.Chapter2.Section1.NormalForms
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card

namespace Homeworks

universe u
variable {A: Type u}

open Prop'

/-! Problems 1 and 2 can be found in NormalForms.lean. -/

section Problem3

@[reducible]
def fₚ (p: Prop' A): (A → Bool) → Bool :=
  fun t => truth t p

theorem exists_prop_for_truth_table [Fintype A]: ∀ f: (A → Bool) → Bool, ∃ p, f = fₚ p :=
  fun f =>
    sorry


end Problem3

section Problem4

abbrev quotient :=
  @Quotient (Prop' A) instSetoid

instance [Fintype A]: Fintype (@quotient A) :=
  sorry

theorem card_quotient [Fintype A]: Fintype.card (@quotient A) = 2^(2^(Fintype.card A)) :=
  sorry

end Problem4

-- TODO: Problem 5

end Homeworks
