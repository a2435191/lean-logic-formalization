import LogicFormalization.Chapter2.Section4.Term
import Mathlib.Data.Fin.VecNotation

namespace Homeworks

open Term HasVar

section Problem1
/-! TODO -/
end Problem1

section Problem2
/-! TODO -/
end Problem2

section Problem3
/-! TODO -/
end Problem3

section Problem4
/-! TODO -/
end Problem4

section Problem5

def 𝒩 : Structure .Rig ℕ where
  interpRel := nofun
  interpFun
  | .zero, _ => 0
  | .one,  _ => 1
  | .add,  a => a 0 + a 1
  | .mul,  a => a 0 * a 1

/-- 2.4 #5 (a) -/
theorem not_exists_nat_rig_term₁ : ¬∃ (t: Term .Rig) (x: Var) (hx: AreVarsFor ![x] t),
    interp t 𝒩 hx ![0] = 1 ∧ interp t 𝒩 hx ![1] = 0 :=
  sorry

/-- 2.4 #5 (b) -/
theorem not_exists_nat_rig_term₂ : ¬∃ (t: Term .Rig) (x: Var) (hx: AreVarsFor ![x] t),
    ∀ n, interp t 𝒩 hx ![n] = 2^n :=
  sorry

open Structure in
/-- 2.4 #5 (c). The only substructure of `𝒩` is `𝒩` itself. -/
theorem 𝒩.substructures: ∀ {A: Set ℕ} [Nonempty A] {𝒜: Structure .Rig A},
    𝒜 ⊆ 𝒩 ↔ HEq 𝒜 𝒩 :=
  sorry

end Problem5
