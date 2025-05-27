import LogicFormalization.Chapter2.Section4.Term
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith.Frontend

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

section a
variable (f: ℕ → ℕ)
@[simp] abbrev isConstant := ∃ y, ∀ n, f n = y
@[simp] abbrev isGe := ∀ n, n ≤ f n
@[simp] abbrev isConstantOrGe := isConstant f ∨ isGe f

variable {u v: ℕ → ℕ}

lemma isConstant_or_isGe_of_add:
    isConstantOrGe u → isConstantOrGe v
    → isConstantOrGe (fun n => u n + v n)
| .inl ⟨yu, hu⟩, .inl ⟨yv, hv⟩ =>
  .inl ⟨yu + yv, fun n => by rw [←hu n, ←hv n]⟩
| _, .inr hv => .inr fun n => calc
  n ≤ v n := hv n
  _ ≤ u n + v n := Nat.le_add_left ..
| .inr hu, _ => .inr fun n => calc
  n ≤ u n := hu n
  _ ≤ u n + v n := Nat.le_add_right ..

lemma isConstant_or_isGe_of_mul:
    isConstantOrGe u → isConstantOrGe v
    → isConstantOrGe (fun n => u n * v n)
| .inl ⟨yu, hu⟩, .inl ⟨yv, hv⟩ =>
  .inl ⟨yu * yv, fun n => by rw [←hu n, ←hv n]⟩
| .inr hu, .inr hv => .inr fun
  | 0 => Nat.zero_le _
  | k + 1 => calc
    _ ≤ u (k + 1) := hu _
    _ ≤ _ := Nat.le_mul_of_pos_right _ <|
      have := hv (k + 1)
      by omega
| .inl ⟨0, hu⟩, .inr hv => .inl ⟨0, by simp [hu]⟩
| .inl ⟨k + 1, hu⟩, .inr hv => .inr fun n => calc
  n ≤ v n := hv n
  _ ≤ u n * v n := Nat.le_mul_of_pos_left _ (by simp [hu])
| .inr hu, .inl ⟨0, hv⟩ => .inl ⟨0, by simp [hv]⟩
| .inr hu, .inl ⟨k + 1, hv⟩ => .inr fun n => calc
  n ≤ u n := hu n
  _ ≤ u n * v n := Nat.le_mul_of_pos_right _ (by simp [hv])


/-- 2.4 #5 (a) -/
theorem not_exists_nat_rig_term₁ : ¬∃ (t: Term .Rig) (x: Var) (hx: AreVarsFor ![x] t),
    interp t 𝒩 hx ![0] = 1 ∧ interp t 𝒩 hx ![1] = 0 := by
  push_neg
  intro t x hx
  let f n := interp t 𝒩 hx ![n]
  -- either f := t^𝒩 is constant or f(n) ≥ n for all n.
  suffices isConstantOrGe f by
    match this with
    | .inl ⟨y, hy⟩ =>
      intro (h₀: f 0 = 1) (h₁: f 1 = 0)
      rw [hy 0] at h₀
      rw [hy 1, h₀] at h₁
      contradiction
    | .inr h =>
      intro _ (h₁: f 1 = 0)
      replace h := h 1
      rw [h₁] at h
      contradiction

  induction t with
  | var v => simp [f, interp]
  | app F ts ih =>
    cases hF : F <;> subst hF
    · exact .inl ⟨0, fun n => rfl⟩
    · exact .inl ⟨1, fun n => rfl⟩
    · apply isConstant_or_isGe_of_add <;> apply ih
    · apply isConstant_or_isGe_of_mul <;> apply ih
end a


/-- 2.4 #5 (b) -/
theorem not_exists_nat_rig_term₂ : ¬∃ (t: Term .Rig) (x: Var) (hx: AreVarsFor ![x] t),
    ∀ n, interp t 𝒩 hx ![n] = 2^n :=
  sorry

open Structure in
/-- 2.4 #5 (c). The only substructure of `𝒩` is `𝒩` itself. -/
theorem 𝒩.substructures: ∀ {M: Set ℕ} [Nonempty M] {ℳ: Structure .Rig M},
    ℳ ⊆ 𝒩 ↔ HEq ℳ 𝒩 :=
  sorry

end Problem5
