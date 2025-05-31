import LogicFormalization.Chapter2.Section4.Term
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring

namespace Homeworks

universe u

open Term

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

variable {V: Type u} [DecidableEq V]

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
theorem not_exists_nat_rig_term₁ : ¬∃ (t: Term .Rig V) (x: V) (hx: areVarsFor {x} t),
    interp t 𝒩 hx (fun _ => 0) = 1 ∧ interp t 𝒩 hx (fun _ => 1) = 0 := by
  push_neg
  intro t x hx
  let f n := interp t 𝒩 hx (fun _ => n)
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
    all_goals
      first
      | apply isConstant_or_isGe_of_add
      | apply isConstant_or_isGe_of_mul
      all_goals
        apply ih
        intro v hv
        apply hx
        exact ⟨_, hv⟩
end a


section b

/-- Represents polynomials with coefficients from `ℕ`. -/
inductive Poly
| const: ℕ → Poly
| var
| add: Poly → Poly → Poly
| mul: Poly → Poly → Poly

namespace Poly

def eval: Poly → ℕ → ℕ
| .const a, _ => a
| .var, n => n
| .add p q, n => p.eval n + q.eval n
| .mul p q, n => p.eval n * q.eval n

lemma eval_mono: ∀ {p: Poly}, Monotone p.eval
| .const _ => fun _ _ _ => Nat.le_refl _
| .var => fun _ _ => id
| .add _ _ => Monotone.add eval_mono eval_mono
| .mul _ _ => Monotone.mul' eval_mono eval_mono

/-- Degree of a polynomial -/
def deg: Poly → ℕ
| .const _ => 0
| .var => 1
| .add p q => max (deg p) (deg q)
| .mul p q => deg p + deg q

/-- Polynomials are homogenous. -/
lemma eval_mul_le {a n} (ha: a ≠ 0) : ∀ {p: Poly}, eval p (a * n) ≤ a^(deg p) * eval p n
| .const c | .var => by simp [eval, deg]
| .add q r => calc eval (add q r) (a * n)
  _ = eval q (a * n) + eval r (a * n) := rfl
  _ ≤ a^(deg q) * eval q n + a^(deg r) * eval r n :=
    Nat.add_le_add (eval_mul_le ha) (eval_mul_le ha)
  _ ≤ _ := by
    apply (Nat.le_or_ge (deg q) (deg r)).elim
    · intro h
      simp only [deg, h, sup_of_le_right, eval, Nat.mul_add, add_le_add_iff_right]
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right <;> simp [*, Nat.zero_lt_of_ne_zero]
    · intro h
      simp only [deg, h, sup_of_le_left, eval, Nat.mul_add, add_le_add_iff_left]
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_right <;> simp [*, Nat.zero_lt_of_ne_zero]
| .mul q r => calc eval (mul q r) (a * n)
  _ = eval q (a * n) * eval r (a * n) := rfl
  _ ≤ (a^(deg q) * eval q n) * (a^(deg r) * eval r n) :=
    Nat.mul_le_mul (eval_mul_le ha) (eval_mul_le ha)
  _ = _ := by simp [deg, eval]; ring

/-- Roughly speaking, use `eval_mul_le` to go from `p(n)`
to `p(2 * n / 2)` to `2^deg(p) p(n)`. This is complicated
by the fact that we are in `ℕ` and lack clean division.
We end up using `⌈n/2⌉` instead. -/
lemma eval_le_mul_eval_half {p: Poly} {n: ℕ}:
    eval p n ≤ 2^(deg p) * eval p ((n + 1) / 2) := calc _
  _ ≤ eval p (2 * ((n + 1) / 2)) := eval_mono (by omega)
  _ ≤ _ := eval_mul_le (by decide)

/-- p(n) does not converge to 2^n as n → ∞ -/
lemma eval_diverges_from_two_pow: ∀ p m, ∃ N, ∀ n ≥ N, m * eval p n < 2^n
| .const c, m => ⟨m * c, fun n hn => Nat.lt_of_le_of_lt hn Nat.lt_two_pow_self⟩
| .var, m => ⟨m + 1, fun n hn =>
  have: m ≤ n - 1 := Nat.le_sub_one_of_lt hn
  Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right n this) mul_pred_self_lt_two_pow⟩
| .add q r, m =>
  let ⟨Nq, hq⟩ := eval_diverges_from_two_pow q (2 * m)
  let ⟨Nr, hr⟩ := eval_diverges_from_two_pow r (2 * m)
  ⟨max Nq Nr, fun n hn => by
    replace hu := hq n (le_of_max_le_left hn)
    replace hv := hr n (le_of_max_le_right hn)
    have := Nat.add_lt_add hu hv
    simp_rw [Nat.two_mul, Nat.add_mul, ←Nat.two_mul, ←Nat.mul_add] at this
    exact Nat.lt_of_mul_lt_mul_left this⟩
| .mul q r, m =>
  -- this one is trickier. we make use of the homogeneity property (`eval_mul_le`)
  let ⟨Nq, hq⟩ := eval_diverges_from_two_pow q (m * 2^(deg q))
  let ⟨Nr, hr⟩ := eval_diverges_from_two_pow r (2 * 2^(deg r))
  ⟨(max Nq Nr) * 2, fun n hn => by
    replace hq := hq ((n + 1) / 2) (by omega)
    replace hr := hr ((n + 1) / 2) (by omega)
    replace hr: 2 ^ r.deg * r.eval ((n + 1) / 2) < 2 ^ ((n + 1) / 2 - 1) := by
      simp only [Nat.mul_assoc] at hr
      apply Nat.lt_of_mul_lt_mul_left (a := 2)
      rw [←Nat.pow_succ']
      apply Nat.lt_of_lt_of_le hr
      apply Nat.pow_le_pow_right (by decide)
      omega

    calc m * eval (mul q r) n
      _ = m * (eval q n * eval r n) := rfl
      _ ≤ m * ((2^(deg q) * eval q ((n + 1) / 2)) * (2^(deg r) * eval r ((n + 1) / 2))) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul <;> exact eval_le_mul_eval_half
      _ = (m * 2^(deg q) * eval q ((n + 1) / 2)) * (2^(deg r) * eval r ((n + 1) / 2)) := by ring
      _ < (2 ^ ((n + 1) / 2)) * (2 ^ ((n + 1) / 2 - 1)) := Nat.mul_lt_mul'' hq hr
      _ = 2 ^ ((n + 1) / 2 + ((n + 1) / 2 - 1)) := (Nat.pow_add ..).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)⟩
where
  mul_pred_self_lt_two_pow : ∀ {n: ℕ}, (n - 1) * n < 2^n
  | 0 => by decide
  | k + 1 => calc (k + 1 - 1) * (k + 1)
    _ = k * (k + 1) := rfl
    _ = (k - 1) * k + 2 * k := by
      simp only [Nat.mul_succ, Nat.sub_mul]
      have := Nat.sub_add_cancel (Nat.le_mul_self k)
      omega
    _ < 2 ^ k + 2 * k :=
      Nat.add_lt_add_right mul_pred_self_lt_two_pow _
    _ ≤ 2 ^ (k + 1) := by
      simp only [Nat.pow_succ, Nat.mul_two, add_le_add_iff_left]
      have: (k - 1) + 1 ≤ 2^(k-1) := Nat.lt_two_pow_self
      match k with
      | 0 => decide
      | l + 1 =>
        rw [Nat.add_sub_cancel] at this
        omega

/-- Convert one of the `L`-terms to a `Poly`. -/
def ofTerm (t: Term .Rig V) {x: V} (hx: areVarsFor {x} t):
    { p // ∀ n, interp t 𝒩 hx (fun _ => n) = eval p n } :=
  match t with
  | .var _ => ⟨.var, fun n => by simp [interp, eval]⟩
  | .app .zero _ => ⟨.const 0, fun n => rfl⟩
  | .app .one _ => ⟨.const 1, fun n => rfl⟩
  | .app .add ts =>
    let ⟨a, ha⟩ := ofTerm (ts 0) (areVarsFor_ofApp hx 0)
    let ⟨b, hb⟩ := ofTerm (ts 1) (areVarsFor_ofApp hx 1)
    ⟨.add a b, fun n => by simp only [eval, ←ha, ←hb]; rfl⟩
  | .app .mul ts =>
    let ⟨a, ha⟩ := ofTerm (ts 0) (areVarsFor_ofApp hx 0)
    let ⟨b, hb⟩ := ofTerm (ts 1) (areVarsFor_ofApp hx 1)
    ⟨.mul a b, fun n => by simp only [eval, ←ha, ←hb]; rfl⟩

end Poly


/-- 2.4 #5 (b) -/
theorem not_exists_nat_rig_term₂ : ¬∃ (t: Term .Rig V) (x: V) (hx: areVarsFor {x} t),
    ∀ n, interp t 𝒩 hx (fun _ => n) = 2^n :=
  fun ⟨t, x, hx, h⟩ =>
    let ⟨p, hp⟩ := Poly.ofTerm t hx
    have ⟨N, hN⟩ := Poly.eval_diverges_from_two_pow p 48
    by {
      have := hN N (Nat.le_refl N)
      rw [←h N, hp N] at this
      omega
    }

end b

open Structure in

/-- 2.4 #5 (c). The only substructure of `𝒩` is `𝒩` itself. -/
theorem 𝒩.substructures {M: Set ℕ} [Nonempty M] {ℳ: Structure .Rig M}:
    (Structure.IsSubstructure ℳ 𝒩) → M = Set.univ
| ⟨h₁, _⟩ => Set.eq_univ_of_forall (all_mem_M h₁)
where all_mem_M
    (h: ∀ (F : Language.Rig.ϝ) (a : Fin (arity F) → ↑M), (𝒩.interpFun F fun x => ↑(a x)) ∈ M):
    (n: ℕ) → n ∈ M
  | 0 => h .zero ![]
  | k + 1 =>
    h .add ![⟨k, all_mem_M h k⟩, ⟨1, h .one ![]⟩]

-- TODO: maybe show other way too? Should be trivial though
end Problem5
