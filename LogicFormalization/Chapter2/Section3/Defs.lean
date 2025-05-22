import LogicFormalization.Chapter2.Section1.Arity
import Mathlib.Data.Set.Operations

universe u v

structure Language where
  /-- The relational symbols. -/
  ρ: Type u
  /-- The functional symbols. -/
  ϝ: Type v
  [instArityRel: Arity ρ]
  [instArityFun: Arity ϝ]

instance (L: Language): Arity L.ρ := L.instArityRel
instance (L: Language): Arity L.ϝ := L.instArityFun

universe w

structure Structure (L: Language) (A: Type u) [Nonempty A] where
  /-- The interpretation `R^𝒜` of the relational symbol `R` in `𝒜`. -/
  interpRel: (R: L.ρ) → Set (Fin (arity R) → A)
  /-- The interpretation `F^𝒜` of the functional symbol `F` in `𝒜`.
  See also `interpConst`. -/
  interpFun: (F: L.ϝ) → (Fin (arity F) → A) → A

namespace Structure
variable {L: Language}
variable {A: Type u} [Nonempty A] {B: Type v} [Nonempty B]

@[inherit_doc]
scoped notation:max R "^" 𝒜 => Structure.interpRel 𝒜 R

@[inherit_doc]
scoped notation:max F "^" 𝒜 => Structure.interpFun 𝒜 F

/-- We identify the interpretation `h^𝒜` for
constant symbol `c`, `h: arity c = 0`, with the value in `A`. -/
def interpConst (𝒜: Structure L A) {c: L.ϝ} (h: arity c = 0) :=
  𝒜.interpFun c fun f => (h ▸ f).elim0

@[inherit_doc]
scoped notation:max h "^" 𝒜 => Structure.interpConst 𝒜 h

section Substructure

/-- `Substructure A ℬ h` is the substructure in `ℬ` with underlying set `A`. -/
@[reducible, simp]
def Substructure (A: Set B) [Nonempty A] (ℬ: Structure L B)
    (h: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ↑·) ∈ A) : Structure L A where
  interpRel R := { a | (R^ℬ) (a ↑·) }
  interpFun F a := ⟨(F^ℬ) (a ↑·), h ..⟩

variable {A: Set B} [Nonempty A]
/-- `IsSubstructure 𝒜 ℬ`, written `A ⊆ B`, means `A` is a substructure of `B`. -/
structure IsSubstructure (𝒜: Structure L A) (ℬ: Structure L B): Prop where
  h₁: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ↑·) ∈ A
  h₂: 𝒜 = Substructure A ℬ h₁

@[inherit_doc]
scoped infix:50 " ⊆ " => IsSubstructure

end Substructure

section Hom

variable {A: Type u} [Nonempty A] {B: Type v} [Nonempty B]
variable (𝒜: Structure L A) (ℬ: Structure L B) (h: A → B)

structure Hom where
  hRel: ∀ R a, a ∈ 𝒜.interpRel R → h ∘ a ∈ ℬ.interpRel R
  hFun: ∀ F a, h ((𝒜.interpFun F) a) = (ℬ.interpFun F) (h ∘ a)

structure StrongHom where
  hRel: ∀ R a, a ∈ 𝒜.interpRel R ↔ h ∘ a ∈ ℬ.interpRel R
  hFun: ∀ F a, h ((𝒜.interpFun F) a) = (ℬ.interpFun F) (h ∘ a)

structure Emb extends StrongHom 𝒜 ℬ h where
  inj: Function.Injective h

structure Iso extends StrongHom 𝒜 ℬ h where
  bij: Function.Bijective h

abbrev Auto h := Iso 𝒜 𝒜 h

end Hom
end Structure
