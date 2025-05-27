import LogicFormalization.Chapter2.Section1.Arity
import Mathlib.Data.Set.Operations
import Mathlib.Data.Quot

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
variable {A: Type u} [Nonempty A] {B: Type v}

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

set_option synthInstance.checkSynthOrder false in
scoped instance (A: Set B) [inst: Nonempty A]: Nonempty B :=
  ⟨↑(Classical.choice inst)⟩

/-- `Substructure A ℬ h` is the substructure in `ℬ` with underlying set `A`. -/
@[reducible, simp]
def Substructure (A: Set B) [Nonempty A] (ℬ: Structure L B)
    (h: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ·) ∈ A) : Structure L A where
  interpRel R := { a | (R^ℬ) (a ·) }
  interpFun F a := ⟨(F^ℬ) (a ·), h ..⟩

variable {A: Set B} [Nonempty A]
/-- `IsSubstructure 𝒜 ℬ`, written `A ⊆ B`, means `A` is a substructure of `B`. -/
structure IsSubstructure (𝒜: Structure L A) (ℬ: Structure L B): Prop where
  h₁: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ·) ∈ A
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

structure Congruence (𝒜: Structure L A) where
  /-- The equivalence relation on `A`. -/
  r: A → A → Prop
  hEquiv: Equivalence r
  hRel: ∀ R: L.ρ, ∀ a b, (∀ i, r (a i) (b i)) → (a ∈ (R^𝒜) ↔ b ∈ R^𝒜)
  hFun: ∀ F: L.ϝ, ∀ a b, (∀ i, r (a i) (b i)) → r ((F^𝒜) a) ((F^𝒜) b)


namespace Congruence
variable [Nonempty B]

/-- The congruence `~ₕ`. -/
def ofStrongHom {𝒜: Structure L A} {ℬ: Structure L B} {h: A → B}
    (hh: StrongHom 𝒜 ℬ h): Congruence 𝒜 where
  r a₁ a₂ := h a₁ = h a₂
  hEquiv := by constructor <;> intros <;> simp_all only
  hRel R a b hyp := by
    have: h ∘ a = h ∘ b := funext hyp
    rw [hh.hRel, this, hh.hRel]
  hFun F a b hyp := by
    have: h ∘ a = h ∘ b := funext hyp
    rw [hh.hFun, this, hh.hFun]

-- for `quotient`
instance [h: Nonempty A] [s: Setoid A]: Nonempty (Quotient s) :=
  (nonempty_quotient_iff s).mpr h

def toSetoid (𝒜: Structure L A): Congruence 𝒜 → Setoid A
| { r, hEquiv, .. } => ⟨r, hEquiv⟩

noncomputable def quotient (𝒜: Structure L A) (c: Congruence 𝒜):
    Structure L (Quotient c.toSetoid) where
  interpRel R a := (R^𝒜) fun i => (a i).out
  interpFun F a := ⟦(F^𝒜) fun i => (a i).out⟧

end Congruence

/-! Recall that the arbitrary (incl. infinite) product of types indexed by `I`
can be represented by
```
def typeProduct (I: Type u) (βs: I → Type v) :=
  (i: I) → βs i
```
-/

section

variable {I: Type u} {β: I → Type v}
  (hβ: ∀ i, Nonempty (β i)) (ℬ: (i: I) → Structure L (β i))

/-- The product of `L`-structures `ℬᵢ` over `i ∈ I`, a possibly infinite indexing type. -/
def product: Structure L ((i: I) → β i) where
  interpRel R b := ∀ i: I, (R^(ℬ i)) (fun j => b j i)
  interpFun F b i := (F^(ℬ i)) (fun j => b j i)

end
end Structure
