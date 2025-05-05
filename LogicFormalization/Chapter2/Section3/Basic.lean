import LogicFormalization.Chapter2.Section1.Arity
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Logic.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Set.Image

universe u v

structure Language where
  /-- The relational symbols. -/
  ρ: Type u
  /-- The functional symbols. -/
  ϝ: Type v
  [instArityRel: Arity ρ]
  [instArityFun: Arity ϝ]

namespace Language

-- TODO: automate basically all this for Gr as well as Ab, O, Ring, etc.
namespace Gr

inductive ρ
deriving Repr, DecidableEq

instance: Arity ρ :=
  ⟨(nomatch ·)⟩

inductive ϝ where
| one | inv | mul
deriving Repr, DecidableEq

instance: Arity ϝ where
  arity
  | .one => 0
  | .inv => 1
  | .mul => 2

/-! These instances make it possible to write e.g. `f 0` for
`f: Fin (arity Language.Gr.ϝ.inv) → G` (the `0` is a `Fin`). -/
instance: NeZero (arity Language.Gr.ϝ.inv) :=
  ⟨by decide⟩

instance: NeZero (arity Language.Gr.ϝ.mul) :=
  ⟨by decide⟩

end Gr

@[reducible]
def Gr := Language.mk Gr.ρ Gr.ϝ

end Language

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

def Gr {G: Type*} [Nonempty G] [Group G] : Structure Language.Gr G where
  interpRel := (nomatch ·)
  interpFun
  | .one, _ => 1
  | .inv, f => (f 0)⁻¹
  | .mul, f => (f 0) * (f 1)

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

lemma substructure_is_substructure {A: Set B} [Nonempty A] {ℬ: Structure L B}
    {h: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ↑·) ∈ A}: Substructure A ℬ h ⊆ ℬ :=
  ⟨h, rfl⟩

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

lemma StrongHom.mk' (hom: Hom 𝒜 ℬ h) (hh: ∀ R a, h ∘ a ∈ ℬ.interpRel R → a ∈ 𝒜.interpRel R):
    StrongHom 𝒜 ℬ h where
  hRel R a := ⟨hom.hRel R a, hh R a⟩
  hFun := hom.hFun

lemma StrongHom.toHom: StrongHom 𝒜 ℬ h → Hom 𝒜 ℬ h
| {hRel, hFun} => ⟨fun R a => (hRel R a).mp, hFun⟩

structure Emb extends StrongHom 𝒜 ℬ h where
  inj: Function.Injective h

structure Iso extends StrongHom 𝒜 ℬ h where
  bij: Function.Bijective h

abbrev Auto h := Iso 𝒜 𝒜 h

lemma emb_inclusion_map {A: Set B} [Nonempty ↑A] {𝒜: Structure L A} {ℬ: Structure L B}
    (h: 𝒜 ⊆ ℬ): Emb 𝒜 ℬ (fun a => a) :=
  have ⟨hR, hF⟩ := Structure.mk.inj h.h₂
  { inj := fun _ _ => Subtype.eq,
    hRel _R _a := hR ▸ Iff.rfl
    hFun _F _a := hF ▸ rfl }

def Substructure.ofHom {𝒜: Structure L A} {ℬ: Structure L B} {h: A → B} (hh: Hom 𝒜 ℬ h) :=
  Substructure (Set.range h) ℬ fun F bs => by
    let as (i): A := -- h(as) = bs
      Exists.choose (bs i).prop
    have has (i): h (as i) = bs i :=
      Exists.choose_spec (bs i).prop
    use (F^𝒜) as
    convert hh.hFun F as using 2
    funext i
    exact (has i).symm

lemma Substructure.ofHom_bijection_of_emb {𝒜: Structure L A} {ℬ: Structure L B} {h: A → B}
    (hh: Emb 𝒜 ℬ h): Iso 𝒜 (ofHom hh.toHom) (⟨h ·, Set.mem_range_self _⟩) :=
  have ⟨⟨hRel, hFun⟩, inj⟩ := hh
  { bij := ⟨fun _ _ ha => inj (Subtype.mk.injEq .. ▸ ha),
            fun ⟨_, a, ha⟩ => ⟨a, Subtype.eq ha⟩⟩,
    hRel := hRel,
    hFun := fun F a => Subtype.eq (hFun F a) }

variable {C: Type w} [Nonempty C]
variable {𝒜: Structure L A} {ℬ: Structure L B} {𝒞: Structure L C}
variable {i: A → B} {j: B → C}

lemma hom_comp (hj: Hom ℬ 𝒞 j) (hi: Hom 𝒜 ℬ i): Hom 𝒜 𝒞 (j ∘ i) where
  hRel R a ha :=
    have hj := hj.hRel R (i ∘ a)
    have hi := hi.hRel R a
    hj (hi ha)
  hFun F a :=
    have hj := hj.hFun F (i ∘ a)
    have hi := hi.hFun F a
    show j _ = _ from hi.symm ▸ hj

lemma strongHom_comp (hj: StrongHom ℬ 𝒞 j) (hi: StrongHom 𝒜 ℬ i): StrongHom 𝒜 𝒞 (j ∘ i) :=
  .mk' 𝒜 𝒞 (j ∘ i) (hom_comp hj.toHom hi.toHom) fun R a ha =>
   have hj := (hj.hRel R (i ∘ a)).mpr
   have hi := (hi.hRel R a).mpr
   hi (hj ha)

lemma emb_comp (hj: Emb ℬ 𝒞 j) (hi: Emb 𝒜 ℬ i): Emb 𝒜 𝒞 (j ∘ i) where
  toStrongHom := strongHom_comp hj.toStrongHom hi.toStrongHom
  inj := Function.Injective.comp hj.inj hi.inj

lemma iso_comp (hj: Iso ℬ 𝒞 j) (hi: Iso 𝒜 ℬ i): Iso 𝒜 𝒞 (j ∘ i) where
  toStrongHom := strongHom_comp hj.toStrongHom hi.toStrongHom
  bij := Function.Bijective.comp hj.bij hi.bij

lemma auto_comp {j i: A → A} (hj: Auto 𝒜 j) (hi: Auto 𝒜 i): Auto 𝒜 (j ∘ i) :=
  iso_comp hj hi

lemma auto_id: Auto 𝒜 id := by
  constructor
  · constructor <;> simp
  · exact Function.bijective_id

section -- TODO: maybe PR these to Mathlib?

open Function
variable {α: Type u} {β: Type v} [Nonempty α] {f: α → β}

private lemma bijective_invFun_of_bijective:
    Bijective f → Bijective (invFun f)
| ⟨_, _⟩ => by
  refine bijective_iff_has_inverse.mpr ⟨f, ?_, ?_⟩
  · apply RightInverse.leftInverse
    apply rightInverse_invFun
    assumption
  · apply LeftInverse.rightInverse
    apply leftInverse_invFun
    assumption

private lemma comp_invFun (hf: Surjective f): f ∘ invFun f = id :=
  funext <| rightInverse_invFun hf

end

open Function in
lemma auto_inv {i: A → A} (hi: Auto 𝒜 i): Auto 𝒜 (invFun i) :=
  have ⟨⟨hRel, hFun⟩, hinj, hsur⟩ := hi
  let iInv := invFun i
  { bij := bijective_invFun_of_bijective hi.bij,
    hRel R a := by
      have := hRel R (iInv ∘ a)
      convert this.symm
      rw [←comp_assoc, comp_invFun hsur]
      rfl
    hFun F a := by
      apply hinj
      have := hFun F (iInv ∘ a)
      convert this.symm
      show (i ∘ iInv) ((F^𝒜) a) = (F^𝒜) ((i ∘ iInv) ∘ a)
      repeat rw [comp_invFun hsur]
      rfl }

noncomputable instance Aut: Group {i: A → A // Auto 𝒜 i} where
  mul | ⟨i, hi⟩, ⟨j, hj⟩ => ⟨j ∘ i, auto_comp hj hi⟩
  mul_assoc a b c := rfl
  one := ⟨id, auto_id⟩
  one_mul a := rfl
  mul_one a := rfl
  inv | ⟨i, hi⟩ => ⟨Function.invFun i, auto_inv hi⟩
  inv_mul_cancel a := by
    dsimp only [HMul.hMul, OfNat.ofNat]
    congr 1
    exact comp_invFun a.prop.bij.right

-- TODO: examples

-- Somewhat clunky since `MonoidHom` is a `Type`
lemma group_hom_iff [Group A] [Group B] {h: A → B}: (∃ h': A →* B, ↑h' = h) ↔ Hom Gr Gr h := by
  constructor
  · intro ⟨⟨⟨h', h₁⟩, h₂⟩, hcoe⟩
    replace hcoe: h' = h := hcoe
    subst h'
    replace h₂: ∀ (x y : A), h (x * y) = h x * h y := h₂
    constructor
    · exact (nomatch ·)
    · rintro (_|_) <;> intro as
      · simpa only [Gr, forall_const]
      · simp only [Gr, Function.comp_apply]
        apply MonoidHom.map_inv ⟨⟨h, h₁⟩, h₂⟩
      · simp only [Gr]
        apply h₂
  · intro ⟨_, hFun⟩
    have (a₁ a₂: A): h (a₁ * a₂) = h a₁ * h a₂ := by
      have := hFun Language.Gr.ϝ.mul
      simp only [Gr] at this
      let a: Fin 2 → A
      | 0 => a₁
      | 1 => a₂
      exact this a
    exact ⟨MonoidHom.mk' h this, rfl⟩

-- TODO: show ring, etc. homomorphisms, isomorphisms are the same. Probably automate this
end Hom

-- TODO: congruence
-- TODO: products
-- TODO: homeworks
