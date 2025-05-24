import LogicFormalization.Chapter2.Section3.Meta
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Set.Image

universe u v w

namespace Structure

variable {L: Language} {B: Type v} [Nonempty B]

lemma substructure_is_substructure {A: Set B} [Nonempty A] {ℬ: Structure L B}
    {h: ∀ F (a: Fin (arity F) → A), interpFun ℬ F (a ↑·) ∈ A}: Substructure A ℬ h ⊆ ℬ :=
  ⟨h, rfl⟩

section Hom

variable {A: Type u} [Nonempty A]
variable (𝒜: Structure L A) (ℬ: Structure L B) (h: A → B)

lemma StrongHom.mk' (hom: Hom 𝒜 ℬ h) (hh: ∀ R a, h ∘ a ∈ ℬ.interpRel R → a ∈ 𝒜.interpRel R):
    StrongHom 𝒜 ℬ h where
  hRel R a := ⟨hom.hRel R a, hh R a⟩
  hFun := hom.hFun

lemma StrongHom.toHom: StrongHom 𝒜 ℬ h → Hom 𝒜 ℬ h
| {hRel, hFun} => ⟨fun R a => (hRel R a).mp, hFun⟩

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
lemma group_hom_iff [Group A] [Group B] {h: A → B}: (∃ h': A →* B, ↑h' = h) ↔ Hom (Gr A) (Gr B) h := by
  constructor
  · intro ⟨⟨⟨h', h₁⟩, h₂⟩, hcoe⟩
    replace hcoe: h' = h := hcoe
    subst h'
    replace h₂: ∀ (x y : A), h (x * y) = h x * h y := h₂
    constructor
    · nofun
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
