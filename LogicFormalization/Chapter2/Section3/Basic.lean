import LogicFormalization.Chapter2.Section3.Meta
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.Set.Image

universe u v w

namespace Structure

-- TODO: more examples beyond those in Meta. See pp. 25-26

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

-- TODO: substructure examples from p. 26

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

-- TODO: examples at top of p. 27

lemma group_hom_iff [Group A] [Group B] {h: A → B}:
    (∀ x y: A, h (x * y) = h x * h y) ↔ Hom (Gr A) (Gr B) h := by
  refine ⟨fun hyp => ⟨nofun, fun F as => ?_⟩, fun ⟨hyp₁, hyp₂⟩ x y => ?_⟩
  · have h_one: h 1 = 1 := by
      have: h 1 = h 1 * h 1 := by rw [←hyp, one_mul]
      have := congr_arg (· * (h 1)⁻¹) this
      simp only [mul_assoc, mul_inv_cancel, mul_one] at this
      exact this.symm
    have h_inv: ∀ a, h a⁻¹ = (h a)⁻¹ := fun a => by
      apply eq_inv_of_mul_eq_one_left
      convert (hyp _ _).symm
      convert h_one.symm
      apply inv_mul_cancel
    cases F
    · exact h_one
    · apply h_inv
    · apply hyp
  · let xy: Fin 2 → A | 0 => x | 1 => y
    exact hyp₂ .mul xy

-- TODO: ring homomorphism proof, similar to above
end Hom

-- TODO: congruence
-- TODO: products
-- TODO: homeworks
