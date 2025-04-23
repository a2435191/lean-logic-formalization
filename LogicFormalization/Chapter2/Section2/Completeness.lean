import LogicFormalization.Chapter2.Section1.Tautologies
import LogicFormalization.Chapter2.Section2.Notation
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Minimal
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Lattice


namespace Prop'

open Notation
open Classical (choice)

universe u
variable {A: Type u} {S: Set (Prop' A)} {p q r: Prop' A}

open Tautologies in
lemma tautology_axiom (h: Axiom p): ⊨ p := by
  cases h <;> simp only [
    Tautologies.trivial, inl, inr, Tautologies.not_or_intro, left,
    right, Tautologies.and, split, Tautologies.absurd, contra]

lemma mp: S ⊢ p → S ⊢ implies p q → S ⊢ q
| ⟨pf_p⟩, ⟨pf_pq⟩ => ⟨.mp p pf_p pf_pq⟩

lemma mp₂: S ⊢ p → S ⊢ q → S ⊢ p![↑p → ↑q → ↑r] → S ⊢ r
| hp, hq, hpqr => mp hq <| mp hp hpqr

def weakenProof {S S': Set (Prop' A)} (h: S ⊆ S') {p: Prop' A}: Proof S p → Proof S' p
| .assumption hp => .assumption (h hp)
| .axiom hp => .axiom hp
| .mp r hr hrp => .mp r (weakenProof h hr) (weakenProof h hrp)

lemma weaken {S S': Set (Prop' A)} (h: S ⊆ S'): S ⊢ p → S' ⊢ p
| ⟨hp⟩ => ⟨weakenProof h hp⟩

lemma weaken_empty: ⊢ p → S ⊢ p
| ⟨hp⟩ => ⟨weakenProof (Set.empty_subset S) hp⟩

def weakenProofEmpty: Proof ∅ p → Proof S p :=
  weakenProof (Set.empty_subset S)

lemma proof_true: ⊢ (⊤: Prop' A) :=
  ⟨.axiom .trivial⟩

lemma proof_true': S ⊢ (⊤: Prop' A) :=
  ⟨.axiom .trivial⟩

/-- Lemma 2.2.1 -/
lemma proof_implies_self: ⊢ (implies p p) :=
  have h₁: Proof ∅ p![↑p → (↑p → ↑p) → ↑p] := .axiom (.inr p (not (implies p p)))
  have h₂: Proof ∅ p![(↑p → (↑p → ↑p) → ↑p) → (↑p → ↑p → ↑p) → ↑p → ↑p] :=
    .axiom (.split p (implies p p) p)
  have h₃: Proof ∅ p![(↑p → ↑p → ↑p) → ↑p → ↑p] := .mp _ h₁ h₂
  have h₄: Proof ∅ p![↑p → ↑p → ↑p] := .axiom (.inr p (not p))
  ⟨.mp _ h₄ h₃⟩

/-- Proposition 2.2.2 -/
theorem sound {p: Prop' A} (h: S ⊢ p): S ⊨ p :=
  f (choice h)
where f {S} {p}: Proof S p → S ⊨ p
  | .assumption hS => fun _ ht => ht _ hS
  | .axiom hp => tautologicalConsequence_of_tautology (tautology_axiom hp)
  | .mp _ hr hrp => tautologicalConsequence_mp (f hr) (f hrp)

lemma not_proof_false: ⊬ (⊥: Prop' A) :=
    not_tautologicalConsequence_false
    ∘ tautologicalConsequence_of_empty.mp
    ∘ sound

lemma consistent_empty: consistent (∅: Set (Prop' A)) :=
  not_proof_false

section Lemma7

lemma left': ⊢ p![↑p → ↑q → ↑p] :=
  ⟨.axiom (.inr p (not q))⟩

lemma generalize (h: ⊢ q): ⊢ implies p q :=
  mp h left'

lemma right': ⊢ p![↑p → ↑q → ↑q] :=
  generalize proof_implies_self


open Classical in
noncomputable def deduction.f {S} {p q: Prop' A}: Proof (S ∪ {p}) q → Proof S (implies p q)
| .axiom hq =>
  .mp q (.axiom hq) (weakenProofEmpty (choice left'))
| .assumption hS => by
  rw [Set.union_singleton, Set.mem_insert_iff] at hS
  apply hS.by_cases <;> intro h
  · subst h
    apply weakenProofEmpty (S := S)
    exact choice proof_implies_self
  · exact .mp q (.assumption h) (weakenProofEmpty (choice left'))
| .mp r hr hrq =>
  have h₁: Proof S p![(↑p → ↑r → ↑q) → (↑p → ↑r) → ↑p → ↑q] :=
    .axiom <| Axiom.split p r q
  have h₂: Proof S p![(↑p → ↑r) → ↑p → ↑q] :=
    .mp p![↑p → ↑r → ↑q] (deduction.f hrq) h₁
  .mp (implies p r) (deduction.f hr) h₂

/-- Lemma 2.2.7 -/
lemma deduction: S ∪ {p} ⊢ q → S ⊢ (implies p q) :=
  fun ⟨h⟩ => ⟨deduction.f h⟩

end Lemma7

/-- Corollary 2.2.8 -/
lemma proof_iff_inconsistent_neg: S ⊢ p ↔ inconsistent (S ∪ {not p}) := ⟨
  fun ⟨pf⟩ =>
    have h₁: Proof (S ∪ {not p}) p![↑p → ¬↑p → ⊥] := .axiom (.absurd p)
    have h₂: Proof (S ∪ {not p}) p![¬↑p → ⊥] := .mp p (weakenProof (Set.subset_union_left) pf) h₁
    have h₃: Proof (S ∪ {not p}) (not p) := .assumption (Set.mem_union_right S rfl)
    ⟨.mp (not p) h₃ h₂⟩,
  fun pf =>
    have ⟨pf'⟩ := deduction pf
    ⟨.mp (implies (not p) ⊥) pf' (.axiom (.contra p))⟩⟩

/-- Corollary 2.2.9 -/
lemma consistent_union_of_consistent: consistent S ∧ S ⊢ p → consistent (S ∪ {p}) :=
  fun ⟨hS, hp⟩ hn => hS (mp hp (deduction hn))

section Lemma11

variable {Sᵢ: Set (Set (Prop' A))}

lemma finite_family_of_proof: ⋃₀ Sᵢ ⊢ p → ∃ Sᵢ' ⊆ Sᵢ, Sᵢ'.Finite ∧ ⋃₀ Sᵢ' ⊢ p
| ⟨pf⟩ => f pf
where f {p}: Proof (⋃₀ Sᵢ) p → ∃ Sᵢ' ⊆ Sᵢ, Sᵢ'.Finite ∧ ⋃₀ Sᵢ' ⊢ p
  | .axiom h => ⟨∅,
    Set.empty_subset Sᵢ,
    Set.finite_empty,
    Set.sUnion_empty ▸ ⟨.axiom h⟩⟩
  | .mp _r hr hrp =>
    have ⟨Sᵣ, hSᵣ₁, hSᵣ₂, hSᵣ₃⟩ := f hr
    have ⟨Sᵣₚ, hSᵣₚ₁, hSᵣₚ₂, hSᵣₚ₃⟩ := f hrp
    ⟨Sᵣ ∪ Sᵣₚ,
      Set.union_subset hSᵣ₁ hSᵣₚ₁,
      Set.Finite.union hSᵣ₂ hSᵣₚ₂,
      mp
        (weaken (Set.sUnion_subset_sUnion Set.subset_union_left) hSᵣ₃)
        (weaken (Set.sUnion_subset_sUnion Set.subset_union_right) hSᵣₚ₃)⟩
  | .assumption hp =>
    have ⟨S, hp'₁, hp'₂⟩ := Set.mem_sUnion.mp hp
    ⟨{S},
      Set.singleton_subset_iff.mpr hp'₁,
      Set.finite_singleton S,
      Set.sUnion_singleton _ ▸ ⟨.assumption hp'₂⟩⟩

open Classical in
lemma single_set_of_proof: IsChain (· ⊆ ·) Sᵢ → Sᵢ.Nonempty → ⋃₀ Sᵢ ⊢ p → ∃ Sⱼ: Set (Prop' A), Sⱼ ∈ Sᵢ ∧ Sⱼ ⊢ p := by
  intro hChain hNonempty hProves
  have ⟨Sᵢ', hSᵢ'₁, hSᵢ'₂, hSᵢ'₃⟩ := finite_family_of_proof hProves
  if hNonempty': Sᵢ'.Nonempty then
    have ⟨S, hS⟩ := hNonempty'
    have ⟨M, _, hM₁, hM₂⟩ := Set.Finite.exists_le_maximal hSᵢ'₂ hS
    refine ⟨M, hSᵢ'₁ hM₁, ?_⟩
    apply weaken ?_ hSᵢ'₃
    rw [Set.sUnion_subset_iff]
    intro Y hY
    if hYM: Y = M then
      exact Eq.subset hYM
    else
      have hChain': IsChain (· ⊆ ·) Sᵢ' := IsChain.mono hSᵢ'₁ hChain
      have := hChain' hY hM₁ hYM
      apply this.elim
      · exact id
      · exact hM₂ hY
  else
    have := Set.not_nonempty_iff_eq_empty.mp hNonempty'
    have ⟨S, hS⟩ := hNonempty
    simp only [this, Set.sUnion_empty] at hSᵢ'₃
    exact ⟨S, hS, weaken_empty hSᵢ'₃⟩

/-- Lemma 2.2.11 -/
lemma lindenbaum: consistent S → ∃ S' ⊇ S, complete S' :=
  fun hS =>
    let P := { S' | consistent S' ∧ S ⊆ S' }
    have := zorn_subset_nonempty (S := P) <| by
      intro Sᵢ h₁ h₂ h₃
      refine ⟨⋃₀ Sᵢ, Set.mem_setOf.mpr ⟨?_, ?_⟩, ?_⟩
      · intro hpf
        have ⟨Sⱼ, hSⱼ₁, hSⱼ₂⟩ := single_set_of_proof h₂ h₃ hpf
        have ⟨this, _⟩ := h₁ hSⱼ₁
        exact this hSⱼ₂
      · have ⟨S₀, hS₀⟩ := Classical.indefiniteDescription _ h₃
        intro p hp
        exact ⟨S₀, hS₀, (h₁ hS₀).right hp⟩
      · intro S hS
        apply Set.subset_sUnion_of_subset Sᵢ S
        · exact subset_refl ..
        · exact hS
    have ⟨M, hM₁, hM₂, hM₃⟩ := this S ⟨hS, subset_refl S⟩
    have: ∀ p, M ⊢ p ∨ M ⊢ not p := fun p =>
      Classical.byCases
        .inl
        fun hn => .inr <|
          have: consistent (M ∪ {not p}) :=
            proof_iff_inconsistent_neg.not.mp hn
          have: M ∪ {p.not} ∈ P := ⟨this, Set.subset_union_of_subset_left hM₁ {p.not}⟩
          have: (not p) ∈ M :=
            have := hM₃ this Set.subset_union_left
            (Set.union_subset_iff.mp this).right rfl
          Nonempty.intro (.assumption this)
    ⟨M, hM₁, hM₂.left, this⟩

alias exists_complete_superset_of_consistent := lindenbaum

end Lemma11

section Lemma12

lemma complete_proof_not_iff_not_proof: complete S → (S ⊢ not p ↔ S ⊬ p)
| ⟨h₁, h₂⟩ => ⟨
  fun h hn =>
    h₁ (mp₂ hn h ⟨.axiom (.absurd p)⟩),
  (h₂ p).resolve_left⟩

lemma complete_proof_iff_not_proof_not: complete S → (S ⊢ p ↔ S ⊬ not p)
| h =>
  calc S ⊢ p
    _ ↔ ¬(¬S ⊢ p) := not_not.symm
    _ ↔ ¬S ⊬ p := ⟨id, id⟩
    _ ↔ S ⊬ not p := (complete_proof_not_iff_not_proof h).not.symm

lemma no_proof_contradiction_of_consistent: consistent S → ¬(S ⊢ p ∧ S ⊢ not p)
| h, ⟨hn₁, hn₂⟩ =>
  h (mp₂ hn₁ hn₂ ⟨.axiom (.absurd p)⟩)

open Classical in
/-- Lemma 2.2.12 -/
lemma proves_iff_truth_of_proves? {S: Set (Prop' A)} {p: Prop' A}: complete S → (S ⊢ p ↔ truth (proves? S) p)
| h@⟨h₁, h₂⟩ => by
  match p with
  | ⊤ => simp only [proof_true', truth]
  | ⊥ =>
    refine (iff_false_right ?_).mpr h₁
    simp only [truth]
    exact Bool.false_ne_true
  | .atom a =>
    rw [truth, proves?, decide_eq_true_eq]
    rfl
  | .not q =>
    have hq := proves_iff_truth_of_proves? h (p := q)
    constructor <;> intro h'
    · rw [truth, Bool.not_iff_not.mpr]
      rw [←hq]
      intro hn
      exact no_proof_contradiction_of_consistent h₁ ⟨hn, h'⟩
    · apply (complete_proof_not_iff_not_proof h).mpr
      rw [truth, Bool.not_eq_true'] at h'
      rwa [h', Bool.false_eq_true, iff_false] at hq
  | .or q r =>
    have hq := proves_iff_truth_of_proves? h (p := q)
    have hr := proves_iff_truth_of_proves? h (p := r)
    rw [truth, Bool.or_eq_true]
    constructor
    · intro h'
      by_contra hn
      simp only [not_or, Bool.not_eq_true] at hn
      rw [hn.left, Bool.false_eq_true, iff_false] at hq
      rw [hn.right, Bool.false_eq_true, iff_false] at hr
      replace hq := (complete_proof_not_iff_not_proof h).mpr hq
      replace hr := (complete_proof_not_iff_not_proof h).mpr hr
      have: S ⊢ not (or q r) := mp₂ hq hr ⟨.axiom (.notOr q r)⟩
      exact no_proof_contradiction_of_consistent h₁ ⟨h', this⟩
    · rw [←hq, ←hr]
      rintro (h|h)
      · exact mp h ⟨.axiom (.inl q r)⟩
      · exact mp h ⟨.axiom (.inr r q)⟩
  | .and q r =>
    have hq := proves_iff_truth_of_proves? h (p := q)
    have hr := proves_iff_truth_of_proves? h (p := r)
    rw [truth, Bool.and_eq_true, ←hq, ←hr]
    constructor
    · intro h'
      have hq' := mp h' ⟨.axiom (.left q r)⟩
      have hr' := mp h' ⟨.axiom (.right q r)⟩
      exact ⟨hq', hr'⟩
    · intro ⟨hq', hr'⟩
      exact mp₂ hq' hr' ⟨.axiom (.and q r)⟩

lemma proves?_models: complete S → models (proves? S) S :=
  fun hS _p hp => (proves_iff_truth_of_proves? hS).mp ⟨.assumption hp⟩

end Lemma12

/-- Theorem 2.2.5 (statement) -/
@[simp]
theorem completeness₂: consistent S ↔ ∃ t, models t S := by
  constructor
  · intro h
    have ⟨S', hS'₁, hS'₂⟩ := lindenbaum h
    use proves? S'
    apply antitone_models hS'₁
    exact proves?_models hS'₂
  · intro ⟨t, ht⟩ hn
    exact Bool.false_ne_true (sound hn t ht)

/-- Theorem 2.2.3 (statement) / Corollary 2.2.10 (proof) -/
@[simp]
theorem completeness₁: S ⊢ p ↔ S ⊨ p := by
  constructor
  · exact sound
  · intro h'
    apply proof_iff_inconsistent_neg.mpr
    have := (completeness₂ (S := S ∪ {not p})).not_right
    apply this.mpr
    apply no_model_for_union_of_tautologicalConsequence
    exact h'

section Theorem4

private lemma Set.sUnion_of_singleton {α: Type u} {S: Set α}: ⋃₀ (Set.singleton '' S) = S := by
  apply Set.ext
  simp only [Set.sUnion_image, Set.mem_iUnion, exists_prop]
  apply exists_eq_right'

lemma finite_subset_of_proof: S ⊢ p → ∃ S' ⊆ S, S'.Finite ∧ S' ⊢ p :=
  fun h =>
    -- use finite_family_of_proof, with each element of the family just a singleton
    let family := Set.singleton '' S
    have hfamily: ⋃₀ family = S := Set.sUnion_of_singleton
    have ⟨family', hfamily'₁, hfamily'₂, hfamily'₃⟩ :=
      finite_family_of_proof (hfamily.symm ▸ h)
    ⟨⋃₀ family',
      hfamily.symm ▸ Set.sUnion_subset_sUnion hfamily'₁,
      Set.Finite.sUnion hfamily'₂ (fun t ht =>
        have := hfamily'₁ ht
        have ⟨_, _, ht'⟩ := (Set.mem_image Set.singleton S t).mp this
        ht' ▸ (Set.finite_singleton _)),
      hfamily'₃⟩

alias compactness₁' := finite_subset_of_proof

/-- Theorem 2.2.4 -/
theorem compactness₁: S ⊨ p → ∃ S₀ ⊆ S, S₀.Finite ∧ S₀ ⊨ p := by
  simp only [←completeness₁]
  exact finite_subset_of_proof

end Theorem4

/-- Corollary 2.2.6 -/
theorem compactness₂: (∃ t, models t S) ↔ ∀ S₀ ⊆ S, S₀.Finite → ∃ t, models t S₀ := by
  simp only [←completeness₂]
  constructor <;> intro h
  · intro S' hS'₁ hS'₂ hn
    exact h (weaken hS'₁ hn)
  · intro hn
    have ⟨S', hS'₁, hS'₂, hS'₃⟩ := finite_subset_of_proof hn
    apply h S' <;> assumption

end Prop'
