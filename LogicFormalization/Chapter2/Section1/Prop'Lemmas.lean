import LogicFormalization.Chapter2.Section1.Notation
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Basic

-- set_option autoImplicit true

namespace Prop'

open Notation

-- TODO: show Prop' is isomorphic to admissible words
universe u
variable {A: Type u} {p q r: Prop' A} {t: A → Bool}

@[simp]
lemma length_pos: length p > 0 := by
  cases p <;> (unfold length; omega)

@[simp ←]
lemma top_eq_true: (⊤: Prop' A) = true :=
  rfl

@[simp ←]
lemma bot_eq_false: (⊥: Prop' A) = false :=
  rfl

section Lemma1

-- Kind of Lemma 2.1.1, since we already get constructor injectivity for free

lemma length_one_iff: length p = 1 ↔ p = ⊤ ∨ p = ⊥ ∨ ∃ a, p = atom a := by
  cases p <;> simp [Nat.ne_of_gt]

lemma length_gt_one_iff: length p > 1 ↔ (∃ q, p = not q) ∨ (∃ q r, p = or q r) ∨ (∃ q r, p = and q r) :=
  calc _
    _ ↔ ¬(length p = 1) :=
      match h: p.length with
      | 0 => absurd h (Nat.ne_of_gt length_pos)
      | 1 | _ + 2 => by simp [h]
    _ ↔ ¬(p = ⊤ ∨ p = ⊥ ∨ ∃ a, p = atom a) := not_congr length_one_iff
    _ ↔ _ := by cases hp: p <;> simp [hp]

end Lemma1

@[simp↓ high]
lemma truth_of_implies: truth t (implies p q) ↔ (truth t p → truth t q) := by
  rw [implies, truth, truth]
  cases (truth t p) <;> cases (truth t q) <;> decide

@[simp↓ high]
lemma truth_of_iff: truth t (iff p q) ↔ truth t p = truth t q := by
  rw [iff, truth]
  simp only [Bool.and_eq_true, truth_of_implies]
  cases (truth t p) <;> cases (truth t q) <;> decide

lemma equivalent_refl: equivalent p p :=
  fun _ => truth_of_iff.mpr rfl

lemma equivalent_symm: equivalent p q → equivalent q p :=
  fun h t => truth_of_iff.mpr (truth_of_iff.mp (h t)).symm

lemma equivalent_trans: equivalent p q → equivalent q r → equivalent p r :=
  fun h₁ h₂ t =>
    truth_of_iff.mpr <|
      Eq.trans
        (truth_of_iff.mp <| h₁ t)
        (truth_of_iff.mp <| h₂ t)

@[simp↓ high]
lemma equivalent_iff: equivalent p q ↔ ∀ t, truth t p = truth t q := by
  simp only [equivalent, tautology, truth_of_iff]

instance: Equivalence (@equivalent A) where
  refl := fun _ => equivalent_refl
  symm := equivalent_symm
  trans := equivalent_trans

instance: Setoid (Prop' A) where
  r := equivalent
  iseqv := instEquivalenceEquivalent

section Lemma2
lemma equivalent_of_or_self: equivalent (or p p) p :=
  fun _ => by rw [truth_of_iff, truth, Bool.or_self]

lemma equivalent_of_and_self: equivalent (and p p) p :=
  fun _ => by rw [truth_of_iff, truth, Bool.and_self]

lemma equivalent_of_or_symm: equivalent (or p q) (or q p) :=
  fun _ => by rw [truth_of_iff, truth, truth, Bool.or_comm]

lemma equivalent_of_and_symm: equivalent (and p q) (and q p) :=
  fun _ => by rw [truth_of_iff, truth, truth, Bool.and_comm]

lemma equivalent_of_or_assoc: equivalent (or p (or q r)) (or (or p q) r) := by
  intro
  rw [truth_of_iff]
  simp only [truth_of_iff, truth, Bool.or_assoc]

lemma equivalent_of_and_assoc: equivalent (and p (and q r)) (and (and p q) r) := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.and_assoc]

lemma equivalent_of_or_and: equivalent (or p (and q r)) (and (or p q) (or p r)) := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.or_and_distrib_left]

lemma equivalent_of_and_or: equivalent (and p (or q r)) (or (and p q) (and p r)) := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.and_or_distrib_left]

private lemma Bool.or_and_self {a b: Bool}: (a || (a && b)) = a := by
  cases a <;> simp

private lemma Bool.and_or_self {a b: Bool}: (a && (a || b)) = a := by
  cases a <;> simp

lemma equivalent_of_or_and_self: equivalent (or p (and p q)) p := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.or_and_self]

lemma equivalent_of_and_or_self: equivalent (and p (or p q)) p := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.and_or_self]

lemma equivalent_of_not_or: equivalent (not (or p q)) (and (not p) (not q)) := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.not_or]

lemma equivalent_of_not_and: equivalent (not (and p q)) (or (not p) (not q)) := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.not_and]

lemma equivalent_of_or_not_self: equivalent (or p (not p)) ⊤ := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.or_not_self]

lemma equivalent_of_and_not_self: equivalent (and p (not p)) ⊥ := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.and_not_self]

lemma equivalent_of_not_not: equivalent (not (not p)) p := by
  intro
  rw [truth_of_iff]
  simp only [truth, Bool.not_not]

end Lemma2

lemma equivalent_of_false_or: equivalent (or ⊥ p) p :=
  fun _ => by simp only [↓truth_of_iff, truth, Bool.false_or]

lemma equivalent_of_true_or: equivalent (or ⊤ p) ⊤ :=
  fun _ => by simp only [↓truth_of_iff, truth, Bool.true_or]

lemma equivalent_of_false_and: equivalent (and ⊥ p) ⊥ :=
  fun _ => by simp only [↓truth_of_iff, truth, Bool.false_and]

lemma equivalent_of_true_and: equivalent (and ⊤ p) p :=
  fun _ => by simp only [↓truth_of_iff, truth, Bool.true_and]

@[simp]
lemma tautologicalConsequence_of_empty: (∅: Set (Prop' A)) ⊨ p ↔ ⊨ p :=
  ⟨fun h t => h t (fun _ => False.elim), fun h t _ => h t⟩

lemma tautologicalConsequence_of_tautology (h: ⊨ p): ∀ {S: Set (Prop' A)}, S ⊨ p :=
  fun t _ => h t

variable {S T: Set (Prop' A)}

lemma left_models_of_union: models t (S ∪ T) → models t S :=
  fun h p hp => h p (Set.mem_union_left T hp)

lemma right_models_of_union: models t (S ∪ T) → models t T :=
  fun h => left_models_of_union (Set.union_comm .. ▸ h)

section Lemma3

lemma not_tautologicalConsequence_false: ⊭ (⊥: Prop' A) :=
  fun hn => Bool.false_ne_true (hn (fun _ => Bool.true))

lemma tautologicalConsequence_and: S ⊨ and p q ↔ S ⊨ p ∧ S ⊨ q := by
  constructor
  · intro h
    constructor
    all_goals
      intro t ht
      have := h t ht
      rw [truth, Bool.and_eq_true] at this
      simp only [this]
  · intro ⟨hl, hr⟩
    intro t ht
    rw [truth, Bool.and_eq_true]
    exact ⟨hl t ht, hr t ht⟩

-- stronger version of (2)
lemma tautologicalConsequence_or: S ⊨ p ∨ S ⊨ q → S ⊨ or p q := by
  rintro (h|h) t ht
  all_goals
    simp only [truth, h t ht, Bool.true_or, Bool.or_true]

lemma tautologicalConsequence_of_union: S ∪ {p} ⊨ q ↔ S ⊨ implies p q := by
  constructor
  · intro h t ht
    apply truth_of_implies.mpr
    intro hp
    apply h t
    rintro p' (hp'|hp')
    · exact ht p' hp'
    · exact hp' ▸ hp
  · intro h t ht
    apply (truth_of_implies (p := p)).mp
    · apply h
      apply left_models_of_union ht
    · apply right_models_of_union ht
      rfl

lemma tautologicalConsequence_mp: S ⊨ p → S ⊨ implies p q → S ⊨ q :=
  fun hp hpq t ht => truth_of_implies.mp (hpq t ht) (hp t ht)

end Lemma3

lemma antitone_models {S': Set (Prop' A)} (h: S ⊆ S'): models t S' → models t S :=
  fun h' p hp => h' p (h hp)

lemma no_model_for_union_of_tautologicalConsequence: S ⊨ p → ¬∃ t, models t (S ∪ {not p}) := by
  intro h ⟨t, ht⟩
  have h₁ := ht (not p) (Set.mem_union_right S rfl)
  have h₂ := h t (antitone_models (Set.subset_union_left) ht)
  rw [truth, h₂] at h₁
  contradiction

@[simp]
lemma truth_disj {ps: List (Prop' A)}: truth t (disj ps) = ps.any (truth t) :=
  match ps with
  | [] => rfl
  | p₀ :: ps' => by
    dsimp [disj]
    apply (List.eq_nil_or_concat' ps').elim
    · intro h
      simp only [h, List.foldl_nil, List.any_nil, Bool.or_false]
    · intro ⟨front, pLast, h⟩
      rw [h, List.foldl_concat, truth, List.any_append,
          List.any_cons, List.any_nil, Bool.or_false, ←Bool.or_assoc]
      congr 1
      rw [←disj, ←List.any]
      apply truth_disj
termination_by ps.length

@[simp]
lemma truth_conj {ps: List (Prop' A)}: truth t (conj ps) = ps.all (truth t) :=
  match ps with
  | [] => rfl
  | p₀ :: ps' => by
    dsimp [conj]
    apply (List.eq_nil_or_concat' ps').elim
    · intro h
      simp only [h, List.foldl_nil, List.all_nil, Bool.and_true]
    · intro ⟨front, pLast, h⟩
      rw [h, List.foldl_concat, truth, List.all_append,
          List.all_cons, List.all_nil, Bool.and_true, ←Bool.and_assoc]
      congr 1
      rw [←conj, ←List.all]
      apply truth_conj
termination_by ps.length

variable {ps qs: List (Prop' A)}

@[simp]
lemma truth_disj_append: truth t (disj (ps ++ qs)) = (ps.any (truth t) || qs.any (truth t)) := by
  simp only [truth_disj, List.any_append]

@[simp]
lemma truth_disj_append': truth t (disj (ps ++ qs)) = (truth t (disj ps) || truth t (disj qs)) := by
  simp only [truth_disj, List.any_append]

@[simp]
lemma truth_conj_append: truth t (conj (ps ++ qs)) = (ps.all (truth t) && qs.all (truth t)) := by
  simp only [truth_conj, List.all_append]

@[simp]
lemma truth_conj_append': truth t (conj (ps ++ qs)) = (truth t (conj ps) && truth t (conj qs)) := by
  simp only [truth_conj, List.all_append]

lemma truth_disj_and_disj: truth t (and (disj ps) (disj qs)) = ((ps.product qs).any fun (p, q) => truth t (and p q)) := by
  simp only [truth, truth_disj, List.any_eq, ←Bool.decide_and, Bool.and_eq_true, Prod.exists,
    List.pair_mem_product, decide_eq_decide]
  tauto

lemma truth_conj_or_conj: truth t (or (conj ps) (conj qs)) = ((ps.product qs).all fun (p, q) => truth t (or p q)) := by
  simp only [truth, truth_conj, List.all_eq, ←Bool.decide_or, Bool.or_eq_true, Prod.forall,
    List.pair_mem_product, and_imp, decide_eq_decide]
  constructor
  · rintro (h|h) _ _ ha hb
    <;> simp only [ha, hb, h, true_or, or_true]
  · intro h
    by_contra hn
    push_neg at hn
    have ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩ := hn
    apply (h x y hx₁ hy₁).elim <;> assumption
