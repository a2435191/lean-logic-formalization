import LogicFormalization.Chapter2.Section1.Prop'Lemmas

namespace Prop'

universe u v
variable {A: Type u} {p q: Prop' A} {t: A → Bool}

@[reducible]
def isLiteral: Prop' A → Prop
| .atom _ | .not (.atom _) => True
| _ => False

@[reducible]
def Literal (A: Type u) :=
  {p: Prop' A // isLiteral p}

namespace Literal
abbrev atom: A → Literal A
| a => ⟨.atom a, trivial⟩

abbrev notAtom: A → Literal A
| a => ⟨.not (.atom a), trivial⟩

/-- Take `a` to `¬a` and `¬a` to `a`. -/
abbrev not: Literal A → Literal A
| ⟨.atom a, _⟩ => .notAtom a
| ⟨.not (.atom a), _⟩ => .atom a

def rec {motive: Literal A → Sort v}
  (atom: ∀ a, motive (.atom a)) (not: ∀ a, motive (.not (.atom a)))
: ∀ a: Literal A, motive a := by
  rintro (_|_)
  case atom => apply atom
  case not =>
    rename_i a _
    cases a <;> try contradiction
    apply not
  all_goals contradiction

lemma equivalent_of_not: ∀ p: Literal A, equivalent (Prop'.not p) (Literal.not p).val := by
  apply rec
  all_goals
    intro a
    apply equivalent_iff.mpr
    intro t
    simp only [truth, Bool.not_not]

lemma truth_not: ∀ {p: Literal A}, truth t (Prop'.not p) = truth t (Literal.not p) :=
  fun {p} =>
    (equivalent_iff.mp (equivalent_of_not p)) t

end Literal

instance: DecidablePred (@isLiteral A) := by
  intro
  unfold isLiteral
  split <;> infer_instance

lemma isLiteral_iff: isLiteral p ↔ (∃ a, p = atom a) ∨ (∃ a, p = not (atom a)) := by
  cases p <;> try tauto
  · rename_i a
    cases a <;> simp [isLiteral]


mutual
/-- Disjunctive normal form -/
@[reducible]
def disjNF: Prop' A → List (List (Literal A))
| .true => [[]]
| .false => []
| .atom a => [[.atom a]]
| .or p q => disjNF p ++ disjNF q
| .and p q => List.product (disjNF p) (disjNF q)|>.map fun (a, b) => a ++ b
| .not p => (conjNF p).map (List.map Literal.not)

/-- Conjunctive normal form -/
@[reducible]
def conjNF: Prop' A → List (List (Literal A))
| .true => []
| .false => [[]]
| .atom a => [[.atom a]]
| .or p q => List.product (conjNF p) (conjNF q)|>.map fun (a, b) => a ++ b
| .and p q => conjNF p ++ conjNF q
| .not p => (disjNF p).map (List.map Literal.not)
end

@[simp, reducible]
def disjNF' (p: Prop' A): Prop' A :=
  disjNF p
    |>.map List.unattach
    |>.map conj
    |> disj

@[simp, reducible]
def conjNF' (p: Prop' A): Prop' A :=
  conjNF p
    |>.map List.unattach
    |>.map disj
    |> conj

open Notation in
#eval do
  let p := p![(¬@'a' ∨@'b') ∧ ¬@'c' ∧ ⊤]
  println! p
  println! (disjNF p, disjNF' p)
  println! (conjNF p, conjNF' p)

namespace List
variable {α: Type u} {β: Type v} {l₁ l₂: List (List α)} {pred: List α → Bool}

protected lemma any_eq' (hf: ∀ x y, pred (x ++ y) = (pred x && pred y)): (l₁.any pred && l₂.any pred) = (l₁.product l₂).any (pred ∘ (fun (x, y) => x ++ y)) := by
  simp only [List.any_eq, ←Bool.decide_and]
  congr 1
  apply propext
  constructor
  · intro ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩
    refine ⟨(x, y), List.pair_mem_product.mpr ⟨hx₁, hy₁⟩, ?_⟩
    rw [Function.comp_apply, hf, hx₂, hy₂, Bool.and_self]
  · intro ⟨(x, y), hxy₁, hxy₂⟩
    rw [List.pair_mem_product] at hxy₁
    rw [Function.comp_apply, hf x y, Bool.and_eq_true] at hxy₂
    exact ⟨⟨x, hxy₁.left, hxy₂.left⟩, ⟨y, hxy₁.right, hxy₂.right⟩⟩

protected lemma all_eq' (hf: ∀ x y, pred (x ++ y) = (pred x || pred y)): (l₁.all pred || l₂.all pred) = (l₁.product l₂).all (pred ∘ (fun (x, y) => x ++ y)) := by
  simp only [List.all_eq, ←Bool.decide_or]
  congr 1
  apply propext
  constructor
  · rintro (h|h) ⟨x, y⟩ hxy
    all_goals
      have ⟨hx, hy⟩ := (List.pair_mem_product.mp hxy)
      have := h _ (by assumption)
      rw [Function.comp_apply, hf, this]
      simp only [Bool.true_or, Bool.or_true]
  · intro h
    apply Classical.or_iff_not_imp_left.mpr
    push_neg
    intro ⟨x, hx₁, hx₂⟩ y hy
    have := h (x, y) (List.pair_mem_product.mpr ⟨hx₁, hy⟩)
    simp only [Function.comp_apply, hf x y, Bool.or_eq_true] at this
    exact this.resolve_left hx₂

variable {l: List α} {f: α → β} {g: β → Prop} {h: α → Prop}

protected lemma exists_of_mem_map': (∃ y ∈ l.map f, g y) ↔ (∃ x ∈ l, g (f x)) := by
  simp only [List.mem_map, exists_exists_and_eq_and]

protected lemma forall_of_mem_map': (∀ y ∈ l.map f, g y) ↔ (∀ x ∈ l, g (f x)) := by
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

variable {l: List (Subtype h)} {pred: α → Prop}

protected lemma exists_mem_unattach: (∃ x ∈ l.unattach, pred x) ↔ (∃ x ∈ l, pred x) := by
  simp only [List.mem_unattach, Subtype.exists, exists_and_right]

protected lemma forall_mem_unattach: (∀ x ∈ l.unattach, pred x) ↔ (∀ x ∈ l, pred x) := by
  simp only [List.mem_unattach, forall_exists_index, Subtype.forall]

end List

section
variable {l: List (List (Prop' A))}
lemma truth_disj_map_conj: truth t (disj (l.map conj)) = decide (∃ c ∈ l, ∀ p ∈ c, truth t p = Bool.true) := by
  rw [truth_disj, List.any_map, List.any_eq]
  simp only [Function.comp_apply, truth_conj, List.all_eq_true]

lemma truth_conj_map_disj: truth t (conj (l.map disj)) = decide (∀ c ∈ l, ∃ p ∈ c, truth t p = Bool.true) := by
  rw [truth_conj, List.all_map, List.all_eq]
  simp only [Function.comp_apply, truth_disj, List.any_eq_true]
end

lemma truth_disjNF'_eq: truth t (disjNF' p) = decide (∃ c ∈ disjNF p, ∀ l ∈ c, truth t l) := by
  simp only [disjNF', truth_disj_map_conj, List.exists_of_mem_map', List.forall_mem_unattach]

lemma truth_conjNF'_eq: truth t (conjNF' p) = decide (∀ d ∈ conjNF p, ∃ l ∈ d, truth t l) := by
  simp only [conjNF', truth_conj_map_disj, List.forall_of_mem_map', List.exists_mem_unattach]

mutual

lemma truth_eq_disjNF' {t: A → Bool}: ∀ {p: Prop' A}, truth t p = truth t (disjNF' p)
| .true | .false | .atom _ => rfl
| .or q r => by
  rw [disjNF', disjNF, List.map_append, List.map_append, truth_disj_append, truth]
  congr 1
  all_goals
    rw [←truth_disj, ←disjNF']
    exact truth_eq_disjNF'
| .and q r => by
  have hq := truth_eq_disjNF' (t := t) (p := q)
  have hr := truth_eq_disjNF' (t := t) (p := r)
  rw [truth, hq, hr]
  simp only [truth_disj, disjNF', List.map_map, List.any_map]
  apply List.any_eq'
  simp only [Function.comp_apply, List.unattach_append, truth_conj, List.all_append, implies_true]
| .not q => by
  rw [truth_disjNF'_eq, disjNF]
  simp only [List.exists_of_mem_map', List.forall_of_mem_map',
    ←Literal.truth_not]
  have: (∃ d ∈ q.conjNF, ∀ p ∈ d, truth t (not p) = Bool.true) ↔ ¬(∀ d ∈ q.conjNF, ∃ p ∈ d, truth t p = Bool.true) := by
    push_neg
    simp only [truth, Bool.not_eq_true', Bool.not_eq_true]
  simp only [this, decide_not]
  rw [truth]
  congr 1
  rw [truth_eq_conjNF']
  exact truth_conjNF'_eq

lemma truth_eq_conjNF' {t: A → Bool}: ∀ {p: Prop' A}, truth t p = truth t (conjNF' p)
| .true | .false | .atom _ => rfl
| .and q r => by
  rw [conjNF', conjNF, List.map_append, List.map_append, truth_conj_append, truth]
  congr 1
  all_goals
    rw [←truth_conj, ←conjNF']
    exact truth_eq_conjNF'
| .or q r => by
  have hq := truth_eq_conjNF' (t := t) (p := q)
  have hr := truth_eq_conjNF' (t := t) (p := r)
  rw [truth, hq, hr]
  simp only [truth_conj, conjNF', List.map_map, List.all_map]
  apply List.all_eq'
  simp only [Function.comp_apply, List.unattach_append, truth_disj, List.any_append, implies_true]
| .not q => by
  rw [truth_conjNF'_eq, conjNF]
  simp only [List.exists_of_mem_map', List.forall_of_mem_map',
    ←Literal.truth_not]
  have: (∀ c ∈ q.disjNF, ∃ p ∈ c, truth t (not p) = Bool.true) ↔ ¬(∃ c ∈ q.disjNF, ∀ p ∈ c, truth t p = Bool.true) := by
    push_neg
    simp only [truth, Bool.not_eq_true', Bool.not_eq_true]
  simp only [this, decide_not]
  rw [truth]
  congr 1
  rw [truth_eq_disjNF']
  exact truth_disjNF'_eq

end

lemma equivalent_disjNF': equivalent p (disjNF' p) :=
  equivalent_iff.mpr fun _ => truth_eq_disjNF'

lemma equivalent_conjNF': equivalent p (conjNF' p) :=
  equivalent_iff.mpr fun _ => truth_eq_conjNF'


end Prop'
