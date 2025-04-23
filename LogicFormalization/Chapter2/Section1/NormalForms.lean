import LogicFormalization.Chapter2.Section1.Prop'Lemmas

namespace Prop'

universe u v
variable {A: Type u} {p: Prop' A}

@[simp, reducible]
def isLiteral: Prop' A → Prop
| .atom _ | .not (.atom _) => True
| _ => False

instance: DecidablePred (@isLiteral A) := by
  intro
  unfold isLiteral
  split <;> infer_instance

lemma isLiteral_iff: isLiteral p ↔ (∃ a, p = atom a) ∨ (∃ a, p = not (atom a)) := by
  cases p <;> try tauto
  · rename_i a
    cases a <;> simp [isLiteral]

def isLiteral.rec {motive: (p: Prop' A) → Sort v}
  (atom: ∀ a, motive (.atom a)) (not: ∀ a, motive (.not (.atom a)))
: ∀ a, isLiteral a → motive a := by
  rintro (_|_) ha
  case atom => apply atom
  case not =>
    rename_i a
    cases a <;> try contradiction
    apply not
  all_goals contradiction

mutual
/-- Disjunctive normal form -/
@[reducible]
def disjNF: Prop' A → List (List (Prop' A))
| .true => [[]]
| .false => []
| .atom a => [[.atom a]]
| .or p q => disjNF p ++ disjNF q
| .and p q => List.product (disjNF p) (disjNF q)|>.map fun (a, b) => a ++ b
| .not p => (conjNF p).map <| List.map fun
                                | .atom a => not (atom a)
                                | .not (.atom a) => atom a
                                | _ => true -- unreachable

/-- Conjunctive normal form -/
@[reducible]
def conjNF: Prop' A → List (List (Prop' A))
| .true => []
| .false => [[]]
| .atom a => [[.atom a]]
| .or p q => List.product (conjNF p) (conjNF q)|>.map fun (a, b) => a ++ b
| .and p q => conjNF p ++ conjNF q
| .not p => (disjNF p).map <| List.map fun
                                | .atom a => not (atom a)
                                | .not (.atom a) => atom a
                                | _ => true -- unreachable
end

mutual
lemma disjNF_all_literals {p: Prop' A}: ∀ conj ∈ disjNF p, ∀ p' ∈ conj, isLiteral p' :=
  fun conj hconj p' hp' =>
    match p with
    | .true =>
      have: conj = [] := List.mem_singleton.mp hconj
      absurd (this ▸ hp') (List.not_mem_nil _)
    | .false => absurd hconj (List.not_mem_nil _)
    | .atom a =>
      have: conj = [atom a] := List.mem_singleton.mp hconj
      have: p' = atom a := List.mem_singleton.mp (this ▸ hp')
      this ▸ trivial
    | .or q r =>
      (List.mem_append.mp hconj).elim
        (disjNF_all_literals conj · p' hp')
        (disjNF_all_literals conj · p' hp')
    | .and q r => by
      simp only [disjNF, List.mem_map, Prod.exists, List.pair_mem_product, List.append_eq] at hconj
      have ⟨a, b, ⟨ha, hb⟩, hab⟩ := hconj
      exact (List.mem_append.mp (hab.symm ▸ hp')).elim
        (disjNF_all_literals a ha p')
        (disjNF_all_literals b hb p')
    | .not q => by
      have ⟨disj, hdisj₁, hdisj₂⟩ := List.mem_map.mp hconj
      have ⟨a', ha'₁, ha'₂⟩ := List.mem_map.mp (hdisj₂.symm ▸ hp')
      replace ha'₁ := conjNF_all_literals disj hdisj₁ a' ha'₁
      rw [←ha'₂]
      apply isLiteral.rec (a := a') <;> (try intro) <;> trivial

lemma conjNF_all_literals {p: Prop' A}: ∀ disj ∈ conjNF p, ∀ p' ∈ disj, isLiteral p' :=
  fun disj hdisj p' hp' =>
    match p with
    | .false =>
      have: disj = [] := List.mem_singleton.mp hdisj
      absurd (this ▸ hp') (List.not_mem_nil _)
    | .true => absurd hdisj (List.not_mem_nil _)
    | .atom a =>
      have: disj = [atom a] := List.mem_singleton.mp hdisj
      have: p' = atom a := List.mem_singleton.mp (this ▸ hp')
      this ▸ trivial
    | .and q r =>
      (List.mem_append.mp hdisj).elim
        (conjNF_all_literals disj · p' hp')
        (conjNF_all_literals disj · p' hp')
    | .or q r => by
      simp only [disjNF, List.mem_map, Prod.exists, List.pair_mem_product, List.append_eq] at hdisj
      have ⟨a, b, ⟨ha, hb⟩, hab⟩ := hdisj
      exact (List.mem_append.mp (hab.symm ▸ hp')).elim
        (conjNF_all_literals a ha p')
        (conjNF_all_literals b hb p')
    | .not q => by
      have ⟨conj, hconj₁, hconj₂⟩ := List.mem_map.mp hdisj
      have ⟨a', ha'₁, ha'₂⟩ := List.mem_map.mp (hconj₂.symm ▸ hp')
      replace ha'₁ := disjNF_all_literals conj hconj₁ a' ha'₁
      rw [←ha'₂]
      apply isLiteral.rec (a := a') <;> (try intro) <;> trivial
end

@[simp, reducible]
def disjNF' (p: Prop' A): Prop' A :=
  (disjNF p).map conj |> disj

@[simp, reducible]
def conjNF' (p: Prop' A): Prop' A :=
  (conjNF p).map (disj) |> conj


-- TODO: cleanup
mutual
lemma equivalent_of_disjNF' {p: Prop' A}: equivalent p (disjNF' p) :=
  equivalent_iff.mpr fun t =>
    match p with
    | .true | .false | .atom _ => rfl
    | .or q r => by
      rw [truth, truth_disj, List.map_append, List.any_append]
      congr 1
      all_goals
        rw [←truth_disj, ←disjNF', equivalent_iff.mp]
        exact equivalent_of_disjNF'
    | .and q r => by -- TODO: golf this
      have hq := equivalent_iff.mp (@equivalent_of_disjNF' q) t
      have hr := equivalent_iff.mp (@equivalent_of_disjNF' r) t
      rw [truth, hq, hr, ←truth]
      conv => rhs; rw [disjNF', disjNF, List.map_map, truth_disj, List.any_map]
      have: truth t ∘ conj ∘ (fun (a, b) => a ++ b) = fun (ps, qs) => (ps.all (truth t) && qs.all (truth t)) :=
        funext fun _ => truth_conj_append

      simp only [this]
      simp only [ ←truth_conj, ←truth.eq_6]
      simp only [truth]

      sorry
    | .not q => by
      rw [truth, disjNF', truth_disj]
      sorry

lemma equivalent_of_conjNF' {p: Prop' A}: equivalent p (conjNF' p) :=
  sorry

end


end Prop'
