import LogicFormalization.Chapter1.Section2
import LogicFormalization.Chapter2.Section1.Arity
import Mathlib.Tactic.DefEqTransformations

universe u

/-!
Everything from the latter half of Chapter 2, Section 1 of the textbook lives here:
* The definition of admissible words;
* Lemmas 2.1.4-2.1.6 and Corollary 2.1.7 (TODO);
* Homework problem 5 (TODO, including definition).
-/

namespace Word
/-
We could define this as
```
structure Admissible (F: Type u) [Arity F] where
  f: F
  ts: Fin (arity f) → Admissible F
```
But that strays from the definition in the book. We use a definition
similar to the above for the decidable algorithm (see `DecidableReading.lean`).
-/
inductive Admissible {F: Type u} [Arity F]: Word F → Prop
| nullary (f: F) (hf: arity f = 0): Admissible [f]
| concat (f: F) (hf: arity f > 0) (ts: List (Word F))
         (hts₁: ∀ t ∈ ts, Admissible t) (hts₂: ts.length = arity f)
         : Admissible (f :: ts.flatten)

namespace Admissible

variable {F: Type u} {f: F} [Arity F] {t u v w: Word F} {ts us: List (Word F)}

lemma not_ε: Admissible w → w ≠ ε
| .nullary ..
| .concat .. => List.cons_ne_nil _ _

lemma ε_not: ¬Admissible (F := F) ε :=
  fun h => not_ε h rfl

/-- The only way to get an empty word from concatenating `Admissible`
words is the empty concatenation. -/
lemma ε_of_flatten_ε
  (h₁: ∀ t ∈ ts, Admissible t) (h₂: ts.flatten = ε)
: ts = ε :=
  match ts with
  | [] => rfl
  | t :: _ => by
    exfalso
    suffices t = ε from
      have ht: Admissible t := h₁ t (List.mem_cons_self ..)
      (this ▸ ε_not) ht
    rw [List.flatten_cons, List.append_eq_nil_iff] at h₂
    exact h₂.left

lemma readability (hw: Admissible w): ∃ (f: F) (ts: List (Word F)),
w = f :: ts.flatten ∧ (∀ t ∈ ts, Admissible t) ∧ ts.length = arity f :=
  match hw with
  | .nullary f hf => ⟨f, [], rfl, List.forall_mem_nil _, hf.symm⟩
  | .concat f _ ts hts₁ hts₂ => ⟨f, ts, rfl, hts₁, hts₂⟩

lemma nullary_of_singleton (h: Admissible [f]): arity f = 0 :=
  Admissible.recOn (motive := fun x hx => x = [f] → arity f = 0) h
    (fun x hx₁ hx₂ => List.head_eq_of_cons_eq hx₂ ▸ hx₁)
    (fun x hx₁ ts hts₁ hts₂ _ heq => by
      absurd (hts₂ ▸ hx₁)
      rw [not_lt, Nat.le_zero_eq, List.length_eq_zero_iff]
      apply ε_of_flatten_ε
      · assumption
      · exact List.tail_eq_of_cons_eq heq)
    rfl

section Lemma4

private lemma List.of_prefix_append_equal_lengths {α: Type u} {x y z w: List α}
: x ++ y <+: z ++ w → x.length = z.length → x = z ∧ y <+: w
| h₁, h₂ =>
  have ⟨s, t⟩ := h₁
  have ⟨g₁, g₂⟩ := List.append_inj (List.append_assoc .. ▸ t) h₂
  ⟨g₁, s, g₂⟩

/-- Lemma 2.1.4 -/
lemma of_flatten_append_prefix_of_flatten {ts us: List (Word F)} {w: Word F}
  (hts: ∀ t ∈ ts, Admissible t) (hus: ∀ u ∈ us, Admissible u)
  (htuw: ts.flatten ++ w = us.flatten)
: ts <+: us ∧ w = (us.drop ts.length).flatten := by
  match us, ts with
  | [], ts =>
    rw [List.flatten_nil, List.append_eq_nil_iff] at htuw
    rw [ε_of_flatten_ε hts htuw.left, htuw.right]
    exact ⟨List.prefix_rfl, rfl⟩
  | u₁ :: us', [] =>
    simp at htuw ⊢
    assumption
  | u₁ :: us', t₁ :: ts' =>
    replace hts := List.forall_mem_cons.mp hts
    replace hus := List.forall_mem_cons.mp hus
    have ⟨h, as, hfas, has₁, has₂⟩ := readability hts.left
    have ⟨h', bs, hfbs, hbs₁, hbs₂⟩ := readability hus.left
    have: h = h' := by
      simp [hfas, hfbs] at htuw
      exact htuw.left
    subst this

    simp only [hfas, hfbs, List.flatten_cons, List.cons_append,
               List.cons_inj_right, ←List.flatten_append] at htuw
    have hlength_as_bs: as.length = bs.length := hbs₂.symm ▸ has₂
    have ⟨hprefixes, hw⟩ := of_flatten_append_prefix_of_flatten -- recurse
      (List.forall_mem_append.mpr ⟨has₁, hts.right⟩)
      (List.forall_mem_append.mpr ⟨hbs₁, hus.right⟩)
      htuw
    rw [List.length_append, hlength_as_bs, List.drop_append] at hw

    replace ⟨heq_as_bs, hprefixes⟩ :=
      List.of_prefix_append_equal_lengths hprefixes hlength_as_bs
    simp only [hfas, hfbs, List.cons_prefix_cons, List.length_cons, List.drop_succ_cons]
    exact ⟨⟨heq_as_bs ▸ rfl, hprefixes⟩, hw⟩
termination_by us.flatten.length

private lemma List.forall_drop {α: Type u} {l: List α} {p: α → Prop} (n: ℕ) (h: ∀ a ∈ l, p a)
: ∀ a ∈ l.drop n, p a :=
  fun a ha => h a (List.mem_of_mem_drop ha)

-- "two immediate consequences"

-- first consequence
lemma flatten_inj (hts: ∀ t ∈ ts, Admissible t) (hus: ∀ u ∈ us, Admissible u)
(heq: ts.flatten = us.flatten): ts = us :=
  have ⟨h₁, h₂⟩ := of_flatten_append_prefix_of_flatten
    hts hus ((List.append_nil ts.flatten).symm ▸ heq)
  have := ε_of_flatten_ε (List.forall_drop ts.length hus) h₂.symm
  List.IsPrefix.eq_of_length_le h₁ (List.drop_eq_nil_iff.mp this)

-- second consequence
lemma append_inj (ht: Admissible t) (hu: Admissible u) (heq: t ++ w = u): t = u ∧ w = ε :=
  have ⟨_, h⟩ := of_flatten_append_prefix_of_flatten (w := w)
    (List.forall_mem_singleton.mpr ht)
    (List.forall_mem_singleton.mpr hu)
    (List.flatten_singleton.symm ▸ List.flatten_singleton.symm ▸ heq)

  have: w = (List.drop 0 []).flatten :=
    List.drop_succ_cons ▸ List.length_singleton ▸ h
  have: w = [] := this
  ⟨List.append_nil t ▸ this ▸ heq, this⟩

/-- Restating of `append_inj` -/
lemma eq_of_prefix (ht: Admissible t) (hu: Admissible u) (htu: t <+: u): t = u :=
  have ⟨_, hw⟩ := htu
  (append_inj ht hu hw).left

lemma eq_prefix_of_eq (ht: Admissible t) (hv: Admissible v) (htuvw: t ++ u = v ++ w): t = v :=
  (List.append_eq_append_iff.mp htuvw).elim
    (fun ⟨_, h₁, _⟩ => (append_inj ht hv h₁.symm).left)
    (fun ⟨_, h₁, _⟩ => (append_inj hv ht h₁.symm).left.symm)

end Lemma4

section Lemma5

/-- Lemma 2.1.5 -/
lemma unique_readability (hw: Admissible w)
: ∃! fts: F × List (Word F), w = fts.1 :: fts.2.flatten ∧ (∀ t ∈ fts.2, Admissible t) ∧ fts.2.length = arity fts.1 := by
  have ⟨f, ts, h₁, h₂, h₃⟩ := readability hw
  refine ⟨(f, ts), ⟨h₁, h₂, h₃⟩, ?_⟩
  intro (f', ts') ⟨h₁', h₂', h₃'⟩
  dsimp at h₁' h₂' h₃'
  have ⟨hf, this⟩ := List.cons.inj (h₁' ▸ h₁)
  have hts := flatten_inj h₂' h₂ this
  rw [hf, hts]

end Lemma5

end Admissible

/-- `v` occurs in `w` at starting position `i` -/
def OccursIn {F: Type u} (v w: Word F) (i: Fin w.length) :=
  ∃ (w₁ w₂: Word F), w = w₁ ++ v ++ w₂ ∧ w₁.length = i

/-- replace `v` in `w` at starting position `i` by `v'`-/
noncomputable def replaceIn {F: Type u} (v w: Word F) (i: Fin w.length) (h: OccursIn v w i) (v': Word F): Word F :=
  let w₁ := h.choose
  let w₂ := h.choose_spec.choose
  w₁ ++ v' ++ w₂

namespace OccursIn

variable {F: Type u} {v w w₁ w₂: Word F} {i: Fin w.length} {f: F}

lemma unique_prefix_and_suffix (h₁: w = w₁ ++ v ++ w₂) (h₂: w₁.length = i)
: w₁ = w.take i ∧ w₂ = w.drop (i + v.length) := by
  rw [←h₂, h₁, List.append_assoc, List.take_left,
      ←List.length_append, ←List.append_assoc, List.drop_left]
  trivial

/-- translate `OccursIn` to a more natural statement w.r.t. the `List` API -/
@[simp]
lemma iff: OccursIn v w i ↔ v <+: w.drop i := by
  constructor
  · intro ⟨w₁, w₂, h₁, h₂⟩
    use w₂
    simp only [h₁, ←h₂, List.append_assoc, List.drop_left]
  · intro ⟨w₂, h⟩
    use w.take i, w₂
    constructor
    · rw [List.append_assoc, h, List.take_append_drop]
    · rw [List.length_take_of_le (Nat.le_of_lt i.isLt)]

lemma refl (hw: 0 < w.length): OccursIn w w ⟨0, hw⟩ :=
  ⟨ε, ε, (List.append_nil _).symm, rfl⟩

lemma prefix_of_zero {hw: 0 < w.length} (h: OccursIn v w ⟨0, hw⟩): v <+: w :=
  iff.mp h

lemma to_succ (hi: i < w.length) (h: OccursIn v w ⟨i, hi⟩)
: OccursIn v (f :: w) ⟨i + 1, Nat.add_lt_add_right hi 1⟩ :=
  iff.mpr <| (congrArg _ List.drop_succ_cons).mpr (iff.mp h)

section Lemma6

open Admissible

structure J (ts: List (Word F)) (k: Fin ts.flatten.length) where
  j: Fin ts.length
  lt: k < (ts.take (j + 1)).flatten.length
  min: ∀ j': Fin ts.length, k < (ts.take (j' + 1)).flatten.length → j' ≥ j

namespace J

/-- Find `j`, the smallest `Fin (ts.length)` s.t.
`k < length ts[0] + ... + length ts[j]`. Then `k` indexed into `flatten ts`
will point to somewhere inside `ts[j]`. -/
def compute (ts: List (Word F)) (k: Fin ts.flatten.length): J ts k :=
  let js := List.range ts.length
    |>.filter fun j => k < (ts.take (j + 1)).flatten.length

  have hlen: ts.length > 0 := List.length_pos_iff.mpr fun hn =>
    Fin.elim0 (k.cast (hn ▸ rfl))
  have hLastMem: ts.length - 1 ∈ js := by
    apply List.mem_filter.mpr
    split_ands
    · apply List.mem_range.mpr
      exact Nat.sub_one_lt_of_lt hlen
    · rw [Nat.sub_one_add_one_eq_of_pos hlen, decide_eq_true]
      rw [List.take_length]
      exact k.isLt

  have isSome := (List.isSome_min?_of_mem hLastMem)
  let j := js.min?.get isSome
  have ⟨hjMem, hjGe⟩ := List.min?_eq_some_iff'.mp (Option.some_get isSome).symm
  have ⟨hjMem', hj⟩ := List.mem_filter.mp hjMem
  ⟨⟨j, List.mem_range.mp hjMem'⟩, decide_eq_true_eq.mp hj,
    fun j' hj' =>
      have hj'Mem: j'.val ∈ js := List.mem_filter.mpr ⟨
        List.mem_range.mpr j'.isLt, decide_eq_true_eq.mpr hj'⟩
      hjGe _ hj'Mem⟩

variable {ts: List (Word F)} {k: Fin ts.flatten.length}

/-- How far `k` reaches into `t[j]` -/
def offset (j: J ts k): ℕ :=
  k - (ts.take j.j).flatten.length

variable {j: J ts k}

lemma ge: k ≥ (ts.take j.j).flatten.length :=
  match hj: j.j with
  | ⟨0, _⟩ => Nat.zero_le _
  | ⟨l + 1, hl⟩ => by
    apply Nat.ge_of_not_lt
    intro hn
    have := j.min ⟨l, Nat.lt_of_succ_lt hl⟩ hn
    conv at this => right; rw [hj]
    simp only [Fin.mk_le_mk, Nat.not_add_one_le_self] at this

lemma offset_lt: j.offset < ts[j.j].length :=
  Nat.sub_lt_left_of_lt_add j.ge <|
    calc k.val
      _ < (ts.take (j.j + 1)).flatten.length := j.lt
      _ = (ts.take j.j).flatten.length + ts[j.j].length := by
        rw [List.take_succ, List.getElem?_eq_getElem j.j.isLt, Option.toList_some]
        rw [List.flatten_append, List.length_append, List.flatten_singleton]
        rfl

lemma occurs_in (h: OccursIn v ts[j.j] ⟨j.offset, j.offset_lt⟩): OccursIn v ts.flatten k :=
  have ⟨v₁, v₂, h₁, h₂⟩ := h
  let w₁ := (ts.take j.j).flatten ++ v₁
  let w₂ := v₂ ++ (ts.drop (j.j + 1)).flatten
  have hts := calc ts.flatten
    _ = (ts.take j.j).flatten ++ ts[j.j] ++ (ts.drop (j.j + 1)).flatten := by
      rw [←List.flatten_singleton (l := ts[j.j])]
      simp only [←List.flatten_append]
      simp only [Fin.getElem_fin, List.take_append_getElem, List.take_append_drop]
    _ = w₁ ++ v ++ w₂ := by simp only [h₁, List.append_assoc, w₁, w₂]
  have hw₁ := by
    unfold w₁
    rw [List.length_append, h₂]
    apply Nat.add_sub_of_le
    apply J.ge
  ⟨w₁, w₂, hts, hw₁⟩

lemma occurs_in_succ (h: OccursIn v ts[j.j] ⟨j.offset, j.offset_lt⟩)
: OccursIn v (f :: ts.flatten) ⟨k + 1, Nat.add_one_lt_add_one_iff.mpr k.isLt⟩ :=
  to_succ k.isLt (j.occurs_in h)

end J

/-- See `unique_admissible_occurring_in` for uniqueness -/
lemma exists_admissible_occurring_in [Arity F] {w: Word F} (hw: Admissible w) (i: Fin w.length): ∃ v, Admissible v ∧ OccursIn v w i :=
  match hi: i with
  | ⟨0, h0⟩ => ⟨w, hw, refl h0⟩
  | ⟨k + 1, hk⟩ =>
    have ⟨f, ts, h₁, h₂, h₃⟩ := readability hw
    have hk': k < ts.flatten.length := Nat.add_one_lt_add_one_iff.mp
      (List.length_cons .. ▸ h₁ ▸ hk)
    let j := J.compute ts ⟨k, hk'⟩
    let tj := ts[j.j]
    have htj: Admissible tj := h₂ tj (List.mem_of_getElem rfl)
    let ⟨v, hv₁, hv₂⟩ := exists_admissible_occurring_in (w := tj) htj ⟨j.offset, j.offset_lt⟩
    ⟨v, hv₁, h₁ ▸ j.occurs_in_succ hv₂⟩
termination_by w.length
decreasing_by calc ts[j.j].length
  _ ≤ ts.flatten.length := List.Sublist.length_le <|
    List.sublist_flatten_of_mem <| List.mem_of_getElem rfl
  _ < (f :: ts.flatten).length := by simp only [List.length_cons, Nat.lt_add_one]
  _ = w.length := congrArg _ h₁.symm

/-- Lemma 2.1.6: `exists_admissible_occurring_in` is unique -/
lemma unique_admissible_occurring_in [Arity F] (hw: Admissible w) (i: Fin w.length): ∃! v: Word F, Admissible v ∧ OccursIn v w i := by
  have ⟨v, hv₁, hv₂⟩ := exists_admissible_occurring_in hw i
  refine ⟨v, ⟨hv₁, hv₂⟩, ?_⟩
  intro v' ⟨hv'₁, hv'₂⟩
  have ⟨x₁, x₂, h₁, h₂⟩ := hv₂
  have ⟨x'₁, x'₂, h'₁, h'₂⟩ := hv'₂
  rw [h₁, List.append_assoc, List.append_assoc] at h'₁
  have := List.append_inj_right h'₁ (h'₂.symm ▸ h₂)
  symm
  apply eq_prefix_of_eq (u := x₂) (w := x'₂)
  <;> assumption


end Lemma6

/-- Like `replaceIn`, but uses `unique_admissible_occurring_in` so only needs an index `i` -/
@[reducible]
noncomputable def replaceIn' [Arity F] {w: Word F} (hw: Admissible w) (i: Fin w.length) (v': Word F): Word F :=
  let ⟨v, ⟨_hv₁, hv₂⟩, _hv₃⟩ := Classical.indefiniteDescription _ (unique_admissible_occurring_in hw i)
  replaceIn v w i hv₂ v'

section Corollary7

/-- Corollary 2.1.7 -/
lemma admissible_replaceIn [Arity F] {w: Word F} (hw: Admissible w) {i: Fin w.length} {v': Word F} (hv': Admissible v'): Admissible (replaceIn' hw i v') :=
  sorry

end Corollary7

end OccursIn
end Word
