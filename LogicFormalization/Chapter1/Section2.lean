import Mathlib.Data.Set.Basic

set_option autoImplicit true

/-! We keep the usual definitions of `Set`, functions, cardinality, products, etc. from Mathlib.
    We also use maps for families/sequences.  -/

open Classical in
theorem cantors_theorem {A: Type u} {S: A → Set A}: ¬∃ a', {a: A | a ∉ S a} = S a' :=
  fun ⟨b, hb⟩ =>
    if hb': b ∈ S b then
      absurd hb' (show b ∈ {a | a ∉ S a} from hb.symm ▸ hb')
    else
      absurd (hb.symm ▸ hb') hb'

@[reducible]
def Word (α: Type u) :=
  List α

namespace Word
/-! We use [0-n) as indices instead of [1-n].-/

abbrev empty (α: outParam (Type u)): Word α :=
  []

@[reducible]
def ε: Word α := empty α

open List

variable {a b c: Word α}

lemma length_concat: length (a ++ b) = length a + length b :=
  List.length_append ..

lemma concat_assoc: a ++ b ++ c = a ++ (b ++ c) :=
  List.append_assoc ..

lemma epsilon_concat {a: Word α}: ε ++ a = a :=
  rfl

lemma concat_epsilon {a: Word α}: a ++ ε = a :=
  List.append_nil _

lemma concat_cancel_left (h: a ++ b = a ++ c): b = c :=
  List.append_cancel_left h

lemma concat_cancel_right (h: a ++ c = b ++ c): a = b :=
  List.append_cancel_right h

end Word

-- TODO: posets, least, minimal, lower bound, Zorn's lemma
