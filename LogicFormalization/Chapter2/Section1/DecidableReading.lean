import LogicFormalization.Chapter2.Section1.Admissibility

namespace Word
namespace Admissible

universe u
variable {F: Type u} [Arity F] {w: Word F}

/-- This is for the extra decidable code not found in the book. -/
structure Reading (F: Type u) where
  f: F
  ts: List (Reading F)

namespace Reading

-- instance [ToString F] : ToString (Reading F) where
--   toString r := go r.f r.ts
-- where go f
--   | [] => toString f
--   | ts =>
--     let tsStrings := ts.attach.map fun ⟨⟨f', ts'⟩, _⟩ => go f' ts'
--     s!"({f}{String.join tsStrings})"
-- decreasing_by calc sizeOf ts'
--   _ < sizeOf (mk f' ts') := by decreasing_trivial
--   _ < sizeOf ts := by decreasing_trivial

def toWord: Reading F → Word F
| { f, ts } => f :: ts.attach.flatMap fun ⟨r, _⟩ => toWord r

/-- Reads a word and recursively splits it into parts if it's admissible, otherwise `none`. -/
def read [Arity F]: Word F → Option (Reading F)
| [] => none
| f :: w =>
  match go (arity f) w with
  | none => none
  | some ⟨ts, [], _⟩ => some { f, ts }
  | some ⟨_, _ :: _, _⟩ => none -- Here, we still have some characters
                                -- left over at the top-level
where go count w: Option (List (Reading F) × (remaining: Word F)
                          ×' remaining.length ≤ w.length) :=
  match count with
  | 0 => some ⟨[], w, Nat.le_refl _⟩
  | k + 1 => match w with
    | [] => none -- Nothing we can do if we run out of characters
    | f' :: v => do
      -- Read off the rest of the first admissible word, which we know
      -- starts with `f'`. `f' :: restOfWordForF` is the same as `t₁` in
      -- the textbook.
      let ⟨restOfWordForF, remaining, hle₁⟩ ← go (arity f') v
      let t₁ := mk f' restOfWordForF

      -- That used up some characters. We have `remaining` left, and
      -- we backtrack to the context of our caller's `f`. Now we
      -- read the `k`-many words `t₂`, ..., `tₙ`.
      let ⟨tᵢs, remaining', hle₂⟩ ← go k remaining

      -- We return `t₁, ..., tₙ` and report any characters we haven't used.
      return ⟨t₁ :: tᵢs, remaining', le_trans hle₂ (Nat.le_succ_of_le hle₁)⟩
termination_by w.length
decreasing_by (
  · decreasing_trivial
  · exact Nat.lt_add_one_of_le hle₁)

theorem isSome_of_read_admissible: Admissible w → (read w).isSome := by
  sorry

theorem admissible_of_isSome_read: (read w).isSome → Admissible w := by
  sorry

-- TODO: theorem that the w, ts from readability is the same as Reading.read

end Reading

-- Let's keep everything decidable!
instance [Arity F]: DecidablePred (Admissible (F := F)) :=
  fun w =>
    if h: (Reading.read w).isSome then
      .isTrue (Reading.admissible_of_isSome_read h)
    else
      .isFalse (h ∘ Reading.isSome_of_read_admissible)
