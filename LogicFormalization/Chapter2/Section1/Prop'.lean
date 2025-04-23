import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Mathlib.Order.Notation
import Mathlib.Data.Set.Basic

universe u

inductive Prop' (A: Type u)
| atom: A → Prop' A
| true | false
| not: Prop' A → Prop' A
| or : Prop' A → Prop' A → Prop' A
| and: Prop' A → Prop' A → Prop' A

namespace Prop'

variable {A: Type u}

@[reducible]
def length: Prop' A → ℕ
| .atom _ | .true | .false => 1
| .not p => length p + 1
| .or p q | .and p q => length p + length q + 1

@[reducible]
def implies (p q: Prop' A) :=
  or (not p) q

@[reducible]
def iff (p q: Prop' A) :=
  and (implies p q) (implies q p)

def disj: List (Prop' A) → Prop' A
| [] => false
| p₁ :: ps => ps.foldl or p₁

def conj: List (Prop' A) → Prop' A
| [] => true
| p₁ :: ps => ps.foldl and p₁

/-- Truth assignment extending `t` to `Prop' A` -/
def truth (t: A → Bool): Prop' A → Bool
| .atom a => t a
| true => Bool.true
| false => Bool.false
| .not p => !(truth t p)
| .or p q => truth t p || truth t q
| .and p q => truth t p && truth t q

@[simp]
def tautology (p: Prop' A) :=
  ∀ t, truth t p

@[simp]
def satisfiable (p: Prop' A) :=
  ∃ t, truth t p

@[simp]
abbrev equivalent (p q: Prop' A) :=
  tautology (iff p q)

@[simp]
def models (t: A → Bool) (S: Set (Prop' A)) :=
  ∀ p ∈ S, truth t p

@[simp]
def tautologicalConsequence (S: Set (Prop' A)) (p: Prop' A) :=
  ∀ t: A → Bool, models t S → truth t p
