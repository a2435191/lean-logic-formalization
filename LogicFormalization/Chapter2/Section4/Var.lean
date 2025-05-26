import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

class HasVar.{u} where
  Var: Type u
  [emb: Function.Embedding ℕ Var]
  [decidable: DecidableEq Var]

export HasVar (Var)

variable [HasVar]

def var (n: ℕ) : Var :=
  HasVar.emb n

lemma var_inj: ∀ {m n}, var m = var n → m = n :=
  @HasVar.emb.inj'

instance [HasVar] : DecidableEq Var :=
  HasVar.decidable

abbrev v₀ := var 0
abbrev v₁ := var 1
abbrev v₂ := var 2
abbrev v₃ := var 3

abbrev x := var 100
abbrev y := var 101
abbrev z := var 102

namespace HasVar

noncomputable scoped instance (priority := low) instReal : HasVar where
  Var := ℝ
  emb := ⟨(↑), CharZero.cast_injective⟩

scoped instance (priority := high) instNat : HasVar where
  Var := ℕ
  emb := ⟨id, Function.injective_id⟩
