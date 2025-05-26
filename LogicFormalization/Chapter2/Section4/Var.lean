import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

class HasVar.{u} where
  Var: Type u
  [inst: Function.Embedding ℕ Var]

export HasVar (Var)

variable [HasVar]

def var (n: ℕ) : Var :=
  HasVar.inst n

lemma var_inj: ∀ {m n}, var m = var n → m = n :=
  @HasVar.inst.inj'

abbrev v₀ := var 0
abbrev v₁ := var 1
abbrev v₂ := var 2
abbrev v₃ := var 3

abbrev x := var 100
abbrev y := var 101
abbrev z := var 102

namespace HasVar

scoped instance (priority := low) instReal : HasVar where
  Var := ℝ
  inst := ⟨(↑), CharZero.cast_injective⟩

scoped instance (priority := high) instNat : HasVar where
  Var := ℕ
  inst := ⟨id, Function.injective_id⟩
