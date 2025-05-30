import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

universe u

class Var (V: Type u) where
  var : ℕ ↪ V

variable {V: Type u} [Var V]

export Var (var)

lemma var_inj: ∀ {m n: ℕ}, var (V := V) m = var n → m = n :=
  @var.inj'

abbrev v₀: V := var 0
abbrev v₁: V := var 1
abbrev v₂: V := var 2
abbrev v₃: V := var 3

abbrev x: V := var 100
abbrev y: V := var 101
abbrev z: V := var 102

instance : Var ℝ where
  var := ⟨(↑), CharZero.cast_injective⟩

instance : Var ℕ where
  var := ⟨id, Function.injective_id⟩
