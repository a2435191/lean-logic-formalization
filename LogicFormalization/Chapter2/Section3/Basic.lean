import LogicFormalization.Chapter2.Section1.Arity
import Mathlib.Data.Set.Defs
import Mathlib.Logic.Basic

universe u v

inductive Language (ρ: Type u) (ϝ: Type v) [Arity ρ] [Arity ϝ]
| relation: ρ → Language ρ ϝ
| function: ρ → Language ρ ϝ

namespace Language

-- TODO: examples

end Language

universe w

structure Structure (ρ: Type u) (ϝ: Type v) [Arity ρ] [Arity ϝ] where
  A: Type w
  nonempty: Nonempty A
  interpRel: (R: ρ) → Set (Fin (arity R) → A)
  interpFun: (F: ϝ) → (Fin (arity F) → A) → A

namespace Structure
variable {ρ: Type u} {ϝ: Type v} [Arity ρ] [Arity ϝ]

def interpConst (𝒜: Structure ρ ϝ) {c: ϝ} (h: arity c = 0) :=
  𝒜.interpFun c fun f => (h ▸ f).elim0
