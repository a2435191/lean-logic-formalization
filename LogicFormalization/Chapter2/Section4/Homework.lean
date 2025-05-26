import LogicFormalization.Chapter2.Section4.Term

-- TODO: problems 1, 2, 3, 4, 5 (b) (c), rename and organize stuff (see previous `Homework.lean` files)

section Problem5

def 𝒩 : Structure .Rig ℕ where
  interpRel := nofun
  interpFun
  | .zero, _ => 0
  | .one,  _ => 1
  | .add,  a => a 0 + a 1
  | .mul,  a => a 0 * a 1

open Term
open HasVar


theorem a : ¬∃ (t: Term .Rig) (x: Var)
  (hx: AreVarsFor (m := 1) (fun | 0 => x) t),
    interp t 𝒩 hx (fun _ => 0) = 1 ∧ interp t 𝒩 hx (fun _ => 1) = 0 := by
  push_neg
  intro t x hx h₀ h₁
  sorry

end Problem5
