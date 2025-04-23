universe u

class Arity (F: Sort u) where
  arity: F → Nat

def arity {F: Sort u} [inst: Arity F] :=
  inst.arity
