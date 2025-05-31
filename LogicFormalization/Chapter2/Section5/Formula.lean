import LogicFormalization.Chapter2.Section4.Term

inductive Formula.Atomic (L: Language) (V := ULift ℕ)
| true | false
| rel (R: L.ρ) (ts: Fin (arity R) → Term L V)
| eq: Term L V → Term L V → Formula.Atomic L V

inductive Formula (L: Language) (V := ULift ℕ)
| atomic: Formula.Atomic L V → Formula L V
| not: Formula L V → Formula L V
| or:  Formula L V → Formula L V → Formula L V
| and: Formula L V → Formula L V → Formula L V
| exists: V → Formula L V → Formula L V
| forall: V → Formula L V → Formula L V

namespace Formula

universe u
variable {V: Type u} {L: Language}

instance : Coe (Formula.Atomic L V) (Formula L V) where
  coe := atomic

/-! We take exercise 1 as the *definition* of subformulas. -/

def subformulas : Formula L V → Set (Formula L V)
| φ@(.atomic _) => { φ }
| .not φ => { .not φ } ∪ subformulas φ
| .or  φ ψ => { .or  φ ψ } ∪ subformulas φ ∪ subformulas ψ
| .and φ ψ => { .and φ ψ } ∪ subformulas φ ∪ subformulas ψ
| .exists x φ => { .exists x φ } ∪ subformulas φ
| .forall x φ => { .forall x φ } ∪ subformulas φ

def occursFreeIn (v: V) : Formula L V → Prop :=
  go ∅
where go (context: Set V) : Formula L V → Prop
| .atomic .true | .atomic .false => False
| .atomic (.eq t₁ t₂) =>
  (Term.occursIn v t₁ ∨ Term.occursIn v t₂) ∧ v ∉ context
| .atomic (.rel _ ts) =>
  ∃ i, Term.occursIn v (ts i) ∧ v ∉ context
| .and φ ψ | .or φ ψ => go context φ ∨ go context ψ
| .not φ => go context φ
| .forall x φ | .exists x φ => go (insert x context) φ

abbrev isSentence (φ: Formula L V) :=
  ∀ v, ¬Formula.occursFreeIn v φ

end Formula

@[reducible]
def Sentence (L: Language) (V := ULift ℕ) :=
  { φ : Formula L V // φ.isSentence }

namespace Formula

universe u
variable {V: Type u} {L: Language}

def AreVarsFor (x : Set V) (φ : Formula L V) :=
  ∀ v, occursFreeIn v φ → v ∈ x

def replace [DecidableEq V] (φ: Formula L V)
    (x: Set V) [DecidablePred (· ∈ x)] (t: x → Term L V): Formula L V :=
  match φ with
  | .atomic .true | .atomic .false => φ
  | .atomic (.rel R ts) => .atomic (.rel R fun i => (ts i).replace x t)
  | .atomic (.eq t₁ t₂) => .atomic (.eq (t₁.replace x t) (t₂.replace x t))
  | .and φ ψ => .and (replace φ x t) (replace ψ x t)
  | .or  φ ψ => .or  (replace φ x t) (replace ψ x t)
  | .not φ => .not (replace φ x t)
  | .forall v φ => .forall v (replace φ (x \ {v}) (fun ⟨y, hy⟩ => t ⟨y, hy.left⟩))
  | .exists v φ => .exists v (replace φ (x \ {v}) (fun ⟨y, hy⟩ => t ⟨y, hy.left⟩))

/-- Lemma 2.5.1 -/
lemma isSentence_of_replace [DecidableEq V] {φ: Formula L V}
    {x: Set V} [DecidablePred (· ∈ x)] {t: x → Term L V}
    (hφ: AreVarsFor x φ) (ht: ∀ x, (t x).varFree):
    isSentence (replace φ x t) := by
  intro v hn
  induction φ with
  | atomic a =>
    match a with
    | .true | .false => exact hn
    | .rel R ts =>
      unfold occursFreeIn occursFreeIn.go at hn
      simp [replace] at hn
      simp [AreVarsFor, occursFreeIn, occursFreeIn.go] at hφ
      sorry
    | .eq t₁ t₂ => sorry
  | not φ ih => sorry
  | or φ ψ ih => sorry
  | and φ ψ ih => sorry
  | «forall» v' φ ih => sorry
  | «exists» v' φ ih => sorry

end Formula

namespace Language

inductive OrName (ϝ C: Type*)
| base: ϝ → OrName ϝ C
| name: C → OrName ϝ C

instance {ϝ} {C} [Arity ϝ] : Arity (OrName ϝ C) where
  arity
  | .base f => arity f
  | .name _ => 0

@[reducible]
def withNames (L: Language) (C: Type*) : Language :=
  { ρ := L.ρ, ϝ := OrName L.ϝ C }

variable {L: Language} {C: Type*}

@[simp]
lemma ρ_withNames: (withNames L C).ρ = L.ρ :=
  rfl

@[simp]
lemma ϝ_withNames: (withNames L C).ϝ = OrName L.ϝ C :=
  rfl

@[simp]
lemma arity_OrName {ϝ: Type*} [Arity ϝ] {c: C}: arity (F := OrName ϝ C) (.name c) = 0 :=
  rfl

end Language

namespace Structure

def withNames {L: Language} {A: Type*} [Nonempty A] (𝒜: Structure L A) (C: Set A := .univ):
    Structure (L.withNames C) A where
  interpRel := 𝒜.interpRel
  interpFun
  | .base f => 𝒜.interpFun f
  | .name c => fun (_: Fin 0 → A) => c


end Structure
