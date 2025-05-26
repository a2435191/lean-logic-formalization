import LogicFormalization.Chapter2.Section3.Basic
import LogicFormalization.Chapter2.Section4.Var

universe u v w
variable [HasVar]

inductive Term (L: Language)
/-- `var v` represents the variable `v`, viewed as a word of length `1`-/
| var (v: Var)
/-- `app F ts` represents the concatenation `Ft₁...tₙ`-/
| app (F: L.ϝ) (ts: Fin (arity F) → Term L)

-- notation L "-term" => Term L

example : Term Language.Ring :=
  .app .mul fun | 0 => .app .add fun
                  | 0 => .var x
                  | 1 => .app .neg fun
                    | 0 => .var y
                | 1 => .var z

namespace Term
variable {L: Language}
def occursIn (v: Var) : Term L → Prop
| .var v' => v = v'
| .app _ ts => ∃ i, occursIn v (ts i)

lemma occursIn_app {v: Var} {F} {ts: Fin (arity F) → Term L}
    {i} (h: occursIn v (ts i)): occursIn v (.app F ts) :=
  ⟨i, h⟩

lemma occursIn_of_occursIn_app {v: Var} {F} {ts: Fin (arity F) → Term L}
    (h: occursIn v (.app F ts)): ∃ i, occursIn v (ts i) :=
  h

instance instDecidableOccursIn (v) (t: Term L) :
    Decidable (occursIn v t) :=
  match t with
  | .var v' => if h: v = v' then .isTrue h else .isFalse h
  | .app _F ts =>
    have: ∀ i, Decidable (occursIn v (ts i)) := fun i =>
      instDecidableOccursIn v (ts i)
    match h: Fin.find (fun i => occursIn v (ts i)) with
    | some _ =>
      have := (Fin.find_eq_some_iff.mp h).left
      .isTrue (occursIn_app this)
    | none =>
      have := Fin.find_eq_none_iff.mp h
      .isFalse fun ⟨i, hi⟩ => this i hi

structure AreVarsFor {m: ℕ} (x: Fin m → Var) (t: Term L) where
  inj': Function.Injective x
  occursIn': ∀ {v}, occursIn v t → v ∈ Set.range x

namespace AreVarsFor

variable {t: Term L} {m: ℕ}

def ofApp {F} {m} {ts: Fin (arity F) → Term L} {x: Fin m → Var} (hx: AreVarsFor x (app F ts)):
    (i: Fin (arity F)) → AreVarsFor x (ts i) :=
  fun _i => ⟨hx.inj', fun h => hx.occursIn' (occursIn_app h)⟩

def idx {t: Term L} {v: Var} {x: Fin m → Var}
    (hx: AreVarsFor x t) (h: occursIn v t): { i : Fin m // x i = v } :=
  match t with
  | .var _v' =>
    have hi := Fin.isSome_find_iff.mpr (hx.occursIn' h)
    let i := (Fin.find (fun i => x i = v)).get hi
    ⟨i, Fin.find_spec _ (Option.get_mem hi)⟩
  | .app _F ts =>
    match hj: Fin.find (fun j => occursIn v (ts j)) with
    | some j =>
      idx (.ofApp hx j) (Fin.find_eq_some_iff.mp hj).left
    | none => False.elim <|
      have := Fin.find_eq_none_iff.mp hj
      this h.choose h.choose_spec

-- TODO: delete?
-- @[coe]
-- def toEmbedding {m: ℕ} {x: Fin m → Var} {t: Term L}:
--     AreVarsFor x t → Function.Embedding (Fin m) Var
-- | { inj', .. } => ⟨x, inj'⟩

end AreVarsFor

variable {A: Type u} [Nonempty A]

def interp (t: Term L) (𝒜: Structure L A) {m} {x: Fin m → Var} (hx: AreVarsFor x t):
    (Fin m → A) → A :=
  match t with
  | .var _xᵢ => fun as => as (hx.idx rfl)
  | .app F ts => fun as => (F^𝒜) (fun i =>
    interp (ts i) 𝒜 (.ofApp hx i) as)

open Structure in
lemma interp_substructure {B: Type v} {A: Set B} [Nonempty A]
    {𝒜: Structure L A} {ℬ: Structure L B}
    (h: 𝒜 ⊆ ℬ) {t: Term L} {m} {x: Fin m → Var} (hx: AreVarsFor x t):
    ∀ (a: Fin m → A), interp t 𝒜 hx a = interp t ℬ hx (a ·) :=
  match t with
  | .var v => fun a => rfl
  | .app F ts => fun a => by
    simp only [interp, h.h₂]
    congr 1
    funext i
    apply interp_substructure
    exact substructure_is_substructure

def varFree : Term L → Prop
| .var _ => False
| .app _ ts => ∀ i, varFree (ts i)

@[simp]
lemma not_varFree_var {v: Var}: ¬varFree (.var v: Term L) :=
  False.elim

@[simp]
lemma varFree_of_varFree_app {F} {ts: Fin (arity F) → Term L}
    (h: varFree (.app F ts)): ∀ {i}, varFree (ts i) :=
  @h

lemma varFree_iff: ∀ {t: Term L}, varFree t ↔ ∀ v, ¬occursIn v t
| .var _ => by simp [varFree, occursIn]
| .app F ts => by
  simp only [varFree, occursIn, not_exists, varFree_iff]
  apply forall_comm

def AreVarsFor.empty {t: Term L} (ht: varFree t): AreVarsFor Fin.elim0 t where
  inj' := Function.injective_of_subsingleton _
  occursIn' := by simp [varFree_iff.mp ht _]

def interpConst (t: Term L) (ht: varFree t) (𝒜: Structure L A): A :=
  interp t 𝒜 (.empty ht) Fin.elim0

def interpConst.spec (t: Term L) (ht: varFree t) (𝒜: Structure L A): A :=
  match t with
  | .var _ => False.elim ht
  | .app F ts =>
    (F^𝒜) (fun i => spec (t := ts i) (ht i) 𝒜)

lemma interpConst_eq_spec {t: Term L} (ht: varFree t) {𝒜: Structure L A} :
    interpConst t ht 𝒜 = interpConst.spec t ht 𝒜 :=
  match t with
  | .var _ => rfl
  | .app F ts => by
    unfold interpConst interpConst.spec interp
    simp only [←interpConst_eq_spec]
    rfl

/-- `replace t τ x` is `t(τ₁/x₁, ..., τₙ/xₙ)`. Note that `x` must be injective. -/
def replace (t: Term L) {m} (τ: Fin m → Term L)
    (x: Fin m ↪ Var): Term L :=
  match t with
  | .var v =>
    match Fin.find (fun j => x j = v) with
    | none => .var v
    | some j => τ j
  | .app F ts => .app F (fun i => replace (ts i) τ x)

/-- Lemma 2.4.1 -/
theorem replace_varFree {t: Term L} {m} {τ: Fin m → Term L}
    {x: Fin m → Var} {hx: AreVarsFor x t} (h: ∀ i, varFree (τ i)):
    varFree (replace t τ ⟨x, hx.inj'⟩) :=
  -- TODO: clean up lol, ideally both cases to term mode
  match t with
  | .var v => by
    unfold replace
    have := hx.2 rfl
    simp only [Set.mem_range] at this
    have := Fin.isSome_find_iff.mpr this
    have ⟨j, hj⟩ := Option.isSome_iff_exists.mp this
    simp only [Function.Embedding.coeFn_mk, hj]
    apply h
  | .app F ts => by
    unfold replace varFree
    intro i
    dsimp
    apply replace_varFree
    · apply AreVarsFor.ofApp hx
    · assumption

-- TODO: generators, (maybe) notation
