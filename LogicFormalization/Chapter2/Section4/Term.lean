import LogicFormalization.Chapter2.Section3.Basic
import LogicFormalization.Chapter2.Section4.Var

universe u v w
variable [HasVar]

inductive Term (L: Language)
/-- `var v` represents the variable `v`, viewed as a word of length `1`-/
| var (v: Var)
/-- `app F ts` represents the concatenation `Ft₁...tₙ`-/
| app (F: L.ϝ) (ts: Fin (arity F) → Term L)


example : Term Language.Ring :=
  .app .mul fun | 0 => .app .add fun
                  | 0 => .var x
                  | 1 => .app .neg fun
                    | 0 => .var y
                | 1 => .var z

namespace Term

variable {L: Language}

/-- Predicate for a variable occurring in a term. -/
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

/- N.B.: Here, we use an injective mapping from `Fin m` instead of a `Finset Var` so
that we can easily talk about the index of a variable (see `idx`),
which is used in `interp`. -/

/-- `AreVarsFor x t` means that `t = t(x₁, ..., xₘ)`, i.e. the `xᵢ` are
unique and contain (possibly not strictly) all the variables in `t`. -/
structure AreVarsFor {m: ℕ} (x: Fin m → Var) (t: Term L) where
  inj': Function.Injective x
  occursIn': ∀ {v}, occursIn v t → v ∈ Set.range x

namespace AreVarsFor

variable {t: Term L} {m: ℕ}

/-- If all the variables in a function application are in `x`, then
then the variables in each subterm remain in `x`. -/
@[simp]
lemma ofApp {F} {m} {ts: Fin (arity F) → Term L} {x: Fin m → Var} (hx: AreVarsFor x (app F ts)):
    (i: Fin (arity F)) → AreVarsFor x (ts i) :=
  fun _i => ⟨hx.inj', fun h => hx.occursIn' (occursIn_app h)⟩

/-- The (unique) `index` of a variable `xᵢ` in a set `x₁, ..., xₘ` is just `i`. -/
def index {t: Term L} {v: Var} {x: Fin m → Var}
    (hx: AreVarsFor x t) (h: occursIn v t): { i : Fin m // x i = v } :=
  match t with
  | .var _v' =>
    have hi := Fin.isSome_find_iff.mpr (hx.occursIn' h)
    let i := (Fin.find (fun i => x i = v)).get hi
    ⟨i, Fin.find_spec _ (Option.get_mem hi)⟩
  | .app _F ts =>
    match hj: Fin.find (fun j => occursIn v (ts j)) with
    | some j =>
      index (.ofApp hx j) (Fin.find_eq_some_iff.mp hj).left
    | none => False.elim <|
      have := Fin.find_eq_none_iff.mp hj
      this h.choose h.choose_spec

end AreVarsFor

variable {A: Type u} [Nonempty A]

/-- The interpretation `t^𝒜` of a term `t` with variables `x₁, ..., xₘ`
(which may not actually appear in `t`) is a function from `A^m` to `A`. -/
def interp (t: Term L) (𝒜: Structure L A) {m} {x: Fin m → Var} (hx: AreVarsFor x t):
    (Fin m → A) → A :=
  match t with
  | .var _xᵢ => fun as => as (hx.index rfl)
  | .app F ts => fun as => (F^𝒜) (fun i =>
    interp (ts i) 𝒜 (.ofApp hx i) as)

open Structure in
/-- If `𝒜 ⊆ ℬ` are `L`-structures and `t` is an `L`-term with variables `x₁, ..., xₘ`,
then for all `a ∈ A^m`, `t^𝒜(a) = t^ℬ(a)`. -/
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

/-- "A term is said to be *variable-free* if no variables occur in it." -/
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

@[simp]
lemma varFree_iff: ∀ {t: Term L}, varFree t ↔ ∀ v, ¬occursIn v t
| .var _ => by simp [varFree, occursIn]
| .app F ts => by
  simp only [varFree, occursIn, not_exists, varFree_iff]
  apply forall_comm

def AreVarsFor.empty {t: Term L} (ht: varFree t): AreVarsFor Fin.elim0 t where
  inj' := Function.injective_of_subsingleton _
  occursIn' := by simp [varFree_iff.mp ht _]

/-- If `t` is variable-free, we can identify its
interpretation with a single value. -/
def interpConst (t: Term L) (ht: varFree t) (𝒜: Structure L A): A :=
  interp t 𝒜 (.empty ht) Fin.elim0

/-- The more natural way of expressing `interpConst`.
See `interpConst_eq_spec`. -/
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
def replace (t: Term L) {m} (τ: Fin m → Term L) (x: Fin m ↪ Var): Term L :=
  match t with
  | .var v =>
    match Fin.find (fun j => x j = v) with
    | none => .var v
    | some j => τ j
  | .app F ts => .app F (fun i => replace (ts i) τ x)

/-- Lemma 2.4.1 -/
theorem replace_varFree {t: Term L} {m} {τ: Fin m → Term L}
    {x: Fin m → Var} (hx: AreVarsFor x t) (h: ∀ i, varFree (τ i)):
    varFree (replace t τ ⟨x, hx.inj'⟩) :=
  match t with
  | .var v =>
    match h': Fin.find fun j => x j = v with
    | none =>
      have ⟨i, hi⟩ := hx.occursIn' rfl
      have := Fin.find_eq_none_iff.mp h'
      absurd hi (this i)
    | some j => by
      simp only [replace, Function.Embedding.coeFn_mk, h']
      apply h
  | .app F ts =>
    fun i => replace_varFree (.ofApp hx i) h

-- TODO: generators, examples, (maybe) notation
