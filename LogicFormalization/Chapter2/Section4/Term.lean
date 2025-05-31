import LogicFormalization.Chapter2.Section3.Basic
import LogicFormalization.Chapter2.Section4.Var

universe u
variable {V: Type u}

inductive Term (L: Language) (V: Type u := ULift ℕ)
/-- `var v` represents the variable `v`, viewed as a word of length `1`-/
| var (v: V)
/-- `app F ts` represents the concatenation `Ft₁...tₙ`-/
| app (F: L.ϝ) (ts: Fin (arity F) → Term L V)


example : Term Language.Ring ℕ :=
  .app .mul fun | 0 => .app .add fun
                  | 0 => .var x
                  | 1 => .app .neg fun
                    | 0 => .var y
                | 1 => .var z

namespace Term

variable {L: Language}

/-- Predicate for a variable occurring in a term. -/
def occursIn (v: V) : Term L V → Prop
| .var v' => v = v'
| .app _ ts => ∃ i, occursIn v (ts i)

lemma occursIn_app {v: V} {F} {ts: Fin (arity F) → Term L V}
    {i} (h: occursIn v (ts i)): occursIn v (.app F ts) :=
  ⟨i, h⟩

lemma occursIn_of_occursIn_app {v: V} {F} {ts: Fin (arity F) → Term L V}
    (h: occursIn v (.app F ts)): ∃ i, occursIn v (ts i) :=
  h

instance instDecidableOccursIn [DecidableEq V] (v: V) (t: Term L V) :
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


/-- `areVarsFor x t` means that `t = t(x₁, ..., xₘ)`, i.e. the `xᵢ` contain
(possibly not strictly) all the variables in `t`. -/
@[reducible]
def areVarsFor (x: Set V) (t: Term L V) :=
  ∀ {v}, occursIn v t → v ∈ x


/-- If all the variables in a function application are in `x`, then
then the variables in each subterm remain in `x`. -/
@[simp]
lemma areVarsFor_ofApp {F} {ts: Fin (arity F) → Term L V} {x: Set V} (hx: areVarsFor x (app F ts)):
    (i: Fin (arity F)) → areVarsFor x (ts i) :=
  fun _i {_v} hv => hx (occursIn_app hv)


universe v
variable {A: Type v} [Nonempty A]

open Structure

/-- The interpretation `t^𝒜` of a term `t` with variables `x₁, ..., xₘ`
(which may not actually appear in `t`) is a function from `A^m` to `A`. We don't
care about the ordering of `x₁, ..., xₘ`, so `A^m` is just a mapping from the set of variables,
`x`, to `A`. -/
def interp [DecidableEq V] (t: Term L V) (𝒜: Structure L A) {x: Set V} (hx: areVarsFor x t):
    (x → A) → A :=
  match t with
  | .var v => fun as => as ⟨v, hx rfl⟩
  | .app F ts => fun as => (F^𝒜) fun i => interp (ts i) 𝒜 (areVarsFor_ofApp hx i) as

open Structure in
/-- If `𝒜 ⊆ ℬ` are `L`-structures and `t` is an `L`-term with variables `x₁, ..., xₘ`,
then for all `a ∈ A^m`, `t^𝒜(a) = t^ℬ(a)`. -/
lemma interp_substructure [DecidableEq V] {B: Type v} {A: Set B} [Nonempty A]
    {𝒜: Structure L A} {ℬ: Structure L B}
    (h: 𝒜 ⊆ ℬ) {t: Term L V} {x: Set V} (hx: areVarsFor x t):
    ∀ (a: x → A), interp t 𝒜 hx a = interp t ℬ hx (a ·) :=
  match t with
  | .var v => fun a => rfl
  | .app F ts => fun a => by
    simp only [interp, h.h₂]
    congr 1
    funext i
    apply interp_substructure
    · exact substructure_isSubstructure
    · apply areVarsFor_ofApp
      exact hx

/-- "A term is said to be *variable-free* if no variables occur in it." -/
def varFree : Term L V → Prop
| .var _ => False
| .app _ ts => ∀ i, varFree (ts i)

@[simp]
lemma not_varFree_var {v: V}: ¬varFree (.var v: Term L V) :=
  False.elim

@[simp]
lemma varFree_of_varFree_app {F} {ts: Fin (arity F) → Term L}
    (h: varFree (.app F ts)): ∀ {i}, varFree (ts i) :=
  @h

@[simp]
lemma varFree_iff: ∀ {t: Term L V}, varFree t ↔ ∀ v, ¬occursIn v t
| .var _ => by simp [varFree, occursIn]
| .app F ts => by
  simp only [varFree, occursIn, not_exists, varFree_iff]
  apply forall_comm

lemma areVarsFor_empty {t: Term L V} (ht: varFree t): areVarsFor ∅ t :=
  fun hv => absurd hv (varFree_iff.mp ht _)

/-- If `t` is variable-free, we can identify its
interpretation with a single value. -/
def interpConst [DecidableEq V] (t: Term L V) (ht: varFree t) (𝒜: Structure L A): A :=
  interp t 𝒜 (areVarsFor_empty ht) (fun x => False.elim x.property)

/-- The more natural way of expressing `interpConst`.
See `interpConst_eq_spec`. -/
def interpConst.spec (t: Term L V) (ht: varFree t) (𝒜: Structure L A): A :=
  match t with
  | .var _ => False.elim ht
  | .app F ts =>
    (F^𝒜) (fun i => spec (t := ts i) (ht i) 𝒜)

lemma interpConst_eq_spec [DecidableEq V] {t: Term L V} (ht: varFree t) {𝒜: Structure L A} :
    interpConst t ht 𝒜 = interpConst.spec t ht 𝒜 :=
  match t with
  | .var _ => rfl
  | .app F ts => by
    unfold interpConst interpConst.spec interp
    simp only [←interpConst_eq_spec]
    rfl

/-- `replace t τ x` is `t(τ₁/x₁, ..., τₙ/xₙ)`. -/
def replace [DecidableEq V] (t: Term L V) (x: Set V) [DecidablePred (· ∈ x)] (τ: x → Term L V): Term L V :=
  match t with
  | .var v =>
    if hv: v ∈ x then
      τ ⟨v, hv⟩
    else
      .var v
  | .app F ts => .app F (fun i => replace (ts i) x τ)

/-- Lemma 2.4.1 -/
theorem replace_varFree [DecidableEq V] {t: Term L V} {x: Set V} [DecidablePred (· ∈ x)]
    {τ: x → Term L V} (hx: areVarsFor x t) (h: ∀ v, varFree (τ v)):
    varFree (t.replace x τ) :=
  match t with
  | .var v => by
    unfold replace
    split_ifs with hv
    · apply h
    · have := hx rfl
      contradiction
  | .app F ts =>
    fun i => replace_varFree (areVarsFor_ofApp hx i) h

-- TODO: generators, examples, (maybe) notation
