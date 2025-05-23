import LogicFormalization.Chapter2.Section3.Defs
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Language.Elab

open Lean Elab Elab.Command

syntax lt  := "<"

syntax inv  := "⁻¹"
syntax mul  := "⬝"
syntax neg  := "-"
syntax add  := "+"
/-- The syntax for function symbols. Currently
`0`, `1`, `⁻¹`, `⬝`, `-`, and `+`.-/

syntax langSymbols := lt <|> inv <|> mul <|> neg <|> add <|> num

inductive Symbol
| lt | inv | mul | neg | add | zero | one

namespace Symbol

def ofSyntax.{u} {m: Type → Type u} [Monad m] [MonadExcept Exception m] (s: Syntax): m Symbol :=
  match s.getKind with
  | ``Elab.lt => pure lt
  | ``Elab.inv => pure inv
  | ``Elab.mul => pure mul
  | ``Elab.neg => pure neg
  | ``Elab.add => pure add
  | `num =>
    match s.toNat with
    | 0 => pure zero
    | 1 => pure one
    | n => throw (.error s
        s!"Only numeric literals `0` and `1` \
        are supported, but `{n}` was passed in")
  | k => throw (.error s s!"Received an invalid symbol (kind {k})")

/-- `true` if a functional symbol, `false` if a relation symbol -/
def isFunction: Symbol → Bool
| inv | mul | neg | add | zero | one => true
| lt => false

def name: Symbol → Name
| lt => `lt | inv => `inv | mul => `mul
| neg => `neg | add => `add
| zero => `zero | one => `one

def arity: Symbol → ℕ
| zero | one => 0
| neg | inv => 1
| lt | mul | add => 2


end Symbol

open Lean.Parser.Command in
def mkEnum {m: Type → Type} [Monad m] [MonadQuotation m] (typeName: Name) (elems: Array Symbol): m (TSyntax `Lean.Parser.Command.inductive) := do
  let emptyOptDeclSig ← `(optDeclSig|)
  let ctors: Array (TSyntax `Lean.Parser.Command.ctor) ← elems.mapM fun sym => do
    let ctor := mkNode `Lean.Parser.Command.ctor
      #[mkNullNode, mkAtom "|", ←`(declModifiers|), ←`($(mkIdent sym.name)), emptyOptDeclSig]
    return ⟨ctor⟩
  return ⟨
    .node .none `Lean.Parser.Command.inductive #[
      mkAtom "inductive",
      ←`(declId| $(mkIdent typeName)),
      emptyOptDeclSig,
      mkNullNode,
      mkListNode ctors,
      mkNullNode,
      ←`(optDeriving|)
    ]⟩

/-- Make an `Arity` instance for `ϝ` or `ρ`. If the type is empty, we use `nofun`. Otherwise, match statement to the appropriate arity -/
private def mkArityInstance (typeName: Name) (symbols: Array Symbol)
    : CommandElabM (TSyntax `command) := do
  if symbols.isEmpty then  `(
    instance: Arity $(mkIdent typeName) := ⟨nofun⟩)
  else
    let alts ← symbols.mapM fun sym =>
      `(Parser.Term.matchAltExpr|
        | .$(mkIdent sym.name) => $(Syntax.mkNatLit sym.arity))
    `(
      instance: Arity $(mkIdent typeName) where
        arity $alts:matchAlt*)

/- For the symbols with non-zero arities, generate `NeZero` instances so that
  we can write e.g. `f 0` for `f: Fin (arity Language.Gr.ϝ.inv) → G` (the `0` is a `Fin`). -/
private def mkNeZeroInstances (typeName: Name) (symbols: Array Symbol)
    : CommandElabM (Array (TSyntax `command)) := do
  let stxs ← symbols.filterMapM fun sym =>
    if sym.arity > 0 then some <$> `(
      instance : NeZero (arity $(mkIdent <| typeName ++ sym.name)) :=
        ⟨by decide⟩)
    else pure none
  return stxs

/-- Declare a new language (set of symbols). -/
elab "#declare_language" lang:ident "{" symbols:langSymbols,* "}" : command => do
  let symbols ← symbols.getElems.mapM (fun stx => Symbol.ofSyntax (stx.raw.getArg 0))
  let (fSymbols, rSymbols) := symbols.partition Symbol.isFunction

  -- declare the inductive types
  let ϝ := lang.getId ++ `ϝ
  let ρ := lang.getId ++ `ρ
  let fStx ← mkEnum ϝ fSymbols
  let rStx ← mkEnum ρ rSymbols

  elabInductive {} fStx
  elabInductive {} rStx

  elabCommand <| ←`(
    namespace $lang
    deriving instance Repr, DecidableEq for $(mkIdent ϝ), $(mkIdent ρ)

    $(←mkArityInstance `ϝ fSymbols)
    $(←mkArityInstance `ρ rSymbols)
  )
  for cmd in ←mkNeZeroInstances `ϝ fSymbols do
    elabCommand cmd
  for cmd in ←mkNeZeroInstances `ρ rSymbols do
    elabCommand cmd

  elabCommand <| ←`(
    end $lang

    @[reducible]
    def $(lang) := Language.mk $(mkIdent ρ) $(mkIdent ϝ))


end Elab

#declare_language Gr   { 1, ⁻¹, ⬝ }     -- Groups
#declare_language Ab   { 0, -, + }    -- Additive abelian groups
#declare_language O    { < }            -- Ordered sets
#declare_language OAb  { <, 0, -, + }   -- Ordered abelian groups
#declare_language Rig  { 0, 1, +, ⬝ }    -- Rigs (semirings)
#declare_language Ring { 0, 1, -, +, ⬝ } -- Rings

-- TODO: add proper documentation comments (that propagate to the inductive types)

end Language
