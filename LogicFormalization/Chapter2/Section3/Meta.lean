import LogicFormalization.Chapter2.Section3.Defs
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Mathlib.Algebra.Notation.Defs -- for Inv

namespace Meta

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

variable {m: Type → Type} [Monad m] [MonadExcept Exception m]

def ofSyntax (s: Syntax): m Symbol :=
  match s.getKind with
  | ``Meta.lt => pure lt
  | ``Meta.inv => pure inv
  | ``Meta.mul => pure mul
  | ``Meta.neg => pure neg
  | ``Meta.add => pure add
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

/-- Get the corresponding notation type class in the base logic. For example, `zero => Zero`, `add => Add`.-/
def typeClass: Symbol → Name
| lt => ``LT | inv => ``Inv | mul => ``Mul
| neg => ``Neg | add => ``Add
| zero => ``Zero | one => ``One

/-- For `matchArms`. `f` is a mapping `Fin (arity sym) → A`. -/
def interp [MonadQuotation m]: Symbol → m (TSyntax `term)
| .lt => `(f 0 < f 1)
| .one => `(1)
| .zero => `(0)
| .add => `(f 0 + f 1)
| .neg => `(-(f 0))
| .mul => `(f 0 * f 1)
| .inv => `((f 0)⁻¹)

end Symbol

#check Lean.Parser.Command.definition
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
  symbols.filterMapM fun sym =>
    if sym.arity > 0 then some <$> `(
      instance : NeZero (arity $(mkIdent <| typeName ++ sym.name)) :=
        ⟨by decide⟩)
    else pure none


private def mkStructure (langName: Name) (symbols: Array Symbol):
    CommandElabM (TSyntax `command) := do
  let instances ← symbols.mapM fun sym =>
    `(bracketedBinder| [$(mkIdent sym.typeClass) A])

  let defName := mkIdent <| `Structure ++ langName
  let langTypeForStructure := mkIdent <| `Language ++ langName
  let mkMatchArms (isFun: Bool) := (
    let symbols := symbols.filter (Symbol.isFunction · == isFun)
    if symbols.isEmpty then
      Array.mkArray1 <$> `(Parser.Term.matchAltExpr| | a, _ => nomatch a)
    else symbols.mapM fun sym => do
      `(Parser.Term.matchAltExpr| | .$(mkIdent sym.name), f => $(←sym.interp))
  )
  `(
    def $defName (A: Type*) $[$instances]* [Nonempty A]: Structure $langTypeForStructure A where
      interpRel $(←mkMatchArms false):matchAlt*
      interpFun $(←mkMatchArms true ):matchAlt*
  )

/-- Declare a new language (set of symbols). -/
elab "#declare_language" lang:ident "{" symbols:langSymbols,* "}" : command => do
  let symbols ← symbols.getElems.mapM (fun stx => Symbol.ofSyntax (stx.raw.getArg 0))
  let (fSymbols, rSymbols) := symbols.partition Symbol.isFunction

  -- declare the inductive types
  let ϝ := lang.getId ++ `ϝ
  let ρ := lang.getId ++ `ρ
  let fStx ← mkEnum (`Language ++ ϝ) fSymbols
  let rStx ← mkEnum (`Language ++ ρ) rSymbols

  elabInductive {} fStx
  elabInductive {} rStx

  let languageNS := mkIdent <| `Language ++ lang.getId
  elabCommand <| ←`(
    namespace $languageNS
    deriving instance Repr, DecidableEq for $(mkIdent ϝ), $(mkIdent ρ)

    $(←mkArityInstance ϝ fSymbols)
    $(←mkArityInstance ρ rSymbols)
  )
  for cmd in ←mkNeZeroInstances ϝ fSymbols do
    elabCommand cmd
  for cmd in ←mkNeZeroInstances ρ rSymbols do
    elabCommand cmd

  elabCommand <| ←`(
    end $languageNS

    @[reducible]
    def $languageNS := Language.mk $(mkIdent ρ) $(mkIdent ϝ))
  /-Make a structure like

    ```def Structure.Ring [Zero A] [One A] [Neg A] [Add A] [Mul A] : Structure Language.Ring A where
    interpRel := nofun
    interpFun
    | .zero, _ => 0
    | .one,  _ => 1
    | .neg,  f => -(f 0)
    | .add,  f => f 0 + f 1
    | .mul,  f => f 0 * f 1
    ```
  -/
  elabCommand (←mkStructure lang.getId symbols)


end Meta

#declare_language Gr   { 1, ⁻¹, ⬝ }     -- Groups
#declare_language Ab   { 0, -, + }    -- Additive abelian groups
#declare_language O    { < }            -- Ordered sets
#declare_language OAb  { <, 0, -, + }   -- Ordered abelian groups
#declare_language Rig  { 0, 1, +, ⬝ }    -- Rigs (semirings)
#declare_language Ring { 0, 1, -, +, ⬝ } -- Rings

-- TODO: add proper documentation comments (that propagate to the inductive types)
