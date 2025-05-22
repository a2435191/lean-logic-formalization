import LogicFormalization.Chapter2.Section3.Defs
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Language.Elab

open Lean Elab Elab.Command

syntax lt  := "<"
/-- The syntax for relation symbols. Currently just `<`. -/
syntax rels := lt

syntax inv  := "⁻¹"
syntax mul  := "⬝"
syntax neg  := "-"
syntax add  := "+"
/-- The syntax for function symbols. Currently
`0`, `1`, `⁻¹`, `⬝`, `-`, and `+`.-/
syntax funs := num <|> inv <|> mul <|> neg <|> add

def symbolNameAndArity (s: Syntax): CommandElabM (Name × ℕ) :=
  let arg := s.getArg 0
  match arg.getKind with
  | ``lt  => pure (`lt,  2)
  | ``inv => pure (`inv, 1)
  | ``mul => pure (`mul, 2)
  | ``neg => pure (`neg, 1)
  | ``add => pure (`add, 2)
  | `num  =>
    match arg.toNat with
    | 0 => pure (`zero, 0)
    | 1 => pure (`one,  0)
    | n => throw (.error s
        s!"Only numeric literals `0` and `1` \
        are supported, but `{n}` was passed in")
  | _ => throw (.error s s!"Received an invalid symbol")

open Lean.Parser.Command in
def mkEnum {m: Type → Type} [Monad m] [MonadQuotation m] (typeName: Name) (elemNames: Array Name): m (TSyntax `Lean.Parser.Command.inductive) := do
  let emptyOptDeclSig ← `(optDeclSig|)
  let ctors: Array (TSyntax `Lean.Parser.Command.ctor) ← elemNames.mapM fun name => do
    let ctor := mkNode `Lean.Parser.Command.ctor #[mkNullNode, mkAtom "|", ←`(declModifiers|), ←`($(mkIdent name)), emptyOptDeclSig]
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
private def mkArityInstance (typeName: Name) (namesAndArities: Array (Name × ℕ))
    : CommandElabM (TSyntax `command) := do
  if namesAndArities.isEmpty then  `(
    instance: Arity $(mkIdent typeName) := ⟨nofun⟩)
  else
    let alts ← namesAndArities.mapM fun (name, arity) =>
      `(Parser.Term.matchAltExpr|
        | .$(mkIdent name) => $(Syntax.mkNatLit arity))
    `(
      instance: Arity $(mkIdent typeName) where
        arity $alts:matchAlt*)

/- For the symbols with non-zero arities, generate `NeZero` instances so that
  we can write e.g. `f 0` for `f: Fin (arity Language.Gr.ϝ.inv) → G` (the `0` is a `Fin`). -/
private def mkNeZeroInstances (typeName: Name) (namesAndArities: Array (Name × ℕ))
    : CommandElabM (Array (TSyntax `command)) := do
  let stxs ← namesAndArities.filterMapM fun (name, arity) =>
    if arity > 0 then some <$> `(
      instance : NeZero (arity $(mkIdent <| typeName ++ name)) :=
        ⟨by decide⟩)
    else pure none
  return stxs

/-- Declare a new language (set of symbols). -/
elab "#declare_language" lang:ident "{" symbols:(funs<|>rels),* "}" : command => do
  let (fs, rs) := symbols.getElems.partition (·.raw.isOfKind ``funs)
  let fNamesAndArities ← fs.mapM symbolNameAndArity
  let rNamesAndArities ← rs.mapM symbolNameAndArity

  -- declare the inductive types
  let ϝ := lang.getId ++ `ϝ
  let ρ := lang.getId ++ `ρ
  let fStx ← mkEnum ϝ fNamesAndArities.unzip.1
  let rStx ← mkEnum ρ rNamesAndArities.unzip.1

  elabInductive {} fStx
  elabInductive {} rStx

  elabCommand <| ←`(
    namespace $lang
    deriving instance Repr, DecidableEq for $(mkIdent ϝ), $(mkIdent ρ)

    $(←mkArityInstance `ϝ fNamesAndArities)
    $(←mkArityInstance `ρ rNamesAndArities)
  )
  for cmd in ←mkNeZeroInstances `ϝ fNamesAndArities do
    elabCommand cmd
  for cmd in ←mkNeZeroInstances `ρ rNamesAndArities do
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
