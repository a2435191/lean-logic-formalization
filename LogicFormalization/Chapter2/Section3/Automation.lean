import LogicFormalization.Chapter2.Section3.Defs

namespace Language.Automation

open Lean Elab Elab.Command

syntax inv  := "⁻¹"
syntax mul  := "⬝"
syntax neg  := "-"
syntax add  := "+"
/-- The syntax for function symbols. Currently
`0`, `1`, `⁻¹`, `⬝`, `-`, and `+`.-/
syntax funs := num <|> inv <|> mul <|> neg <|> add

syntax lt  := "<"
/-- The syntax for relation symbols. Currently just `<`. -/
syntax rels := lt

def symbolNameAndArity (s: Syntax): CommandElabM (Name × ℕ) :=
  let arg := s.getArg 0
  match arg.getKind with
  | ``inv => pure (`inv, 1)
  | ``mul => pure (`mul, 2)
  | ``neg => pure (`neg, 1)
  | ``add => pure (`add, 2)
  | ``lt  => pure (`lt,  2)
  | `num  =>
    match arg.toNat with
    | 0 => pure (`zero, 0)
    | 1 => pure (`one,  0)
    | n => throw (.error s
        s!"Only numeric literals `0` and `1` \
        are supported, but `{n}` was passed in")
  | _ => throw (.error s s!"Received an invalid symbol")

def mkInductiveEnum (typeName: Name) (elemNames: Array Name): Declaration :=
  dbg_trace elemNames
  let ctors := elemNames.toList.map fun name =>
    { name := typeName ++ name, type := .const typeName [] }
  let it :=
    { name := typeName, type := .sort 1, ctors }
  .inductDecl [] 0 [it] false

set_option hygiene false in
elab "#declare_language" lang:ident "{" symbols:(funs<|>rels),* "}" : command => do

  let (fs, rs) := symbols.getElems.partition (·.raw.isOfKind ``funs)
  let fNamesAndArities ← Array.unzip <$> fs.mapM symbolNameAndArity
  let rNamesAndArities ← Array.unzip <$> rs.mapM symbolNameAndArity

  dbg_trace fNamesAndArities
  -- declare the inductive types
  let ϝ := lang.getId ++ `ϝ
  let ρ := lang.getId ++ `ρ
  let fDecl := mkInductiveEnum ϝ fNamesAndArities.fst

  let rDecl := mkInductiveEnum ρ rNamesAndArities.fst
  liftCoreM (addAndCompile fDecl *> addAndCompile rDecl)
  -- from `mkAuxConstructions` (private) in `MutualInductive.lean`
  for fn in [mkRecOn, mkCasesOn, mkNoConfusion, mkBelow, mkIBelow, mkBRecOn, mkBInductionOn] do
    liftTermElabM (fn ϝ *> fn ρ)

  -- derive instances
  elabCommand <| ←`(
    namespace $lang
    deriving instance Repr, DecidableEq for $(mkIdent ϝ), $(mkIdent ρ)


    end $lang
  )

-- namespace OAb
-- #print OAb.ϝ
-- instance: Arity OAb.ϝ where
--   arity x := match x with | .one => 0
-- end OAb


-- #check ϝ
-- #print Nat
-- #print OAb.ϝ.rec

-- open Lean Elab Command in
-- elab "#my_cmd" : command => do
--   let name := `abcde
--   let ctors := [{ name, type := .sort 1, ctors := [⟨name ++ `zero, .const name []⟩] }]
--   let fDecl := .inductDecl [] 0 ctors false
--   liftCoreM (addAndCompile fDecl)


open Lean.Parser.Command in
def mkEnum {m: Type → Type} [Monad m] [MonadQuotation m] (typeName: Name) (elemNames: Array Name): m (TSyntax `Lean.Parser.Command.declaration) := do
  let emptyDeclModifiers ← `(declModifiers|)
  let emptyOptDeclSig ← `(optDeclSig|)
  let ctors: Array (TSyntax `Lean.Parser.Command.ctor) ← elemNames.mapM fun name => do
    have {α}: Coe Syntax (TSyntax α) := ⟨TSyntax.mk⟩
    let ctor := mkNode `Lean.Parser.Command.ctor #[mkNullNode, mkAtom "|", emptyDeclModifiers, ←`($(mkIdent name)), emptyOptDeclSig]
    return ⟨ctor⟩
  return ⟨
    .node .none `Lean.Parser.Command.declaration #[
      emptyDeclModifiers,
      .node .none `Lean.Parser.Command.inductive #[
        mkAtom "inductive",
        ←`(declId| $(mkIdent typeName)),
        emptyOptDeclSig,
        mkNullNode,
        mkListNode ctors,
        mkNullNode,
        ←`(optDeriving|)
      ],
    ]⟩

open Lean Elab Command in
elab "#my_cmd" : command => do
  let name := `abcde
  let stx ← mkEnum name #[`a, `b, `c]
  let stx' ← `(inductive abcde | a | b | c)
  dbg_trace "{stx}\n\n{stx'} {stx.raw == stx'}"
  elabCommand <| stx
  -- let ctors := [{ name, type := .sort 1, ctors := [
  --   ⟨name ++ `zero, .const name []⟩,
  --   ⟨name ++ `one , .const name []⟩] }]
  -- let fDecl := .inductDecl [] 0 ctors false
  -- let preDef: PreDefinition := {
  --   ref := mkIdent name
  --   kind := sorry
  --   levelParams := sorry
  --   modifiers := sorry
  --   declName := sorry
  --   type := sorry
  --   value := sorry
  --   termination := sorry
  -- }
  -- liftCoreM (addAndCompile fDecl)
#my_cmd

#check compileDecls

#check addAndCompileNonRec

-- deriving instance BEq, DecidableEq for abcde
