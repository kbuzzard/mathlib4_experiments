import Lean

open Lean

deriving instance Repr for ParserDescr

unsafe def getParserDescrUnsafe (name : Name) : CoreM (Option ParserDescr) := do
  let info ← getConstInfo name
  if info.type.isConstOf ``ParserDescr || info.type.isConstOf ``TrailingParserDescr then
    return some (← evalConst ParserDescr info.name)
  return none

@[implementedBy getParserDescrUnsafe]
constant getParserDescr : Name → CoreM (Option ParserDescr)

def formatPrec (prec : Nat) (default := 0) : Format :=
  if prec == default then ""
  else if prec == eval_prec min then ":min"
  else if prec == eval_prec max then ":max"
  else if prec == eval_prec lead then ":lead"
  else if prec == eval_prec arg then ":arg"
  else f!":{prec}"

open ParserDescr in
def getParserInfo (category : Name) (p : ParserDescr) : Format := do
  if category == `term then
    if let trailingNode _ prec prec₁ (binary `andthen (symbol s) (cat c₂ prec₂)) := p then
      if c₂ == category then
        if prec₁ == prec && prec₂ == prec + 1 then
          return f!"infixl{formatPrec prec} {repr s}"
        if prec₁ == prec + 1 && prec₂ == prec then
          return f!"infixr{formatPrec prec} {repr s}"
        if prec₁ == prec + 1 && prec₂ == prec + 1 then
          return f!"infix{formatPrec prec} {repr s}"
    if let node _ prec (binary `andthen (symbol s) (cat c₁ prec₁)) := p then
      if c₁ == category && prec₁ == prec then
        return f!"prefix{formatPrec prec} {repr s}"
    if let trailingNode _ prec prec₁ (symbol s) := p then
      if prec₁ == prec then
        return f!"postfix{formatPrec prec} {repr s}"
  if let node _ prec p₁ := p then
    return f!"syntax{formatPrec prec (eval_prec lead)} {go p₁} : {category}"
  if let trailingNode _ prec prec₁ p₁ := p then
    return f!"syntax{formatPrec prec} {category}{formatPrec prec₁} {go p₁} : {category}"
  return Format.paren (repr p)
where
  go : ParserDescr → Format
  | const k => format k
  | unary _ p => go p
  | binary `andthen p₁ p₂ => go p₁ ++ " " ++ go p₂
  | binary `orelse p₁ p₂ => Format.paren (go p₁ ++ " <|> " ++ go p₂)
  | binary b p₁ p₂ => f!"{go p₁} <{b}> {go p₂}"
  | node _ _ p => go p
  | trailingNode _ _ _ p => go p
  | symbol s => repr s
  | nonReservedSymbol s _ => "&" ++ repr s
  | cat catName prec => format catName ++ formatPrec prec
  | nodeWithAntiquot _ _ p => go p
  | sepBy p sep _ _ => Format.paren (go p) ++ sep ++ "*"
  | sepBy1 p sep _ _ => Format.paren (go p) ++ sep ++ "+"
  | parser k => format k

def getConstDeclPos (declName : Name) : CoreM Format := do
  let module := (← findModuleOf? declName).map format |>.getD "<local>"
  let range := (← findDeclarationRanges? declName).map (format ·.range.pos.line) |>.getD "???"
  return f!"{module}:{range}"

open Std.Format in
partial def getNotationInfo (category : Name) (stx : Syntax) : CoreM Format := do
  let kind := stx.getKind
  if kind == `choice then
    return nestD <| prefixJoin line (← stx.getArgs.toList.mapM (getNotationInfo category))
  if #[nullKind, identKind, strLitKind, charLitKind, numLitKind, scientificLitKind, nameLitKind, fieldIdxKind, interpolatedStrLitKind, interpolatedStrKind].elem kind
    || (`antiquot).isSuffixOf kind then
    return f!"{kind} @ <builtin>"
  let info ← match ← getParserDescr kind with
    | some descr => getParserInfo category descr
    | none => format (← getConstInfo kind).name
  let pos ← getConstDeclPos kind
  return f!"{info}{Format.group f!" @ {pos}"}"

open Lean.Parser Lean.Elab Lean.Elab.Command

syntax (name := printNotation) "#print_notation " strLit (" : " ident)? : command

@[commandElab printNotation]
def elabPrintNotation : CommandElab
| `(#print_notation%$tk $str $[: $category:ident]?) => do
  let input := str.isStrLit?.get!
  let category := category.map (·.getId) |>.getD `term
  match runParserCategory (← getEnv) category input with
  | Except.error err => logErrorAt str m!"{err}"
  | Except.ok stx => do
    let msg ← liftCoreM <| getNotationInfo category stx
    logInfoAt tk m!"{repr input} => {msg}"
| _ => throwUnsupportedSyntax

#print_notation "1 + 2"
#print_notation "2 * 3"
#print_notation "4 ^ 5"
#print_notation "6 = 7"

postfix:lead "⁻¹" => 2
 
#print_notation "-1"
#print_notation "x⁻¹"

#print_notation "eval_prec max"
#print_notation "[1, 2, 3]"
#print_notation "if x then y else z"

#print_notation "@& Nat"
#print_notation "a[i]"
#print_notation "← _"

#print_notation "11"
#print_notation "{}"
--#print_notation "$x"

#print_notation "intro" : tactic
#print_notation "rw [a]" : tactic
--#print_notation "cases _ with | $x => $y" : tactic
--#print_notation "$x <;> $y" : tactic

#print_notation "#check 1" : command
#print_notation "#print_notation \"\"" : command

#print_notation "a == b"