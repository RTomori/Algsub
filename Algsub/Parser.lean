import Lean
import Algsub.Typing

/-!
# Concrete syntax for the ML-like core language

Surface syntax in the style of PCF++, elaborated directly into the locally
nameless `Exp` of `Algsub.Basic`.  The entry points are the term-level
`[alg| e]` and the command `#alg e`, which infers a typing for `e`.

Scope resolution happens during elaboration: `Parser.translate` threads a
binder context (innermost binder first) through the surface tree, so a bound
occurrence becomes `Exp.bvar` at its de Bruijn index and an unbound one
becomes `Exp.fvar`.  Plain `macro_rules` cannot do this, being context-free.

Three constraints shaped the grammar:
* A reserved token in *any* syntax declaration poisons that spelling as a Lean
  identifier for every downstream file.  So the only leading keywords spelled
  as string literals are ones Lean already reserves
  (`if then else let in fun true false`).
* `&"kw"` (a non-reserved symbol) cannot lead an alternative in a category
  whose leading parsers include `ident`, unless the category is declared with
  `behavior := symbol`: otherwise the application rule wins and the keyword
  never matches.  With `symbol` behavior, `fix` and `rec` are keywords of the
  object language while staying ordinary identifiers in Lean.
* `r.foo` lexes as a single dotted identifier, so projection off a variable is
  resolved in the elaborator rather than by the `.` rule, which is left to
  handle compound receivers such as `(fun x -> x).f`.

Patterns (`algpat`) appear wherever a binder does: `fun p₁ … pₙ -> e`,
`let p = e in b`, the parameters of `let rec`, and the clauses of
`match e with | p₁ -> b₁ | …`.  Every clause starts with `|`; a clause body
extends as far as it can, so a `match` nested in a body that is not the last
must be parenthesized.  A `let` whose pattern is a
bare variable stays a polymorphic `Exp.letE`; any other is sugar for
`(fun p -> b) e`, hence monomorphic.  Tags are written `` `l ``, which lexes as
a name literal, so like `_`, `&` and `|` it reserves no new token.

`Exp.seq` has deliberately no concrete syntax: `TypeChecker.inferExpr` has no
rule for it.  Nor, yet, for `Exp.case`, so `#typecheck` reports `Impossible`
for a `match`.
-/

namespace Algsub

open Lean Elab Term

/-! ## Grammar -/

declare_syntax_cat algsub (behavior := symbol)
/-- With `symbol` behavior, leading `"true"`/`"false"` match identifiers instead of
becoming tokens, which would stop them parsing as Lean terms. -/
declare_syntax_cat algpat (behavior := symbol)

/-- A record field `l = e`. -/
syntax algsubField := ident " = " algsub
/-- A record pattern field `l = p`. -/
syntax algpatField := ident " = " algpat
/-- A match clause `| p -> e`. -/
syntax algsubClause := " | " algpat " -> " algsub

syntax:max ident : algsub
syntax:max num : algsub
syntax:max "-" num : algsub
syntax:max "true" : algsub
syntax:max "false" : algsub
syntax:max "{" algsubField,* "}" : algsub
syntax:max "(" algsub ")" : algsub
/-- Escape hatch: splice a Lean-level `Exp` value into surface syntax. -/
syntax:max "~" term:max : algsub
/-- A tag `` `l ``: applied, it injects its argument; bare, it carries `{}`. -/
syntax:max name : algsub

syntax:1023 algsub:1023 "." ident : algsub          -- projection
syntax:1022 algsub:1022 algsub:1023 : algsub        -- application, left assoc
syntax:max "!" algsub:max : algsub                  -- boolean negation

syntax:70 algsub:70 " * " algsub:71 : algsub
syntax:65 algsub:65 " + " algsub:66 : algsub
syntax:35 algsub:36 " && " algsub:35 : algsub
syntax:30 algsub:31 " || " algsub:30 : algsub

syntax:5 "fun" algpat:max+ " -> " algsub:5 : algsub
syntax:5 "if" algsub " then " algsub " else " algsub:5 : algsub
syntax:5 "let" algpat " = " algsub " in " algsub:5 : algsub
syntax:5 "let" &"rec" ident algpat:max* " = " algsub " in " algsub:5 : algsub
syntax:5 &"fix" ident " => " algsub:5 : algsub
syntax:5 "match" algsub " with" algsubClause+ : algsub

syntax:max ident : algpat
syntax:max "_" : algpat
syntax:max num : algpat
syntax:max "-" num : algpat
syntax:max "true" : algpat
syntax:max "false" : algpat
syntax:max "{" algpatField,* "}" : algpat
syntax:max "(" algpat ")" : algpat
syntax:max name : algpat                            -- `l, matching `l {}
syntax:100 name algpat:max : algpat                 -- `l p
syntax:35 algpat:36 " & " algpat:35 : algpat
syntax:30 algpat:31 " | " algpat:30 : algpat

/-- Entry point: `[alg| e]` is the `Exp` denoted by the surface term `e`. -/
syntax:max "[alg| " algsub "]" : term

/-! ## Primitives

Primitives are *identifiers*, resolved during elaboration, so none of them has
to be a token.  A primitive in head position with enough arguments becomes the
corresponding `Exp` node; used bare, or applied to too few arguments, it is
η-expanded, since `Exp.const` has no typing rule.  Being identifiers, they can
also be shadowed by a binder, as in `fun succ -> succ 1`. -/

namespace Parser

/-- Arity of each primitive identifier. -/
def primArity : String → Option Nat
  | "succ" | "pred" | "iszero" | "not" => some 1
  | "add" | "mul" | "and" | "or" => some 2
  | _ => none

/-- A binder context, innermost binder first; a name's position is its index. -/
abbrev Ctx := List String

def Ctx.index? (ctx : Ctx) (x : String) : Option Nat := ctx.findIdx? (· == x)

private def strLit (s : String) : Term := Syntax.mkStrLit s

/-- `Exp` for a primitive appearing in a non-saturated position. -/
def etaPrim : String → MacroM Term
  | "succ"   => `(Exp.lam (Pat.pbvar 0) (Exp.succ (Exp.bvar 0)))
  | "pred"   => `(Exp.lam (Pat.pbvar 0) (Exp.pred (Exp.bvar 0)))
  | "iszero" => `(Exp.lam (Pat.pbvar 0) (Exp.iszero (Exp.bvar 0)))
  | "not"    => `(Exp.lam (Pat.pbvar 0) (Exp.not (Exp.bvar 0)))
  | "add"    => `(Exp.lam (Pat.pbvar 0) (Exp.lam (Pat.pbvar 0) (Exp.add (Exp.bvar 1) (Exp.bvar 0))))
  | "mul"    => `(Exp.lam (Pat.pbvar 0) (Exp.lam (Pat.pbvar 0) (Exp.mul (Exp.bvar 1) (Exp.bvar 0))))
  | "and"    => `(Exp.lam (Pat.pbvar 0) (Exp.lam (Pat.pbvar 0) (Exp.and (Exp.bvar 1) (Exp.bvar 0))))
  | "or"     => `(Exp.lam (Pat.pbvar 0) (Exp.lam (Pat.pbvar 0) (Exp.or (Exp.bvar 1) (Exp.bvar 0))))
  | c        => `(Exp.const $(strLit c))

/-- Resolve one identifier.  A dotted identifier `r.a.b` becomes a projection
chain off its first component, since the lexer hands it over as one token. -/
def translateIdent (ctx : Ctx) (id : Ident) : MacroM Term := do
  match id.getId.components.map Name.toString with
  | [] => Macro.throwErrorAt id "empty identifier"
  | base :: labels =>
    let hd ←
      match ctx.index? base with
      | some i => `(Exp.bvar $(Syntax.mkNatLit i))
      | none   =>
        if (primArity base).isSome && labels.isEmpty then etaPrim base
        else `(Exp.fvar $(strLit base))
    labels.foldlM (fun e l => `(Exp.proj $e $(strLit l))) hd

/-! ## Patterns

The `i`-th distinct variable of a pattern, left to right, is slot `i`, referred
to by `bvar i` in the body.  Slots are assigned by name, so both sides of `|`
bind the same slots in whatever order they mention them; a variable repeated
under `&` or across record fields shares one slot, which
`TypeChecker.inferPat` rejects as ill-formed. -/

private def tagName (l : TSyntax `name) : String := l.getName.toString (escape := false)

/-- The variables of a pattern in slot order, appended to `acc`. -/
partial def patVars (acc : Array String) (stx : TSyntax `algpat) : Array String :=
  match stx with
  | `(algpat| $x:ident) =>
      let n := x.getId.toString
      if acc.contains n then acc else acc.push n
  | `(algpat| ($p)) | `(algpat| $_:name $p) => patVars acc p
  | `(algpat| $p & $q) | `(algpat| $p | $q) => patVars (patVars acc p) q
  | `(algpat| { $fs,* }) =>
      fs.getElems.foldl (fun acc f =>
        match f with
        | `(algpatField| $_:ident = $p) => patVars acc p
        | _ => acc) acc
  | _ => acc

/-- Translate a pattern whose variables, in slot order, are `vars`. -/
partial def translatePat (vars : Array String) (stx : TSyntax `algpat) : MacroM Term := do
  match stx with
  | `(algpat| ($p))   => translatePat vars p
  | `(algpat| $x:ident) =>
      unless x.getId.isAtomic do Macro.throwErrorAt x "pattern variables cannot be dotted"
      match vars.findIdx? (· == x.getId.toString) with
      | some i => `(Pat.pbvar $(Syntax.mkNatLit i))
      | none   => Macro.throwErrorAt x "unexpected pattern variable"
  | `(algpat| _)      => `(Pat.pwild)
  | `(algpat| true)   => `(Pat.plbool true)
  | `(algpat| false)  => `(Pat.plbool false)
  | `(algpat| $n:num) => `(Pat.plint $(Syntax.mkNatLit n.getNat))
  | `(algpat| -$n:num) => `(Pat.plint (-$(Syntax.mkNatLit n.getNat)))
  | `(algpat| $l:name) => `(Pat.pinj $(strLit (tagName l)) (Pat.prcd PatFields.nil))
  | `(algpat| $l:name $p) => `(Pat.pinj $(strLit (tagName l)) $(← translatePat vars p))
  | `(algpat| $p & $q) => `(Pat.pand $(← translatePat vars p) $(← translatePat vars q))
  | `(algpat| $p | $q) => `(Pat.por $(← translatePat vars p) $(← translatePat vars q))
  | `(algpat| { $fs,* }) => do
      let mut out ← `(PatFields.nil)
      for f in fs.getElems.reverse do
        match f with
        | `(algpatField| $l:ident = $p) =>
            out ← `(PatFields.cons $(strLit l.getId.toString) $(← translatePat vars p) $out)
        | _ => Macro.throwErrorAt f "ill-formed record pattern field"
      `(Pat.prcd $out)
  | _ => Macro.throwErrorAt stx "unsupported pattern"

mutual

/-- Flatten an application spine into its head and its arguments, in order. -/
partial def spine (stx : TSyntax `algsub) : Array (TSyntax `algsub) × TSyntax `algsub :=
  match stx with
  | `(algsub| $f:algsub $a:algsub) => let (as, hd) := spine f; (as.push a, hd)
  | _ => (#[], stx)

/-- Translate a surface term under the binder context `ctx`. -/
partial def translate (ctx : Ctx) (stx : TSyntax `algsub) : MacroM Term := do
  match stx with
  | `(algsub| ($e))          => translate ctx e
  | `(algsub| ~$e:term)      => pure e
  | `(algsub| $x:ident)      => translateIdent ctx x
  | `(algsub| $l:name)       => `(Exp.inj $(strLit (tagName l)) (Exp.rcd Fields.nil))
  | `(algsub| true)          => `(Exp.lbool true)
  | `(algsub| false)         => `(Exp.lbool false)
  | `(algsub| $n:num)        => `(Exp.lint $(Syntax.mkNatLit n.getNat))
  | `(algsub| -$n:num)       => `(Exp.lint (-$(Syntax.mkNatLit n.getNat)))
  | `(algsub| $e . $l:ident) => `(Exp.proj $(← translate ctx e) $(strLit l.getId.toString))
  | `(algsub| !$e)           => `(Exp.not $(← translate ctx e))
  | `(algsub| $a * $b)       => `(Exp.mul $(← translate ctx a) $(← translate ctx b))
  | `(algsub| $a + $b)       => `(Exp.add $(← translate ctx a) $(← translate ctx b))
  | `(algsub| $a && $b)      => `(Exp.and $(← translate ctx a) $(← translate ctx b))
  | `(algsub| $a || $b)      => `(Exp.or  $(← translate ctx a) $(← translate ctx b))
  | `(algsub| fix $f:ident => $b) => do
      let n := f.getId.toString
      `(Exp.fix $(strLit n) $(← translate (n :: ctx) b))
  | `(algsub| if $c then $t else $f) =>
      `(Exp.ifc $(← translate ctx c) $(← translate ctx t) $(← translate ctx f))
  | `(algsub| fun $ps:algpat* -> $b) => translateFun ctx ps b
  | `(algsub| let $p:algpat = $v in $b) => do
      if let `(algpat| $x:ident) := p then
        let n := x.getId.toString
        `(Exp.letE $(strLit n) $(← translate ctx v) $(← translate (n :: ctx) b))
      else
        `(Exp.app $(← translateFun ctx #[p] b) $(← translate ctx v))
  | `(algsub| let rec $f:ident $ps:algpat* = $v in $b) => do
      let fn := f.getId.toString
      `(Exp.letE $(strLit fn) (Exp.fix $(strLit fn) $(← translateFun (fn :: ctx) ps v))
          $(← translate (fn :: ctx) b))
  | `(algsub| match $e with $cs:algsubClause*) => do
      let mut out ← `(Clauses.nil)
      for c in cs.reverse do
        match c with
        | `(algsubClause| | $p -> $b) =>
            let vars := patVars #[] p
            out ← `(Clauses.cons $(← translatePat vars p) $(← translate (vars.toList ++ ctx) b) $out)
        | _ => Macro.throwErrorAt c "ill-formed match clause"
      `(Exp.case $(← translate ctx e) $out)
  | `(algsub| { $fs,* }) => do
      let mut out ← `(Fields.nil)
      for f in fs.getElems.reverse do
        match f with
        | `(algsubField| $l:ident = $e) =>
            out ← `(Fields.cons $(strLit l.getId.toString) $(← translate ctx e) $out)
        | _ => Macro.throwErrorAt f "ill-formed record field"
      `(Exp.rcd $out)
  | _ => translateApp ctx stx

/-- `fun p₁ … pₙ -> b`: nested pattern lambdas, the body seeing the variables of
the innermost pattern first.  With no patterns, just `b`. -/
partial def translateFun (ctx : Ctx) (ps : Array (TSyntax `algpat)) (b : TSyntax `algsub) :
    MacroM Term := do
  let varss := ps.map (patVars #[])
  let body ← translate (varss.foldl (fun ctx vs => vs.toList ++ ctx) ctx) b
  (ps.zip varss).foldrM (fun (p, vs) e => do `(Exp.lam $(← translatePat vs p) $e)) body

/-- Application, with primitive and tag heads folded into their `Exp` nodes. -/
partial def translateApp (ctx : Ctx) (stx : TSyntax `algsub) : MacroM Term := do
  let (args, hd) := spine stx
  if args.isEmpty then Macro.throwErrorAt stx "unsupported syntax"
  if let `(algsub| $l:name) := hd then
    let inj ← `(Exp.inj $(strLit (tagName l)) $(← translate ctx args[0]!))
    return ← (args[1:].toArray).foldlM (fun e a => do `(Exp.app $e $(← translate ctx a))) inj
  if let `(algsub| $f:ident) := hd then
    let name := f.getId.toString
    if (ctx.index? name).isNone then
      if let some n := primArity name then
        if args.size >= n then
          let prim ← translatePrim ctx name args[0:n]
          return ← (args[n:].toArray).foldlM
            (fun e a => do `(Exp.app $e $(← translate ctx a))) prim
  args.foldlM (fun e a => do `(Exp.app $e $(← translate ctx a))) (← translate ctx hd)

/-- A saturated primitive application. -/
partial def translatePrim (ctx : Ctx) (name : String) (args : Array (TSyntax `algsub)) :
    MacroM Term := do
  match name, args with
  | "succ",   #[a] => `(Exp.succ $(← translate ctx a))
  | "pred",   #[a] => `(Exp.pred $(← translate ctx a))
  | "iszero", #[a] => `(Exp.iszero $(← translate ctx a))
  | "not",    #[a] => `(Exp.not $(← translate ctx a))
  | "add",    #[a, b] => `(Exp.add $(← translate ctx a) $(← translate ctx b))
  | "mul",    #[a, b] => `(Exp.mul $(← translate ctx a) $(← translate ctx b))
  | "and",    #[a, b] => `(Exp.and $(← translate ctx a) $(← translate ctx b))
  | "or",     #[a, b] => `(Exp.or  $(← translate ctx a) $(← translate ctx b))
  | _, _ => Macro.throwErrorAt args[0]! s!"'{name}' applied to wrong number of arguments"

end

end Parser

macro_rules | `([alg| $e:algsub]) => Parser.translate [] e

/-- `#typecheck e` infers a typing for the surface term `e`. -/
syntax (name := algCmd) "#typecheck " algsub : command

elab_rules : command
  | `(command| #typecheck $e:algsub) => do
      let t ← liftMacroM <| Parser.translate [] e
      let src := ((e.raw.getSubstring?.map (·.toString)).getD (toString e.raw)).trimAscii.toString
      Lean.Elab.Command.elabCommand (← `(command|
        #eval show IO Unit from do
          IO.print ($(quote src))
          IO.println (" ⊩ " ++ toString (repr (TypeChecker.inferExpr $t).run))))


#typecheck fun g -> fun h -> fun y -> if false then y else h (g (h y))

#typecheck fix f => fun g -> fun y -> if false then y else g(f g y)


#typecheck fix g => fun x -> g 2 + g false
#eval [alg|fix f => fun g -> fun y -> if false then y else g (f g y)]
#typecheck fix f => fun g -> fun y -> if false then y else g (f g y)
#typecheck fun r -> r. l
#typecheck let id = fun x -> x in fun b -> if b then {x = 42, y = id} else {x = 17, y = false}
#typecheck fun l -> l.a.b + l.b.y

#typecheck fun x -> if x.p then x.q else x.q
#typecheck fix g => fun x -> g 2 + g false
#typecheck fix x => (fun y -> fun z -> z) (x x)
#typecheck let f = fun x -> x in f f
#typecheck (fun f -> (fun x -> f (fun v -> (x x) v)) (fun x -> f (fun v -> (x x) v)))
#typecheck let rec f = fun x -> {l = x, r = f x} in f

#typecheck fun {a = x, b = y} -> x + y
#typecheck fun (r & {p = b}) -> if b then r.q else 0
#typecheck fun (`a x | `b x) -> x + 1
#typecheck fun (`some _ | `none) (true | false) -> 1
#typecheck let {x = a, y = b} = {x = 1, y = true} in if b then a else 0
#typecheck (fun (`a x | `b x) -> x + 1) (`a 3)
#eval [alg| let rec len l = match l with | `nil -> 0 | `cons {tl = t} -> 1 + len t in len]

end Algsub
