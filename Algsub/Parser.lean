import Lean
import Algsub.Basic

open Lean Elab Meta

declare_syntax_cat Term

declare_syntax_cat Field
syntax ident "=" Term : Field
syntax Term : Field
declare_syntax_cat NEFields
syntax Field : NEFields
syntax ident "=" Term "," NEFields : NEFields

declare_syntax_cat Atom
syntax "(" Term ")" : Atom
syntax ident : Atom
syntax num : Atom
syntax "true" : Atom
syntax "false" : Atom
syntax "{}" : Atom
syntax "{" NEFields "}" : Atom

declare_syntax_cat PathTerm
syntax PathTerm "." ident : PathTerm
syntax Atom : PathTerm

declare_syntax_cat AppTerm
syntax PathTerm : AppTerm
syntax AppTerm PathTerm : AppTerm

syntax AppTerm : Term
syntax "if" Term "then" Term "else" Term : Term
syntax "let" ident "=" Term "in" Term : Term
syntax "fun" ident "->" Term : Term
syntax "fix" Term : Term
