import Mathlib.Tactic
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeMap
open Lean hiding Environment Exception
open Meta

namespace Types
inductive Polarity | pos | neg
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
    | .pos => .neg | .neg => .pos

abbrev Symbol := String

inductive TyArg (α : Type) where
    | pos    (a : α)
    | neg    (a : α)
    | negPos (n p : α)
    | none
    deriving BEq, Repr

inductive Head (α : Type) where
    | func : α → α → Head α
    | rcd  : List (Symbol × α) → Head α
    | base (stamp : Nat) (args : List (TyArg α))
  deriving BEq, Repr
abbrev StateId := ℕ

-- nondeterministic finite automata
structure State where
  pol : Polarity
  cons : List (Head (Std.HashSet StateId))
  flow : Std.HashSet StateId

structure Automata where
  states : Array State
-- Type representation
inductive Ty where
    | var  (v : Symbol)          -- TNamed v []  (free, or bound by an enclosing rec)
    | zero                       -- ⊥ at +, ⊤ at −
    | add  (a b : Ty)            -- ⊔ at +, ⊓ at −
    | fix  (v : Symbol) (t : Ty) -- μv.t
    | cons (h : Head α)

inductive Node (ι : Type) where
  | var    (v : Symbol)   -- free variable
  | zero
-- | unit
  | sum    (a b : ι)
 -- | prod (a b : ι)
  | fix    (body : ι)
  | fixVar (binder : ι)   -- bound occurrence → its μ node
  | cons   (h : Head ι)
  deriving BEq, Repr

inductive Variance
  | VPos | VNeg | VNegPos | None
  deriving BEq, Repr

structure TyCtx where
  next : Nat := 1
  decls : Std.HashMap ℕ (Symbol × Array Variance) := {}
  byName : Std.HashMap Symbol ℕ := {}





structure Typechecker.Context where
  env : TyCtx := {}

structure Typechecker.State where
  ngen : ℕ  := 0
  nvargen : ℕ := 0


abbrev M := ReaderT Context <| StateT Typechecker.State <| Except String

def mkFreshId : M ℕ := do{
  let s ← get;
  modify (fun s ↦ {s with ngen := s.ngen + 1});
  pure s.ngen
}

end Types
