import Mathlib.Tactic
import Std.Data.HashMap
import Std.Data.HashSet
import Algsub.Basic
import Algsub.Types

/-! Type inference directly on scheme automata. Each typing rule copies in the automata of its
premises, adds the states for its constraint, and biunifies. Biunification rewrites states in
place, so the bisubstitution it stands for is already applied to every root: there is no
`apply_pos ξ` / `apply_neg ξ` step, a rule only chooses its result state. -/

namespace Typecheck
open Types

-- let-bound variables stand for the scheme automaton of their definition
abbrev TM := ReaderT (Std.HashMap String SAutomata) Types.M

-- stamps of the ground types in `default_tyenv`
def boolK : ℕ := 1
def intK : ℕ := 2

-- a scheme automaton under construction: rules append states and rewrite them in place, never
-- renumber, so state ids handed out earlier stay valid
abbrev BuildM := StateT Automata Types.M

def build (x : BuildM (Std.HashMap String StateId × StateId)) : Types.M SAutomata := do{
  let ((env, res), A) ← x.run #[];
  pure {scheme := A, env := env, res := res}
}

def alloc (p : Polarity) (cons : List (Head (List StateId))) (flow : List StateId := []) :
    BuildM StateId :=
  modifyGet fun A ↦ (A.size, A.push (create_state p cons flow))

def State.shift (k : ℕ) (s : State) : State :=
  let sh (ss : Std.HashSet StateId) : Std.HashSet StateId :=
    ss.fold (fun acc q ↦ acc.insert (q + k)) {};
  {s with cons := s.cons.map (Head.mapM (m := Id) sh), flow := sh s.flow}

-- copy a sub-derivation's automaton in after the current states; its type variables are flow
-- edges between its own states, so they stay disjoint from everyone else's
def embed (a : SAutomata) : BuildM (Std.HashMap String StateId × StateId) :=
  modifyGet fun A ↦
    let k := A.size;
    ((a.env.map fun _ q ↦ q + k, a.res + k),
     if k = 0 then a.scheme else A ++ a.scheme.map (State.shift k))

-- a fresh type variable α, i.e. α⁻ ⇝ α⁺
def flowPair : BuildM (StateId × StateId) := do{
  let p ← alloc .pos [];
  let n ← alloc .neg [] [p];
  pure (n, p)
}

-- solve q⁺ ≤ q⁻. The memo table starts empty: `embed` renumbers states, so pairs remembered from
-- an earlier constraint may name different states now
def constrain (q₁ q₂ : StateId) : BuildM Unit := do{
  let A ← get;
  if h : q₁ < A.size ∧ q₂ < A.size then
    let ⟨(A, _), _⟩ ← Types.biunify A.toVector {} (← read).env.decls ⟨q₁, h.1⟩ ⟨q₂, h.2⟩;
    set A.toArray
  else throw s!"dangling state id"
}

-- Δ₁ ⊓ Δ₂: a variable bound in both gets a fresh state with the heads and flow edges of each
def meetEnv (Δ₁ Δ₂ : Std.HashMap String StateId) : BuildM (Std.HashMap String StateId) :=
  Δ₂.foldM (fun Δ x d₂ ↦ do{
    match Δ[x]? with
    | none => pure (Δ.insert x d₂)
    | some d₁ =>
      let A ← get;
      let (s₁, s₂) := (A[d₁]!, A[d₂]!);
      let d ← modifyGet fun A ↦ (A.size, A.push
        {pol := .neg, cons := mergeHeads .neg (s₁.cons ++ s₂.cons), flow := s₁.flow ∪ s₂.flow});
      pure (Δ.insert x d)
  }) Δ₁

/-! One function per typing rule. None of them recurses, so `inferExpr` below only dispatches. -/

-- λ-bound x : [x : α]α
def var (x : String) : Types.M SAutomata := build do{
  let (n, p) ← flowPair;
  pure ({(x, n)}, p)
}

def lit (k : ℕ) : Types.M SAutomata := build do pure ({}, ← alloc .pos [.base k []])

-- λx. e : [Δ]Δ(x) → τ, where Δ(x) = ⊤ (an empty negative state) when x is unused
def abs (x : String) (a : SAutomata) : Types.M SAutomata := build do{
  let (Δ, τ) ← embed a;
  let d ← match Δ[x]? with | some d => pure d | none => alloc .neg [];
  pure (Δ.erase x, ← alloc .pos [.func [d] [τ]])
}

-- e₁ e₂ : [Δ₁ ⊓ Δ₂]α  where  τ₁ ≤ τ₂ → α
def app (a₁ a₂ : SAutomata) : Types.M SAutomata := build do{
  let (Δ₁, τ₁) ← embed a₁;
  let (Δ₂, τ₂) ← embed a₂;
  let (αn, αp) ← flowPair;
  constrain τ₁ (← alloc .neg [.func [τ₂] [αn]]);
  pure (← meetEnv Δ₁ Δ₂, αp)
}

-- ground-type operators k → k' and k → k → k'
def unop (k k' : ℕ) (a : SAutomata) : Types.M SAutomata := build do{
  let (Δ, τ) ← embed a;
  constrain τ (← alloc .neg [.base k []]);
  pure (Δ, ← alloc .pos [.base k' []])
}

def binop (k k' : ℕ) (a₁ a₂ : SAutomata) : Types.M SAutomata := build do{
  let (Δ₁, τ₁) ← embed a₁;
  let (Δ₂, τ₂) ← embed a₂;
  let arg ← alloc .neg [.base k []];
  constrain τ₁ arg;
  constrain τ₂ arg;
  pure (← meetEnv Δ₁ Δ₂, ← alloc .pos [.base k' []])
}

-- if e₁ then e₂ else e₃ : [Δ₁ ⊓ Δ₂ ⊓ Δ₃]α  where  τ₁ ≤ bool, τ₂ ≤ α, τ₃ ≤ α
def cond (a₁ a₂ a₃ : SAutomata) : Types.M SAutomata := build do{
  let (Δ₁, τ₁) ← embed a₁;
  let (Δ₂, τ₂) ← embed a₂;
  let (Δ₃, τ₃) ← embed a₃;
  constrain τ₁ (← alloc .neg [.base boolK []]);
  let (αn, αp) ← flowPair;
  constrain τ₂ αn;
  constrain τ₃ αn;
  pure (← meetEnv Δ₁ (← meetEnv Δ₂ Δ₃), αp)
}

-- {l₁ = e₁, …} : [⊓ Δᵢ]{l₁ : τ₁, …}
def record (fs : List (Symbol × SAutomata)) : Types.M SAutomata := build do{
  let (Δ, ls) ← fs.foldlM (fun (Δ, ls) (l, a) ↦ do{
    let (Δ', τ) ← embed a;
    pure (← meetEnv Δ Δ', (l, [τ]) :: ls)
  }) ({}, []);
  pure (Δ, ← alloc .pos [.rcd ls.reverse])
}

-- e.l : [Δ]α  where  τ ≤ {l : α}
def proj (l : Symbol) (a : SAutomata) : Types.M SAutomata := build do{
  let (Δ, τ) ← embed a;
  let (αn, αp) ← flowPair;
  constrain τ (← alloc .neg [.rcd [(l, [αn])]]);
  pure (Δ, αp)
}

-- let x = e₁ in e₂ : [Δ₁ ⊓ Δ₂]τ₂, keeping Δ₁ in case x is unused
def letIn (a₁ a₂ : SAutomata) : Types.M SAutomata := build do{
  let (Δ₁, _) ← embed a₁;
  let (Δ₂, τ₂) ← embed a₂;
  pure (← meetEnv Δ₁ Δ₂, τ₂)
}

-- fix f. e : [Δ]τ  where  e : [Δ, f : τ_f]τ  and  τ ≤ τ_f
def fixpoint (n : ℕ) (f : String) (a : SAutomata) : Types.M SAutomata := build do{
  let (Δ, τ) ← embed a;
  if let some d := Δ[f]? then constrain τ d;
  pure (Δ.erase f, τ)
}

def freshName : TM String := do pure s!"_uniq.{← mkFreshId}"

mutual
def inferExpr (n : ℕ := 5): (e : Exp) → TM SAutomata
  | .lbool _ => lit boolK
  | .lint _ => lit intK
  | .succ e | .pred e => do unop intK intK (← inferExpr n e)
  | .iszero e => do unop intK boolK (← inferExpr n e)
  | .not e => do unop boolK boolK (← inferExpr n e)
  | .add e₁ e₂ | .mul e₁ e₂ => do binop intK intK (← inferExpr n e₁) (← inferExpr n e₂)
  | .and e₁ e₂ | .or e₁ e₂ => do binop boolK boolK (← inferExpr n e₁) (← inferExpr n e₂)
  | .fvar x => do{
    match (← read)[x]? with
    -- let-bound: the stored automaton is copied into every use, so each use gets fresh variables
    | some a => pure a
    | none => var x
  }
  | .lam _ e => do{
    let x ← freshName;
    abs x (← inferExpr n (open_expr x e))
  }
  | .app e₁ e₂ => do app (← inferExpr n e₁) (← inferExpr n e₂)
  | .ifc e₁ e₂ e₃ => do cond (← inferExpr n e₁) (← inferExpr n e₂) (← inferExpr n e₃)
  | .letE _ e₁ e₂ => do{
    -- simplified before storing, so the copies made at each use stay small
    let a₁ := (← inferExpr n e₁).simplify;
    let x ← freshName;
    letIn a₁ (← withReader (·.insert x a₁) (inferExpr n (open_expr x e₂)))
  }
  | .proj e l => do proj l (← inferExpr n e)
  | .rcd fs => do record (← inferRcd n fs)
  | .fix _ e => do{
    let f ← freshName;
    fixpoint n f (← inferExpr n (open_expr f e))
  }
  | _ => throw "impossible"
termination_by e => e.size
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rw [opening_preserves_size']; omega)

def inferRcd (n : ℕ := 5) : Fields → TM (List (Symbol × SAutomata))
  | .nil => pure []
  | .cons l e fs => do pure ((l, ← inferExpr n e) :: (← inferRcd n fs))
termination_by fs => fs.size
end

def infer (e : Exp) : Except String Typing :=
  (decode_typing <$> SAutomata.simplify <$> (inferExpr 5 e).run {}).run

-- (λx. x) 1
#eval infer (.app (.lam "x" (.bvar 0)) (.lint 1))
-- λx. if x.p then x.q else x.q
#eval infer (.lam "x" (.ifc (.proj (.bvar 0) "p") (.proj (.bvar 0) "q") (.proj (.bvar 0) "q")))
-- let id = λx. x in {a = id 1, b = id true}
#eval infer (.letE "id" (.lam "x" (.bvar 0))
  (.rcd (.cons "a" (.app (.bvar 0) (.lint 1)) (.cons "b" (.app (.bvar 0) (.lbool true)) .nil))))
-- λx. x x
#eval infer (.lam "x" (.app (.bvar 0) (.bvar 0)))
-- f f   (free f)
#eval infer (.app (.fvar "f") (.fvar "f"))
-- fix f. λx. f x
#eval infer (.fix "f" (.lam "x" (.app (.bvar 1) (.bvar 0))))
-- λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))
#eval infer (.lam "f"
  (.app (.lam "x" (.app (.bvar 1) (.lam "v" (.app (.app (.bvar 1) (.bvar 1)) (.bvar 0)))))
        (.lam "x" (.app (.bvar 1) (.lam "v" (.app (.app (.bvar 1) (.bvar 1)) (.bvar 0)))))))
-- 1 + true   (fails)
#eval infer (.add (.lint 1) (.lbool true))

end Typecheck
