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

-- [Δ₁]τ₁ ≤∀ [Δ₂]τ₂, i.e. a₁ is at least as general as a₂: some substitution ρ of a₁'s type
-- variables has ρ(τ₁) ≤ τ₂ and Δ₂(x) ≤ ρ(Δ₁(x)) for each x bound by Δ₁, with Δ₂(x) = ⊤ where Δ₂
-- leaves x out. a₂'s variables stay rigid.
-- Simplifying leaves one head per constructor and singleton successor sets, as `subsume_ptype`
-- expects. From the roots, `subsume_ptype` / `subsume_ntype` match heads, and the pairs they visit
-- relate each state of a₁ to the states of a₂ it must instantiate to. That leaves the variables:
-- one on a flow edge n ⇝ p of a₁ is bounded below by n's partners and above by p's, so ρ exists
-- iff m ⇝ u is admissible for every such edge, partner m of n and partner u of p.
def subsume_typing (a₁ a₂ : SAutomata) : Types.M Bool := do{
  let (a₁, a₂) := (a₁.simplify, a₂.simplify);
  let ((Δ₁, τ₁, Δ₂, τ₂, top), A) ← (show BuildM _ from do{
    let (Δ₁, τ₁) ← embed a₁;
    let (Δ₂, τ₂) ← embed a₂;
    pure (Δ₁, τ₁, Δ₂, τ₂, ← alloc .neg [])
  }).run #[];
  let A := A.toVector;
  -- [TODO] prove that simplified typings are reduced, as for `check`
  if hA : reduced_typing A then do{
    let τ₁ ← checkId _ τ₁;
    let τ₂ ← checkId _ τ₂;
    let Δ ← Δ₁.toList.mapM fun (x, d₁) ↦ do pure (← checkId _ (Δ₂.getD x top), ← checkId _ d₁);
    -- each pair is (smaller, larger), so a₁'s state comes first in the result, a₂'s in the env
    let some seen ← tryCatch (do{
        let ⟨seen, _⟩ ← subsume_ptype A hA {} τ₁ τ₂;
        some <$> Δ.foldlM (fun seen (d₂, d₁) ↦ do pure (← subsume_ntype A hA seen d₂ d₁).1) seen
      }) (fun _ ↦ pure none) | pure false;
    let partners : Std.HashMap StateId (List StateId) := seen.fold (fun m (q, q') ↦
      let (l, r) := if q < a₁.scheme.size then (q, q') else (q', q);
      m.alter l (some <| r :: ·.getD [])) {};
    let bounds := partners.toList.flatMap fun (n, ms) ↦ A[n]!.flow.toList.flatMap fun p ↦
      ms.flatMap fun m ↦ (partners.getD p []).map (m, ·);
    -- the pairs found admissible so far stay valid for later edges
    let mut s := {};
    for (m, u) in bounds do{
      let some ⟨s', _⟩ := admissible A s (← checkId _ m) (← checkId _ u) | return false;
      s := s'
    }
    pure true
  } else throw "subsume_typing: simplified automata should be reduced"
}
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
-- []⊥, the bottom of ≤∀: it requires nothing of the environment, and f : ⊥ says f never returns
def bot_typing : SAutomata := {scheme := #[create_state .pos [] []], env := {}, res := 0}
-- fix f. e : [Δ]τ  where  e : [Δ, f : τ_f]τ  and  τ ≤ τ_f
-- [TODO] Rewrite to parameterised Milner-Mycroft
def fixpoint (f : String) (a : SAutomata) : Types.M SAutomata := build do{
  let (Δ, τ) ← embed a;
  if let some d := Δ[f]? then constrain τ d;
  pure (Δ.erase f, τ)
}

def freshName : TM String := do pure s!"_uniq.{← mkFreshId}"

mutual
def inferExpr (n : ℕ := 5) (polrec : Bool := True): (e : Exp) → TM SAutomata
  | .lbool _ => lit boolK
  | .lint _ => lit intK
  | .succ e | .pred e => do unop intK intK (← inferExpr n polrec e)
  | .iszero e => do unop intK boolK (← inferExpr n polrec e)
  | .not e => do unop boolK boolK (← inferExpr n polrec e)
  | .add e₁ e₂ | .mul e₁ e₂ => do binop intK intK (← inferExpr n polrec e₁) (← inferExpr n polrec e₂)
  | .and e₁ e₂ | .or e₁ e₂ => do binop boolK boolK (← inferExpr n polrec e₁) (← inferExpr n polrec e₂)
  | .fvar x => do{
    match (← read)[x]? with
    | some a => pure a
    | none => var x
  }
  | .lam _ e => do{
    let x ← freshName;
    abs x (← inferExpr n polrec (open_expr x e))
  }
  | .app e₁ e₂ => do app (← inferExpr n polrec e₁) (← inferExpr n polrec e₂)
  | .ifc e₁ e₂ e₃ => do cond (← inferExpr n polrec e₁) (← inferExpr n polrec e₂) (← inferExpr n polrec e₃)
  | .letE _ e₁ e₂ => do{
    -- simplified before storing, so the copies made at each use stay small
    let a₁ := (← inferExpr n polrec e₁).simplify;
    let x ← freshName;
    letIn a₁ (← withReader (·.insert x a₁) (inferExpr n polrec (open_expr x e₂)))
  }
  | .proj e l => do proj l (← inferExpr n polrec e)
  | .rcd fs => do record (← inferRcd n polrec fs)
  | .fix x e => if polrec then do{
        let f ← freshName;
        let e' := open_expr f e;
        -- Kleene iteration σₖ₊₁ = F(σₖ) from []⊥, where F(σ) types e with f : σ. Each σₖ lies below
        -- the lfp in ≤∀, so it types `fix f. e` only once F(σₖ) ≤∀ σₖ. Every round passes the same
        -- `n`, so that nested fixes are typed alike and F stays one function.
        let mut σ := bot_typing;
        for _ in [:n] do{
          let σ' := (← withReader (·.insert f σ) (inferExpr n polrec e')).simplify;
          if ← subsume_typing σ' σ then return σ';
          σ := σ'.simplify
        };
        throw s!"failed to reach fixpoint within {n} steps; typing before termination: {repr (decode_typing σ)}";
        -- the chain need not reach a fixpoint, and σ is none: fall back to monomorphic recursion,
        -- which is sound by itself
  } else do {
      let f ← freshName;
      fixpoint f (← inferExpr n polrec (open_expr f e));
  }
  | _ => throw "impossible"
termination_by e => e.size
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rw [opening_preserves_size']; omega)

def inferRcd (n : ℕ := 5) (polrec : Bool := True): Fields → TM (List (Symbol × SAutomata))
  | .nil => pure []
  | .cons l e fs => do pure ((l, ← inferExpr n polrec e) :: (← inferRcd n polrec fs))
termination_by fs => fs.size
end

def infer (e : Exp) (allowRec : Bool := False): Except String Typing := do{
  let (Δ, τ) ← (decode_typing <$> SAutomata.simplify <$> (inferExpr 3 False e).run {}).run
  if allowRec then pure (Δ, τ)
  else if (Δ.any (fun _ t ↦ hasRecType t) || hasRecType τ)
    then throw s!"Recursive types not allowed" else pure (Δ, τ)
}
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
#eval infer (.fix "f" (.lam "x" (.add (.app (.bvar 1) (.lint 1)) (.app (.bvar 1) (.lbool True)))))
#eval infer (.add (.fvar "x") (.lint 1))
#eval open_expr "g" (.lam "x" (.bvar 0))
#eval decode_typing bot_typing

end Typecheck
