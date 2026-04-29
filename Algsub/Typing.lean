import Mathlib.Tactic
import Std.Data.TreeMap
import Std.Data.HashSet
import Algsub.Basic

structure TypeChecker.State where
  ngen : ℕ  := 0
  seen : Std.HashSet Constraint := {}

structure TypeChecker.Context where
  env : Environment := {}
  lparams : List String := []

namespace TypeChecker

abbrev M := ReaderT Context <| StateT TypeChecker.State <| Except Exception

def M.run (env : Environment := {}) (x : M α) : Except Exception α := x {env}|>.run' {}

def getEnv : M Environment := return (← read).env

def extendEnv (n : ℕ) (t : Typing) : M α → M α := ReaderT.adapt (fun c ↦ {env := c.env.insert n t})

def mkFreshId : M ℕ := do{
  let s ← get;
  modify (fun s ↦ {ngen := s.ngen + 1, seen := s.seen});
  pure s.ngen
}
open Exception
/-- Constraint generation -/
def genCst : Constraint →  M (List Constraint)
  | (t1, t2)  =>
    match t1, t2 with
      | .bot, _ => pure []
      | .bool, .bool => pure []
      | .int, .int => pure []
      | .join τ₁ τ₂, τ =>pure [(τ₁,τ), (τ₂, τ)]
      | τ, .meet τ₁ τ₂ => pure [(τ, τ₁), (τ, τ₂)]
      | .rcd f, .rcd g =>
        let df := dom f
         let dg := dom g
          if (dg.all (fun l ↦ Std.HashSet.contains df l))
          then
            let cs' := dg.fold (fun cs l ↦
              match lookup f l, lookup g l with
                |.some τ₁, .some τ₂ => (τ₁, τ₂) :: cs
                | _, _ => []) []
            return cs'
          else Except.error (Exception.CannotBiunify (.pos (PType.rcd f)) (.neg (NType.rcd g)))
      | .arr τ₁ τ₂, .arr σ₁ σ₂ => pure [(σ₁, τ₁), (τ₂, σ₂)]
      | _, _ => Except.error (CannotBiunify (.pos t1) (.neg t2))

partial def biunify (C : List Constraint) : M Bisubst :=
  match C with
    | [] => return Std.TreeMap.empty
    | (.var n, .var m) :: cs =>
      if n == m then biunify cs
      else do{
        let θ := [m ↦ .var n ⁺];
        modify (fun s => {ngen := s.ngen, seen := s.seen.fold (fun seen' t ↦ seen'.insert (apply_to_cst θ t)) {}});
        let σ' ← biunify (cs.map (apply_to_cst θ));
        pure (compose σ' θ)
      }
    | (.var n, τ) :: cs => do{
      if !ftv_neg n τ then
          let θ := [n ↦ NType.meet (.var n) τ ⁻];
          modify (fun s => {ngen := s.ngen, seen := s.seen.fold (fun seen' t ↦ seen'.insert (apply_to_cst θ t)) {}});
          let σ' ← biunify (cs.map (apply_to_cst θ));
          pure (compose σ' θ)
      else Except.error Circular
    }
    | (τ, .var n) :: cs => do{
      if !ftv_pos n τ then
        let θ := [n ↦ PType.join (.var n) τ ⁺];
        modify (fun s => {ngen := s.ngen, seen := s.seen.fold (fun s' t ↦ s'.insert (apply_to_cst θ t)) {}});
        let σ' ← biunify (cs.map (apply_to_cst θ));
        pure (compose σ' θ)
        else Except.error Circular
    }
    | (τ₁, τ₂) :: cs => do{
      let st ← get;
      if (τ₁,τ₂) ∈ st.seen then biunify cs else do{
        modify (fun s =>  {ngen := s.ngen, seen := s.seen.insert (τ₁, τ₂)}) ;
        let cst' ← genCst (τ₁, τ₂);
        biunify (cst' ++ cs)
      }
    }

#eval (genCst (.arr (.var 1) (.arr (.var 0) (.var 0)), .arr (.bool) (.var 2))).run

#eval (biunify [(.bool, .var 1)]).run
mutual
def inferExpr : Exp → M Typing
    | Exp.lbool _ => pure (Std.TreeMap.empty, .bool)
    | Exp.lint _ => pure (Std.TreeMap.empty, .int)
    | .bvar n => do{
      let env ← getEnv;
      match env.get? n with
        | .some ty => pure ty
        | .none => do{
            let s ← mkFreshId;
            pure (Std.TreeMap.empty.insert n (.var s), PType.var s)
        }
      }
      | .lam _ e => do{
        let (Δ, τ') ← inferExpr e;
        let n := Δ.size - 1;
        match Δ.get? n with
          | .none =>
              let n ← mkFreshId;
              pure (Δ, .arr (.var n) τ')
          | .some τ =>
              let env' := Δ.erase n;
              pure (env', .arr τ τ')
      }
      | .app e1 e2 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let α ← mkFreshId;
        let ξ ← biunify [(τ₁, .arr τ₂ (.var α))];
        let Δ := join_env Δ₂ Δ₁;
        pure (Δ.foldr (fun i τ g ↦ g.insert i (apply_neg ξ τ)) {}, apply_pos ξ (.var α))
      }
      | .ifc e1 e2 e3 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let (Δ₃, τ₃) ← inferExpr e3;
        let α ← mkFreshId;
        let ξ ← biunify [(τ₁, .bool),(τ₂, .var α), (τ₃, .var α)];
        let Δ := join_env Δ₃ (join_env Δ₂ Δ₁);
        pure (Δ.foldr (fun i τ g ↦ g.insert i (apply_neg ξ τ)) {}, apply_pos ξ (.var α))
      }
      | .letE e1 e2 => do{
        let ty@(Δ₁, _)← inferExpr e1;
        let n := numBinders e2 + 1;
        let (Δ₂, τ₂) ← extendEnv n ty (inferExpr e2);
        let Δ := join_env Δ₁ Δ₂;
        pure (Δ, τ₂)
      }
      | .proj e l => do{
        let (Δ,τ) ← inferExpr e;
        let α ← mkFreshId;
        let ξ ← biunify [(τ, .rcd (.nil l (.var α)))];
        pure (Δ.foldr (fun i τ g ↦ g.insert i (apply_neg ξ τ)) {}, apply_pos ξ (.var α))
      }
      | .rcd f => inferRcd f
      | _ => Except.error Impossible
def inferRcd : Fields → M Typing
  | .nil l e  => do{
    let (Δ, τ) ← inferExpr e;
    pure (Δ, .rcd (.nil l τ))
  }
  | .cons l e fs => do{
    let (Δ₁, τ) ← inferExpr e;
    let (Δ₂, t) ←inferRcd fs;
    match t with
      | .rcd τ' => do{
              let Δ := join_env Δ₁ Δ₂;
              pure (Δ, .rcd (.cons l τ τ'))}
      | _ => Except.error Impossible
  }
end
#eval (inferExpr (.lam "x" (.ifc (.proj (.bvar 0) "p") (.proj (.bvar 0) "q") (.proj (.bvar 0) "q")))).run
#eval (inferExpr (.proj (.bvar 0) "foo")).run
end TypeChecker
