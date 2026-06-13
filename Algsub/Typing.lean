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
def atomic (c : Constraint) : Bool :=
  match c with
    | (t1, t2) =>
        match t1, t2 with
                            | .var _, .arr _ _ | .var _, .rcd _ | .var _, .var _ => true
                            | .arr _ _, .var _| .rcd _ , .var _ => true
                            | .bool, .var _ | .var _, .bool => true
                            | _, _ => false

def bisubst_of_atomic (c : Constraint) : M Bisubst :=
  match c with
    |(.var n, .var m) => if n < m then pure [n ↦ .meet (.var n) (.var m) ⁻]
              else if m < n then pure [m ↦ .join (.var n) (.var m)⁺] else pure emptyBisubst
    |(.var n, τ) =>
      if (ftv_neg n τ) then do{
        let β ← mkFreshId;
        pure [n ↦ .fix β (.meet (.var n) (apply_neg [n ↦ .var β⁻] τ))⁻]
      } else pure [n ↦ .meet (.var n) τ ⁻]
    |(τ, .var n) => if ftv_pos n τ then do{
      let β ← mkFreshId;
      pure [n ↦ .fix β (.join (.var n) (apply_pos [n ↦ .var β⁺] τ))⁺]
    } else pure [n ↦ .join (.var n) τ ⁺]
    |(_, _) => Except.error Impossible

def subi : Constraint →  M (List Constraint)
  | (tpos, tneg) =>
      match tpos, tneg with
        | .arr τ₁ τ₂, .arr σ₁ σ₂ => pure [(σ₁, τ₁), (τ₂, σ₂)]
        | .bool, .bool | .int, .int => pure []
        | .rcd pos, .rcd neg => do{
              let pos' := pos.map_of_rcd;
              let neg' := neg.map_of_rcd;
              let prod : Std.HashMap String Constraint := pos'.map (fun l τ ↦ (τ, neg'.get! l)) ;
              pure (prod.values)
        }
        | .fix n τ, τ' => pure [(apply_pos [n↦.fix n τ⁺] τ, τ')]
        | τ, .fix n τ' => pure [(τ, apply_neg [n↦ .fix n τ'⁻] τ')]
        | .join τ₁ τ₂, τ => pure [(τ₁, τ), (τ₂,τ)]
        | τ, .meet τ₁ τ₂ => pure [(τ, τ₁), (τ,τ₂)]
        | .bot, _ => pure []
        | _, .top => pure []
        |_, _ => Except.error (CannotBiunify (.pos tpos) (.neg tneg))

def HashSet.map
  [BEq α] [Hashable α][BEq β] [Hashable β] (s : Std.HashSet α)
  (f : α → β) : Std.HashSet β :=   s.fold (fun acc x => acc.insert (f x)) ∅

partial def biunify (C : List Constraint) : M Bisubst :=
  match C with
    | [] => pure emptyBisubst
    | c :: C => do{
      let st ← get;
      if c ∈ st.seen
      then biunify C
      else if atomic c then
        let θ ← bisubst_of_atomic c;
        modify (fun s ↦ {seen := HashSet.map (s.seen) (apply_to_cst θ) });
        let σ ← biunify (C.map (apply_to_cst θ));
        pure (compose σ θ)
     else
      let cst ←subi c;
      modify (fun s ↦ {seen := s.seen.insert c});
      biunify (cst ++ C);
    }

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
              Except.error Impossible
          | .some τ =>
              pure (Δ.erase n, .arr τ τ')
      }
      | .app e1 e2 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let α ← mkFreshId;
        let ξ ← biunify [(τ₁, .arr τ₂ (.var α))];
        let Δ := meet_env Δ₁  Δ₂;
        pure (Δ.map (fun i τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      }
      | .ifc e1 e2 e3 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let (Δ₃, τ₃) ← inferExpr e3;
        let β ← mkFreshId;
        let ξ ← biunify [(τ₁, .bool), (τ₂, .var β), (τ₃,.var β)];
        let Δ := meet_env Δ₃ (meet_env Δ₂ Δ₁);
        pure (Δ.map (fun i τ ↦ apply_neg ξ τ), apply_pos ξ (.var β))
      }
      | .letE e1 e2 => do{
        let ty@(Δ₁, _)← inferExpr e1;
        let n := numBinders e2 + 1;
        let (Δ₂, τ₂) ← extendEnv n ty (inferExpr e2);
        let Δ := meet_env Δ₁ Δ₂;
        pure (Δ, τ₂)
      }
      | .proj e l => do{
        let (Δ,τ) ← inferExpr e;
        let α ← mkFreshId;
        let ξ ← biunify [(τ, .rcd (.cons l (.var α) .nil))];
        pure (Δ.map (fun i τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      }
      | .rcd f => inferRcd f
      | _ => Except.error Impossible
def inferRcd : Fields → M Typing
  | .nil l e  => do{
    let (Δ, τ) ← inferExpr e;
    pure (Δ, .rcd (.cons l τ (.nil)))
  }
  | .cons l e fs => do{
    let (Δ₁, τ) ← inferExpr e;
    let (Δ₂, t) ←inferRcd fs;
    match t with
      | .rcd τ' => do{
              let Δ := meet_env Δ₂ Δ₁;
              pure (Δ, .rcd (.cons l τ τ'))}
      | _ => Except.error Impossible
  }
end
#eval (biunify [(.var 0, .arr (.var 0) (.var 0))]).run
#eval (inferExpr ( .lam "x" (.ifc (.proj (.bvar 0) "p") (.proj (.bvar 0) "q") (.proj (.bvar 0) "q") ))).run
/- -/
#eval (inferExpr ((.proj (.bvar 1) "p"))).run

end TypeChecker
