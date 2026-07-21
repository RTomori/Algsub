import Mathlib.Tactic
import Std.Data.HashMap
import Std.Data.HashSet
import Algsub.Basic

open Lean hiding Environment Exception
open Meta

structure TypeChecker.State where
  ngen : ℕ  := 0
  nvargen : ℕ := 0
  seen : Std.HashSet Constraint := {}

structure TypeChecker.Context where
  env : Environment := {}
  lparams : List String := []

namespace TypeChecker

abbrev M := ReaderT Context <| StateT TypeChecker.State <| Except Exception

def M.run (env : Environment := {}) (x : M α) : Except Exception α := x {env}|>.run' {}

def getEnv : M Environment := return (← read).env

def extendEnv (x : String) (t : Typing) : M α → M α := ReaderT.adapt (fun c ↦ {env := c.env.insert x t})

def mkFreshId : M ℕ := do{
  let s ← get;
  modify (fun s ↦ {ngen := s.ngen + 1});
  pure s.ngen
}

def mkFreshVar : M String := do{
  let s ← get;
  modify (fun s ↦ {nvargen := s.nvargen + 1});
  pure (("_uniq." ++ s.nvargen.repr))
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
                            | .int, .var _|.var _, .int => true
                            | _, _ => false

def bisubst_of_atomic (c : Constraint) : M Bisubst :=
  match c with
    |(.var n, .var m) => pure [n ↦ .meet (.var n) (.var m) ⁻]
      --if n < m then pure [n ↦ .meet (.var n) (.var m) ⁻]
        --      else if m < n then pure [m ↦ .join (.var n) (.var m)⁺] else pure emptyBisubst
    |(.var n, τ) =>
      if not (isftv_neg n τ) then pure [n ↦ .meet (.var n) τ ⁻]
      else Except.error Impossible
    |(τ, .var n) => if not (isftv_pos n τ) then
      pure [n ↦ .join (.var n) τ ⁺]
      else Except.error Impossible
    |(_, _) => Except.error Impossible

def subi : Constraint →  M (List Constraint)
  | (tpos, tneg) =>
      match tpos, tneg with
        | .join τ₁ τ₂, τ => pure [(τ₁, τ), (τ₂,τ)]
        | τ, .meet τ₁ τ₂ => pure [(τ, τ₁), (τ,τ₂)]
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
        | .bot, _ => pure []
        | _, .top => pure []
        |_, _ => Except.error (CannotBiunify (.pos tpos) (.neg tneg))

def HashSet.map
  [BEq α] [Hashable α] [BEq β] [Hashable β] (s : Std.HashSet α)
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
        -- Record `c` as solved *before* rewriting by θ, then map the whole cache
        -- through θ so it stays in the same coordinates as the rewritten worklist.
        -- Without inserting `c`, a repeated atomic constraint α ≤ τ is solved again
        -- and conjoins τ to α's bound a second time, producing duplicate ⊓/⊔ terms.
        modify (fun s ↦ {s with seen := HashSet.map (s.seen.insert c) (apply_to_cst θ) });
        let σ ← biunify (C.map (apply_to_cst θ));
        pure (compose σ θ)
     else
      let cst ←subi c;
      modify (fun s ↦ {s with seen := s.seen.insert c});
      biunify (cst ++ C);
    }


mutual
  def inferExpr : Exp → M Typing
    | Exp.lbool _ => pure ({}, .bool)
    | Exp.lint _ => pure ({}, .int)
    | .fvar x => do{
      let env ← getEnv;
      match env.get? x with
        | .some (Δ, τ) => do
            let (pos, neg) := schemeOccs (Δ, τ);
            let dedup := (pos ++ neg).foldl (fun (s : Std.HashSet ℕ) n ↦ s.insert n) {};
            let fvs : List ℕ := dedup.toList;
            let ξ ← fvs.foldlM (fun ξ n ↦ do
              let m ← mkFreshId;
              pure (ξ.insert n (.var m, .var m))) emptyBisubst;
            pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ τ)
        | .none => do
            let s ← mkFreshId;
            pure (Std.HashMap.emptyWithCapacity.insert x (.var s), .var s)
    }
    | .lam _ e => do
      let s ← mkFreshVar;
      let e' := open_expr s e;
      let (Δ, τ') ← inferExpr e';
      match Δ.get? s with
        | .none =>
            let a ← mkFreshId;
            pure (Δ, .arr (.var a) τ')
        | .some τ =>
            pure (Δ.erase s, .arr τ τ')
    | .app e₁ e₂ => do{
      let (Δ₁, τ₁) ← inferExpr e₁;
      let (Δ₂, τ₂) ← inferExpr e₂;
      let α ← mkFreshId;
      let ξ ← biunify [(τ₁, .arr τ₂ (.var α))];
      let Δ := meet_env Δ₁  Δ₂;
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
    }
    | .ifc e1 e2 e3 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let (Δ₃, τ₃) ← inferExpr e3;
        let α ← mkFreshId;
        let ξ ← biunify [(τ₁, .bool),(τ₂,.var α),  (τ₃, .var α)];
        let Δ := meet_env Δ₃ (meet_env Δ₂ Δ₁);
        pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      }
      | .letE x e1 e2 => do{
        let ty@(Δ₁, _)← inferExpr e1;
        let (Δ₂, τ₂) ← extendEnv x ty (inferExpr e2);
        let Δ := meet_env Δ₁ Δ₂;
        pure (Δ, τ₂)
      }
      | .proj e l => do{
        let (Δ,τ) ← inferExpr e;
        let α ← mkFreshId;
        let ξ ← biunify [(τ, .rcd (.cons l (.var α) .nil))];
        pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      }
    | .rcd f => inferRcd f
    |_ => Except.error Impossible
    termination_by e => e.size
    decreasing_by
      all_goals simp_wf
      all_goals first
        | omega
        | (rw [opening_preserves_size']; omega)
  def inferRcd : Fields → M Typing
    | .nil => pure ({}, .rcd .nil)
    | .cons l e fs => do{
    let (Δ₁, τ) ← inferExpr e;
    let (Δ₂, t) ←inferRcd fs;
    match t with
      | .rcd τ' => do{
              let Δ := meet_env Δ₂ Δ₁;
              pure (Δ, .rcd (.cons l τ τ'))}
      | _ => Except.error Impossible
  }
  termination_by fs => fs.size
end



def infer (e : Exp) : M Typing := do
  let t ← inferExpr e
  pure t
#eval (inferExpr (.lam "x" (.bvar 0))).run
#eval (inferExpr (.letE "f" (.lam "x" (.bvar 0)) (.app (.app (.fvar "f") (.fvar "f")) (.lbool false)))).run
#eval (inferExpr
  (.letE "f"
    (.lam "x" (.bvar 0))
      (.letE "_" (.app (.app (.fvar "f") (.fvar "f")) (.lbool false)) (.ifc (.app (.fvar "f") (.lbool true)) (.lbool true) (.lbool false))))).run
end TypeChecker
