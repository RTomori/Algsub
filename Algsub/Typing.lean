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
  lparams : Environment := {}

structure TypeChecker.Context where
  env : Environment := {}
  lctx : Environment := {}

namespace TypeChecker

abbrev M := ReaderT Context <| StateT TypeChecker.State <| Except Exception

def M.run (lctx : Environment := {}) (x : M α) : Except Exception α := x {lctx}|>.run' {}

def getPolyCtx : M Environment := return (← read).lctx

def getParams : M Environment := return (← get).lparams

def extendPolyCtx (x : String) (t : Typing) : M α → M α := ReaderT.adapt (fun c ↦ {lctx := c.lctx.insert x t})

def mkFreshId : M ℕ := do{
  let s ← get;
  modify (fun s ↦ {s with ngen := s.ngen + 1});
  pure s.ngen
}

def mkFreshVar : M String := do{
  let s ← get;
  modify (fun s ↦ {s with nvargen := s.nvargen + 1});
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


/-- Perhaps sound? since ξ(.var n) = .var n is by no means a subtype of τ, where τ constructed.
-/
def bisubst_of_atomic (c : Constraint) : M Bisubst :=
  match c with
    |(.var n, .var m) => pure [n ↦ .meet (.var n) (.var m) ⁻]
      --if n < m then pure [n ↦ .meet (.var n) (.var m) ⁻]
        --      else if m < n then pure [m ↦ .join (.var n) (.var m)⁺] else pure emptyBisubst
    |(.var n, τ) =>
      if not (isftv_neg n τ) then pure [n ↦ .meet (.var n) τ ⁻]
      else Except.error <| CannotBiunify (.pos (.var n)) (.neg τ)
    |(τ, .var n) => if not (isftv_pos n τ) then
      pure [n ↦ .join (.var n) τ ⁺]
      else Except.error <| CannotBiunify (.pos τ) (.neg (.var n))
    |(τ₁, τ₂) => Except.error <| CannotBiunify (.pos τ₁) (.neg τ₂)

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

/--
#### Proof that Bisubsitution Cannot Solve the Atomic Constraint

∀ρ' ∀ t⁻,t⁺, ∃ ρ ⊧ α ≤ τ, ρ t⁺ ≤ ρ'(ξt⁺), ρ'(ξt⁻)≤ρt⁻.
A counterexample:

-/
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
 /--
 # How to type recursive terms?
 * 次の主張は成り立つだろうか?
 fix f = e : [Δ]τならば，Δ', τ₁，τ₂が存在してe : [f : τ₁, Δ']τ₂かつτ₁ ≤ τ₂。


 | .fix f e => do{
      let s ← mkFreshVar;
      let e' := open_expr s e;
      -- Let [Δ₀]α be typing where dom(Δ₀) = fv(e) \  fv(Π), each assigned to distinct type variables
      let Δ ← getPolyCtx;
      let dom := (fv (.fix f e)).sort \ Δ.keys;
      let α ← mkFreshId;
      let env : MonoEnv ← dom.foldlM (fun Δ x ↦ do{
        let m ← mkFreshId;
        pure (Δ.insert x (.var m))
      }) {};
      let ty@(Δ₀, τ₀) ← extendPolyCtx s (env, .var α) (inferExpr e');
      let ξ ← biunify [(τ₀, .var α)];
      pure ((meet_env env Δ₀).map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      } -/
  def inferExpr : (e : Exp) → M Typing
    | Exp.lbool _ => pure ({}, .bool)
    | Exp.lint _ => pure ({}, .int)
    | Exp.succ e | Exp.pred e => do{
      let (Δ, τ) ← inferExpr e;
      let α ← mkFreshId;
      let ξ ← biunify [(τ, .int)];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), .int)
    }
    | Exp.iszero e => do{
      let (Δ, τ) ← inferExpr e;
      let α ← mkFreshId;
      let ξ ← biunify [(τ, .int)];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), .bool)
    }
    | .fvar x => do{
      let env ← getPolyCtx;
      match env.get? x with
        | .some (Δ, τ) => do
            let (pos, neg) := schemeOccs (Δ, τ);
            let dedup := (pos ++ neg).foldl (fun (s : Std.HashSet ℕ) n ↦ s.insert n) {};
            let fvs : List ℕ := dedup.toList;
            let ξ ← fvs.foldlM (fun ξ n ↦ do
              let m ← mkFreshId;
              pure (ξ.insert n (.var m, .var m))) emptyBisubst;
            pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ τ)
        | .none =>
          do
            let s ← mkFreshId;
            let ty := (Std.HashMap.emptyWithCapacity.insert x (.var s), .var s);
            --modify (fun s => {lparams := params.insert x ty});
            pure ty

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
    | .add e₁ e₂ | .mul e₁ e₂ => do{
      let (Δ₁, τ₁) ← inferExpr e₁;
      let (Δ₂, τ₂) ← inferExpr e₂;
      let α ← mkFreshId;
      let ξ ← biunify [(.arr .int (.arr .int .int), .arr τ₁ (.arr τ₂ (.var α)))];
      let Δ := meet_env Δ₁ Δ₂;
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ),  apply_pos ξ (.var α))
    }
    | .ifc e1 e2 e3 => do{
        let (Δ₁, τ₁) ← inferExpr e1;
        let (Δ₂, τ₂) ← inferExpr e2;
        let (Δ₃, τ₃) ← inferExpr e3;
        let α ← mkFreshId;
        let ξ ← biunify [(τ₁, .bool), (τ₂, .var α), (τ₃, .var α)];
        let Δ := meet_env Δ₃ (meet_env Δ₂ Δ₁);
        pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
      }
      | .letE _ e1 e2 => do{
        let ty@(Δ₁, _)← inferExpr e1;
        let s ← mkFreshVar;
        let e2' := open_expr s e2;
        let (Δ₂, τ₂) ← extendPolyCtx s ty (inferExpr e2');
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
    | .fix f e => do{
      -- A typing rule mimicking Hindley-Milner
      let s ← mkFreshVar;
      let e' := open_expr s e;
      let (Δ, τ) ← inferExpr e';
      match Δ.get? s with
        | .none => Except.error Impossible
        | .some τ' => do{
          let ξ ← biunify [(τ, τ')];
          pure ((Δ.erase s).map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ τ)
        }
    }
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

#eval (inferExpr (.fix "g" (.lam "x" (.add (.app (.bvar 1) (.lint 2)) (.app (.bvar 1) (.lbool False)))))).run
#eval (inferExpr (.fix "f" (.lam "x" (.bvar 1)))).run

#eval (inferExpr ((.lam "g" (.lam "h1" (.lam "y" (.ifc (.lbool False) (.bvar 0) (.app (.bvar 2) (.app (.bvar 3) (.app (.bvar 2) (.app (.bvar 1) (.app (.bvar 3) (.app (.bvar 1) (.app (.bvar 2) (.bvar 0)))))))))))))).run

#eval (inferExpr (.fix "x" (.app (.bvar 0) (.bvar 0)))).run
#eval (inferExpr (.app (.fvar "f") (.fvar "f"))).run
#eval (inferExpr (.add (.fvar "x") (.fvar "y"))).run

#eval (inferExpr (.fix "f" (.lam "g" (.lam "y" (.ifc (.lbool False) (.bvar 0) (.app (.bvar 1) (.app (.bvar 2) (.app (.bvar 1) (.bvar 0))))))))).run
-- FIxpoint combinator
#eval (inferExpr (.lam "f"
  (.app (.lam "x" (.app (.bvar 1) (.lam "v" (.app (.app (.bvar 1) (.bvar 1)) (.bvar 0)))))
              (.lam "x" (.app (.bvar 1) (.lam "v" (.app (.app (.bvar 1) (.bvar 1)) (.bvar 0)))))))).run

#eval (inferExpr (.lam "x" (.ifc (.proj (.bvar 0) "p") (.proj (.bvar 0) "q") (.proj (.bvar 0) "q")))).run
#eval (inferExpr (.fix "f" (.lam "x" (.bvar 0)))).run
end TypeChecker
