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

abbrev Symbol := String
inductive Variance
  | VPos | VNeg | VNegPos | None
  deriving BEq, Repr
structure TyCtx where
  next : Nat := 1
  decls : Std.HashMap ℕ (Symbol × Array Variance) := {}
  byName : Std.HashMap Symbol ℕ := {}

structure TypeChecker.Context where
  env : TyCtx := {}
  lctx : Environment := {}

namespace TypeChecker

abbrev M := ReaderT Context <| StateT TypeChecker.State <| Except Exception

def M.run (lctx : Environment := {}) (x : M α) : Except Exception α := x {lctx}|>.run' {}

def getPolyCtx : M Environment := return (← read).lctx

def getParams : M Environment := return (← get).lparams

def extendPolyCtx (x : String) (t : Typing) : M α → M α :=
  ReaderT.adapt (fun c ↦ {lctx := c.lctx.insert x t})

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
                            | .var _, .sum _ | .sum _, .var _ => true
                            | .bool, .var _ | .var _, .bool => true
                            | .int, .var _|.var _, .int => true
                            | _, _ => false


def bisubst_of_atomic (c : Constraint) : M Bisubst :=
  match c with
    |(.var n, .var m) => if n < m then pure [n ↦ .meet (.var n) (.var m) ⁻]
              else if m < n then pure [m ↦ .join (.var n) (.var m)⁺] else pure emptyBisubst
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
        -- Width subtyping: the record must provide every field that is demanded of it.
        | .rcd pos, .rcd neg => do{
              let pos' := pos.map_of_rcd;
              let neg' := neg.map_of_rcd;
              let prod : Std.HashMap String Constraint ← neg'.foldM (fun rcd l n ↦
              match pos'.get? l with
                | .some p => pure <| rcd.insert l (p, n)
                | .none => Except.error (CannotBiunify (.pos tpos) (.neg tneg))) {};
              pure (prod.values)
        }
        -- Dually, every tag the sum may carry must be handled.
        | .sum pos, .sum neg => do{
              let pos' := pos.map_of_rcd;
              let neg' := neg.map_of_rcd;
              let prod : Std.HashMap String Constraint ← pos'.foldM (fun sum l p ↦
              match neg'.get? l with
                | .some n => pure <| sum.insert l (p, n)
                | .none => Except.error (CannotBiunify (.pos tpos) (.neg tneg))) {};
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

/-- `π₁ ⊔⁻ π₂`: a join of negative types, defined only where it is again a negative type
denoting exactly the union of the two: one side is `⊤`, the sides are equal, or both are
sums (union the tags, join the payloads of shared ones). -/
partial def negJoin : NType → NType → Option NType
  | .top, _ | _, .top => some .top
  | .sum f, .sum g => do
      let merged ← f.toList.mapM fun (l, x) =>
        match lookup g l with
        | some y => (l, ·) <$> negJoin x y
        | none => pure (l, x)
      let extra := g.toList.filter fun (l, _) => (lookup f l).isNone
      pure (.sum (fields_of_list (merged ++ extra)))
  | π₁, π₂ => if π₁ == π₂ then some π₁ else none

/-- The boolean literals matched by an or-tree of boolean literal patterns. -/
def boolLits : Pat → Option (List Bool)
  | .plbool b => some [b]
  | .por p q => (· ++ ·) <$> boolLits p <*> boolLits q
  | _ => none

/-- Typing of an opened pattern: the negative type it demands of the scrutinee, the
variables it binds, and whether every value of that type is known to match it. -/
structure PatTyping where
  ty : NType
  bv : List String
  total : Bool

mutual
/-- `Δ ⊢ p ⇒ π`.  Runs in the direction of `inferExpr`: from what the body demands (`Δ`)
of the variables `p` binds to what `p` demands of the scrutinee, so no biunification is
needed.  Literals type as their base type but are not total: without singleton types,
only an or-tree covering `bool` is. -/
def inferPat (Δ : MonoEnv) (p : Pat) : M PatTyping :=
  match p with
  | .pfvar x => pure ⟨Δ.getD x .top, [x], true⟩
  | .pwild => pure ⟨.top, [], true⟩
  | .plbool _ => pure ⟨.bool, [], false⟩
  | .plint _ => pure ⟨.int, [], false⟩
  | .prcd fs => inferPatFields Δ fs
  | .pinj l q => do{
      let t ← inferPat Δ q;
      pure {t with ty := .sum (.cons l t.ty .nil)}
  }
  | .pand q r => do{
      let t₁ ← inferPat Δ q;
      let t₂ ← inferPat Δ r;
      if t₁.bv.any t₂.bv.contains then Except.error (IllFormedPat p)
      else pure ⟨mkMeet t₁.ty t₂.ty, t₁.bv ++ t₂.bv, t₁.total && t₂.total⟩
  }
  | .por q r =>
      match boolLits p with
        | .some bs => pure ⟨.bool, [], bs.contains true && bs.contains false⟩
        | .none => do{
            let t₁ ← inferPat Δ q;
            let t₂ ← inferPat Δ r;
            if !(t₁.bv.all t₂.bv.contains && t₂.bv.all t₁.bv.contains) then
              Except.error (IllFormedPat p)
            else match negJoin t₁.ty t₂.ty with
              | .some π => pure ⟨π, t₁.bv, t₁.total && t₂.total⟩
              | .none => Except.error (CannotJoin (.neg t₁.ty) (.neg t₂.ty))
        }
  -- `inferExpr` opens every slot before typing the pattern.
  | .pbvar _ => Except.error Impossible
def inferPatFields (Δ : MonoEnv) (fs : PatFields) : M PatTyping :=
  match fs with
  | .nil => pure ⟨.rcd .nil, [], true⟩
  | .cons l q fs' => do{
      let t ← inferPat Δ q;
      let r ← inferPatFields Δ fs';
      match r.ty with
        | .rcd ts =>
            if t.bv.any r.bv.contains then Except.error (IllFormedPat (.prcd fs))
            else pure ⟨.rcd (.cons l t.ty ts), t.bv ++ r.bv, t.total && r.total⟩
        | _ => Except.error Impossible
  }
end

mutual

  def inferExpr : (e : Exp) → M Typing
    | Exp.lbool _ => pure ({}, .bool)
    | Exp.lint _ => pure ({}, .int)
    | Exp.succ e | Exp.pred e => do{
      let (Δ, τ) ← inferExpr e;
      let ξ ← biunify [(τ, .int)];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), .int)
    }
    | Exp.iszero e => do{
      let (Δ, τ) ← inferExpr e;
      let ξ ← biunify [(τ, .int)];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), .bool)
    }
    | Exp.not e => do{
      let (Δ, τ) ← inferExpr e;
      let α ← mkFreshId;
      let ξ ← biunify [(τ, .bool), (.bool, (.var α))];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
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
            pure ty

    }
    | .lam p e => do{
      let xs ← (List.range p.arity).mapM (fun _ ↦ mkFreshVar);
      let (Δ, τ) ← inferExpr (open_expr_slots 0 xs e);
      let t ← inferPat Δ (open_pat_slots 0 xs p);
      -- A pattern lambda has no fallthrough: it must bind every slot and match every
      -- value of the type it demands.
      if !(xs.all t.bv.contains) then Except.error (IllFormedPat p)
      else if !t.total then Except.error (RefutablePat p)
      else pure (xs.foldl Std.HashMap.erase Δ, .arr t.ty τ)
    }
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
    | .and e₁ e₂ | .or e₁ e₂ => do{
      let (Δ₁, τ₁) ← inferExpr e₁;
      let (Δ₂, τ₂) ← inferExpr e₂;
      let α ← mkFreshId;
      let ξ ← biunify [(.arr .bool (.arr .bool .bool), .arr τ₁ (.arr τ₂ (.var α)))];
      let Δ := meet_env Δ₁ Δ₂;
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α))
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
    | .inj l e => do{
      let (Δ, τ) ← inferExpr e;
      let α ← mkFreshId;
      let ξ ← biunify [(τ, .sum (.cons l (.var α) .nil))];
      pure (Δ.map (fun _ τ ↦ apply_neg ξ τ), apply_pos ξ (.var α));
    }
    | .fix _ e => do{

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
        | (rw [opening_slots_preserves_size]; omega)
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

end TypeChecker
