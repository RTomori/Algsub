import Mathlib.Tactic
import Mathlib.Control.Traversable.Basic
import Std.Data.TreeMap
import Std.Data.HashSet
mutual
  inductive Exp : Type where
  /-- Fixme : translate to locally nameless -/
    | bvar : ℕ → Exp
    | fvar : String → Exp
    | const : String → Exp
    | app : Exp → Exp → Exp
    | lbool : Bool → Exp
    | lint : Int → Exp
    | lam : String → Exp → Exp
    | fix : String → Exp → Exp
    | rcd : Fields → Exp
    | ifc : Exp → Exp → Exp → Exp
    | letE : String → Exp → Exp → Exp
    | seq : Exp → Exp → Exp
    | succ : Exp → Exp
    | pred : Exp → Exp
    | iszero : Exp → Exp
    | add : Exp → Exp → Exp
    | mul : Exp → Exp → Exp
    | not : Exp → Exp
    | and : Exp → Exp → Exp
    | or : Exp → Exp → Exp
    | proj : Exp → String → Exp
    deriving BEq, Repr
  inductive Fields : Type where
    | nil : Fields
    | cons : String → Exp → Fields → Fields
    deriving BEq, Repr
end


mutual
def fv : Exp → Std.HashSet String
  | .bvar _ | .lint _ | .lbool _ | .const _ => {}
  | .iszero t | .pred t | .succ t | .not t => fv t
  | .mul e1 e2 | .add e1 e2 | .or e1 e2 | .and e1 e2=> fv e1 ∪ fv e2
  | .fvar x => {x}
  | .app t1 t2 => fv t1 ∪ fv t2
  | .lam _ t => fv t
  | .fix _  t => fv t
  | .seq t1 t2 => fv t1 ∪ fv t2
  | .ifc t1 t2 t3 => fv t1 ∪ fv t2 ∪ fv t3
  | .rcd fs => fv_rcd fs
  | .proj e _ => fv e
  | .letE _ e1 e2 => fv e1 ∪ fv e2

def fv_rcd : Fields → Std.HashSet String
  | .nil => {}
  | .cons _ e fs => fv e ∪ fv_rcd fs
end

mutual
def numBinders : Exp → ℕ
  | .bvar _|.lbool _ | .lint _ | .fvar _ | .const _=> 0
  | .lam _ e | .iszero e  => numBinders e + 1
  | .letE _ e1 e2 => max (numBinders e2 + 1) (numBinders e1)
  | .ifc e1 e2 e3 => max (max (numBinders e1) (numBinders e2)) (numBinders e3)
  | .fix _ e => numBinders e + 1
  | .app e1 e2=> max (numBinders e1) (numBinders e2)
  | .add e1 e2| .mul e1 e2 | .and e1 e2 | .or e1 e2=> max (numBinders e1) (numBinders e2)
  | .seq e1 e2 => max (numBinders e1) (numBinders e2)
  | .proj e _ => numBinders e
  | .pred e | .succ e | .not e => numBinders e
  | .rcd f => numBinders_rcd f

def numBinders_rcd : Fields → ℕ
  | .nil => 0
  | .cons _ e fs => max (numBinders e) (numBinders_rcd fs)
end

mutual
@[simp]
def Exp.size : Exp → ℕ
  | .bvar _ | .fvar _ | .lbool _ | .lint _ | .const _ => 1
  | .app e1 e2 | .seq e1 e2  | .add e1 e2 | .mul e1 e2  | .and e1 e2 | .or e1 e2
      => 1 + e1.size + e2.size
  | .lam _ e | .fix _ e| .iszero e | .pred e | .succ e   | .not e   => 1 + e.size
  | .ifc e1 e2 e3   => 1 + e1.size + e2.size + e3.size
  | .letE _ e1 e2   => 1 + e1.size + e2.size
  | .proj e _       => 1 + e.size
  | .rcd f          => 1 + f.size
@[simp]
def Fields.size : Fields → ℕ
  | .nil          => 1
  | .cons _ e fs  => 1 + e.size + fs.size
end

mutual
@[simp]
def open_expr_at (k : ℕ) (x : String) : Exp → Exp
  | .bvar i => if i == k then (.fvar x) else (.bvar i)
  | .fvar y => .fvar y
  | .lbool b => .lbool b
  | .lint n => .lint n
  | .const c => .const c
  | .iszero t => .iszero (open_expr_at k x t)
  | .pred t => .pred (open_expr_at k x t)
  | .succ t => .succ (open_expr_at k x t)
  | .not t => .not (open_expr_at k x t)
  | .app t₁ t₂ => .app (open_expr_at k x t₁) (open_expr_at k x t₂)
  | .add t₁ t₂ => .add (open_expr_at k x t₁) (open_expr_at k x t₂)
  | .mul t₁ t₂ => .mul (open_expr_at k x t₁) (open_expr_at k x t₂)
  | .and t₁ t₂ => .and (open_expr_at k x t₁) (open_expr_at k x t₂)
  | .or t₁ t₂ => .or (open_expr_at k x t₁) (open_expr_at k x t₂)
  | .seq t₁ t₂ => .seq (open_expr_at k x t₁) (open_expr_at (k + 1) x t₂)
  | .lam y t => .lam y (open_expr_at (k + 1) x t)
  | .ifc t₁ t₂ t₃ => .ifc (open_expr_at k x t₁) (open_expr_at k x t₂) (open_expr_at k x t₃)
  | .fix y t => .fix y (open_expr_at (k + 1) x t)
  | .proj f y => .proj (open_expr_at k x f) y
  | .letE y t₁ t₂ => .letE y (open_expr_at k x t₁) (open_expr_at (k + 1) x t₂)
  | .rcd f => .rcd (open_rcd_at k x f)
  @[simp]
def open_rcd_at (k : ℕ) (x : String) : Fields → Fields
  | .nil => .nil
  | .cons l e fs => .cons l (open_expr_at k x e) (open_rcd_at k x fs)
end
@[elab_as_elim]
theorem Exp.induct
  {motive : Exp → Prop}
  (base_bool : ∀ b, motive (.lbool b))
  (base_int : ∀ n, motive (.lint n))
  (base_const : ∀ c, motive (.const c))
  (base_bvar : ∀ n, motive (.bvar n))
  (base_fvar : ∀ s, motive (.fvar s))
  (base_nil : motive (.rcd .nil))
  (ind_lam : ∀ x e, motive e → motive (.lam x e))
  (ind_app : ∀ e1 e2, motive e1 → motive e2 → motive (.app e1 e2))
  (ind_seq : ∀ e1 e2, motive e1 → motive e2 → motive (.seq e1 e2))
  (ind_fix : ∀ x e, motive e → motive (.fix x e))
  (ind_if : ∀ e1 e2 e3, motive e1 → motive e2 → motive e3 → motive (.ifc e1 e2 e3))
  (ind_let : ∀ x e1 e2, motive e1 → motive e2 → motive (.letE x e1 e2))
  (ind_cons : ∀ x e fs, motive e → motive (.rcd fs) → motive (.rcd (.cons x e fs)))
  (ind_proj : ∀ e x, motive e → motive (.proj e x))
  (ind_succ : ∀ e, motive e → motive (.succ e))
  (ind_pred : ∀ e, motive e → motive (.pred e))
  (ind_iszero : ∀ e, motive e → motive (.iszero e))
  (ind_add : ∀ e1 e2, motive e1 → motive e2 → motive (.add e1 e2))
  (ind_mul : ∀ e1 e2, motive e1 → motive e2 → motive (.mul e1 e2))
  (ind_not : ∀ e, motive e → motive (.not e))
  (ind_and : ∀ e1 e2, motive e1 → motive e2 → motive (.and e1 e2))
  (ind_or : ∀ e1 e2, motive e1 → motive e2 → motive (.or e1 e2))
  (e : Exp) : motive e :=
  Exp.rec (motive_1 := motive) (motive_2 := fun fs => motive (.rcd fs))
    base_bvar base_fvar base_const ind_app base_bool base_int ind_lam ind_fix
    (fun _f ih => ih)
    ind_if
    ind_let
    ind_seq
    ind_succ
    ind_pred
    ind_iszero ind_add ind_mul ind_not ind_and ind_or ind_proj
    base_nil ind_cons
    e
/-
mutual
@[elab_as_elim]
theorem PType.induct
  {motive : Ty → Prop}
  (base_pvar : ∀ n, motive (.pos (.var n)))
  (base_bool : motive (.pos (.bool)))
  (base_int : motive (.pos (.int)))
  (base_bot : motive (.pos (.bot)))
  (base_nil : motive (.pos (.rcd .nil)))
  (ind_arr : ∀ τ₁ τ₂, motive (.neg τ₁) → motive (.pos τ₂) → motive (.pos (.arr τ₁ τ₂)))
  (ind_join : ∀ τ₁ τ₂, motive (.pos τ₁) → motive (.pos τ₂) → motive (.pos (.join τ₁ τ₂)))
  (ind_rcd : ∀ x τ τ', motive (.pos τ) → motive (.pos (.rcd τ'))
    → motive (.pos (.rcd (.cons x τ τ'))))
  (ind_fix : ∀n τ, motive (.pos τ) → motive (.pos (.fix n τ)))
  (τ : PType) : motive (.pos τ) := sorry
 /--  PType.rec
   (motive_1 := motive)
   (motive_2 := fun p => motive (.pos p))
   (motive_3 := fun n => motive (.neg n))
   (motive_4 := fun fs => motive (.pos (.rcd fs)))
   (motive_5 := fun fs => motive (.neg (.rcd fs)))
   (fun p h => h) (fun n h => h) base_bool base_int base_pvar
   ind_arr
   (fun a h => match a with
                | .nil => base_nil | .cons x t ts => h) ind_join ind_fix base_bot
   (NType.induct _ _ _ _ _ _ _ _ _ NType.bool) _ _ _ _ _ _ _ _ _ _ _ τ
--/
theorem NType.induct
  {motive : Ty → Prop}
  (base_nvar : ∀ n, motive (.neg (.var n)))
  (base_bool : motive (.neg (.bool)))
  (base_int : motive (.neg (.int)))
  (base_top : motive (.neg (.top)))
  (base_nil : motive (.neg (.rcd .nil)))
  (ind_arr : ∀ τ₁ τ₂, motive (.pos τ₁) → motive (.neg τ₂) → motive (.neg (.arr τ₁ τ₂)))
  (ind_meet : ∀ τ₁ τ₂, motive (.neg τ₁) → motive (.neg τ₂) → motive (.neg (.meet τ₁ τ₂)))
  (ind_rcd : ∀ x τ τ', motive (.neg τ) → motive (.neg (.rcd τ')) → motive (.neg (.rcd (.cons x τ τ'))))
  (ind_fix : ∀ n τ, motive (.neg τ) → motive (.neg (.fix n τ)))
  (τ : NType) : motive (.neg τ) := sorry
  /-NType.rec
  (motive_1 := motive)
  (motive_2 := fun p => motive (.pos p))
  (motive_3 := fun n => motive (.neg n))
  (motive_4 := fun fs => motive (.pos (.rcd fs)))
  (motive_5 := fun fs => motive (.neg (.rcd fs)))
  (fun _ h => h) (fun _ h => h)
  _ _ _ _ _ _ _ _ base_bool base_int base_nvar ind_arr
  (fun a h => match a with |.nil => base_nil | .cons x t ts => h)
  ind_meet base_top ind_fix _ _ _ _ τ
-/
end
-/

theorem opening_preserves_size : ∀ k x e, (open_expr_at k x e).size = e.size := by
  intros k x e
  induction e using Exp.induct generalizing k with
    | base_bool b | base_int n | base_fvar x | base_nil | base_const c => simp
    | base_bvar m =>
        by_cases h : m == k <;> simp[h]
    | ind_lam y e h =>simp only [open_expr_at, Exp.size, h]
    | ind_app e1 e2 h1 h2 =>
      simp only [open_expr_at, Exp.size, h1,h2]
    | ind_seq e1 e2 h1 h2 =>
      simp only  [open_expr_at, Exp.size, h1, h2]
    | ind_fix y e h => simp only [open_expr_at, Exp.size, h]
    | ind_pred e h | ind_succ e h | ind_iszero e h => simp[h]
    | ind_add e1 e2 h1 h2 | ind_mul e1 e2 h1 h2 | ind_and e1 e2 h1 h2  | ind_or e1 e2 h1 h2
        => simp[open_expr_at, Exp.size, h1, h2]
    | ind_if e1 e2 e3 h1 h2 h3 => simp only [open_expr_at, Exp.size, h1,h2,h3]
    | ind_let y e1 e2 h1 h2 => simp only [open_expr_at, Exp.size, h1,h2]
    | ind_not e h => simp only [open_expr_at, Exp.size, h]
    | ind_cons y e fs he hfs =>
        simp at hfs
        simp only [open_expr_at,open_rcd_at, Exp.size, Fields.size, he,hfs]
    | ind_proj e y h => simp only [open_expr_at, Exp.size, h]


def open_expr x e := open_expr_at 0 x e

theorem opening_preserves_size' : ∀ x e, (open_expr x e).size = e.size := by
  apply opening_preserves_size
