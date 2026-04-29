import Mathlib.Tactic
import Mathlib.Control.Traversable.Basic
import Std.Data.TreeMap

mutual
  inductive Exp : Type where
  /-- Fixme : translate to locally nameless -/
    | bvar : ℕ → Exp
    | app : Exp → Exp → Exp
    | lbool : Bool → Exp
    | lint : Int → Exp
    | lam :  String → Exp → Exp
    | fix : Exp → Exp
    | rcd : Fields → Exp
    | ifc : Exp → Exp → Exp → Exp
    | letE : Exp → Exp → Exp
    | proj : Exp → String → Exp
    deriving BEq, Repr
  inductive Fields : Type where
    | nil : String → Exp → Fields
    | cons : String → Exp → Fields → Fields
    deriving BEq, Repr
end

/- Types are classified w.r.t. their polarities. Neutral types (logical variables, constants)
are regarded as type with both polarities -/
inductive TyField (α : Type) : Type where
  | nil : String → α → TyField α
  | cons : String → α → TyField α → TyField α
  deriving BEq, Hashable, DecidableEq, Repr

mutual
inductive Ty : Type where
  | pos (p : PType)
  | neg (p : NType)
  deriving BEq, Hashable, Repr
inductive PType : Type where
  | bool : PType
  | int : PType
  | var : ℕ → PType
  | arr : NType → PType → PType
  | rcd : TyField PType → PType
  | join : PType → PType → PType
  | fix : ℕ → PType → PType
  | bot : PType
  deriving BEq, Hashable, Repr
inductive NType : Type where
  | bool : NType
  | int : NType
  | var : ℕ → NType
  | arr : PType → NType → NType
  | rcd : TyField NType → NType
  | meet : NType → NType → NType
  | top : NType
  | fix : ℕ → NType → NType
  deriving BEq, Hashable, Repr
end

abbrev MonoEnv := Std.TreeMap ℕ NType
abbrev Typing := MonoEnv × PType
abbrev Environment := Std.TreeMap ℕ Typing

def join_env (e1 e2 : MonoEnv) : MonoEnv :=
  e1.mergeWith (fun _ τ₁ τ₂ => NType.meet τ₁ τ₂) e2

abbrev Constraint := PType × NType

inductive Exception where
  | UnknownIdent (x : String)
  | CannotInferArg (x : String)
  | CannotBiunify (τ₁ τ₂ : Ty)
  | Circular
  | Impossible
  deriving Repr

deriving instance Hashable for Constraint


def emptyEnv : Environment  := Std.TreeMap.empty


def dom :  TyField α →  Std.HashSet String
  | TyField.nil l _=> {l}
  | TyField.cons l _ ts => {l} ∪ dom ts

def rcd_map (f : α → β) (rcd : TyField α) : TyField β :=
  match rcd with
    | .nil l e => .nil l (f e)
    | .cons l x ts => .cons l (f x) (rcd_map f ts)

def rcd_traverse {m : Type → Type} [Applicative m]
  {α β : Type} (f : α → m β) : TyField α → m (TyField β)
  | .nil l e => (.nil l) <$> f e
  | .cons l x fs => (TyField.cons l) <$> f x <*> (rcd_traverse f fs)

def lookup (f : TyField α) (name : String) : Option α :=
  match f with
    | .nil l e => if name = l then .some e else .none
    | .cons l x ts => if name = l then .some x else lookup ts name
def Bisubst := Std.TreeMap ℕ (PType × NType)
deriving instance Repr for Bisubst
deriving instance Inhabited for Bisubst

def emptyBisubst : Bisubst := Std.TreeMap.empty

notation "[" n "↦" σ₁"⁺]" => emptyBisubst.insert n (σ₁, NType.var n)

notation "[" n "↦" σ₂ "⁻]" => emptyBisubst.insert n (PType.var n, σ₂)

mutual
def apply_pos (σ : Bisubst) : PType → PType
 | .var n =>
    match σ.get? n with
      | .none => .var n
      | .some (t1, _) => t1
  | .bool => .bool
  | .int => .int
  | .bot => .bot
  | .join t1 t2 => .join (apply_pos σ t1) (apply_pos σ t2)
  | .arr t1 t2 => .arr (apply_neg σ t1) (apply_pos σ t2)
  | .rcd fs => .rcd (apply_pos_rcd σ fs)
  | .fix n τ => .fix n (apply_pos σ τ)
def apply_neg (σ : Bisubst) : NType → NType
  | .var n =>
      match σ.get? n with
        | .none => .var n
        | .some (_, t2) => t2
  | .bool => .bool
  | .int => .int
  | .top => .top
  | .meet t1 t2 => .meet (apply_neg σ t1) (apply_neg σ t2)
  | .arr t1 t2 => .arr (apply_pos σ t1) (apply_neg σ t2)
  | .rcd fs => .rcd (apply_neg_rcd σ fs)
  | .fix n τ   => .fix n (apply_neg σ τ)

def apply_pos_rcd (σ : Bisubst) : TyField PType → TyField PType
  | .nil l τ => .nil l (apply_pos σ τ)
  | .cons name t fs => .cons name (apply_pos σ t) (apply_pos_rcd σ fs)
def apply_neg_rcd (σ : Bisubst) : TyField NType → TyField NType
  | .nil l τ => .nil l (apply_neg σ τ)
  | .cons name t fs => .cons name (apply_neg σ t) (apply_neg_rcd σ fs)
end

def apply_to_cst (σ : Bisubst) (c : Constraint) : Constraint :=
  match c with
    | (τ₁, τ₂) => (apply_pos σ τ₁, apply_neg σ τ₂)

def compose (σ₁ σ₂ : Bisubst) : Bisubst :=
  σ₂.map (fun _ (τ₁, τ₂) ↦ (apply_pos σ₁ τ₁, apply_neg σ₁ τ₂))

-- test
#eval compose (emptyBisubst.insert 0 (.bot, .var 0)) (emptyBisubst.insert 0 (.bot, .var 0))

mutual
def ftv_pos (n : ℕ) : PType → Bool
  | .var m => m == n
  | .bot | .int | .bool  => false
  | .join τ₁ τ₂ => ftv_pos n τ₁ && ftv_pos n τ₂
  | .rcd f => ftv_posrcd n f
  | .arr τ₁ τ₂ => ftv_neg n τ₁ && ftv_pos n τ₂
def ftv_neg (n : ℕ) : NType → Bool
 | .var m => m == n
 | .top | .int | .bool => false
 | .meet τ₁ τ₂ => ftv_neg n τ₁ && ftv_neg n τ₂
 | .rcd f => ftv_negrcd n f
 | .arr τ₁ τ₂ => ftv_pos n τ₁ && ftv_neg n τ₂
 | .fix m τ => _

def ftv_posrcd(n : ℕ) : TyField PType → Bool
  | .nil _ τ => ftv_pos n τ
  | .cons _ τ fs => ftv_pos n τ && ftv_posrcd n fs

def ftv_negrcd (n : ℕ) : TyField NType → Bool
  | .nil _ τ => ftv_neg n τ
  | .cons _ τ fs => ftv_neg n τ && ftv_negrcd n fs
end

mutual
def numBinders : Exp → ℕ
  | .bvar _|.lbool _ | .lint _ => 0
  | .lam _ e => numBinders e + 1
  | .letE e1 e2 => max (numBinders e2 + 1) (numBinders e1)
  | .ifc e1 e2 e3 => max (max (numBinders e1) (numBinders e2)) (numBinders e3)
  | .fix e => numBinders e + 1
  | .app e1 e2 => max (numBinders e1) (numBinders e2)
  | .proj e _ => numBinders e
  | .rcd f => numBinders_rcd f

def numBinders_rcd : Fields → ℕ
  | .nil _ e => numBinders e
  | .cons _ e fs => max (numBinders e) (numBinders_rcd fs)
end
instance : Traversable TyField where
  map := rcd_map
  traverse := rcd_traverse
