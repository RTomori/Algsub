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
    | lam :  Exp → Exp
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
  | nil : TyField α
  | cons : String → α → TyField α → TyField α
  deriving BEq, Hashable, DecidableEq, Inhabited


mutual
inductive Ty : Type where
  | pos (p : PType)
  | neg (p : NType)
  deriving BEq, Hashable
inductive PType : Type where
  | bool : PType
  | int : PType
  | var : ℕ → PType
  | arr : NType → PType → PType
  | rcd : TyField PType → PType
  | join : PType → PType → PType
  | fix : ℕ → PType → PType
  | bot : PType
  deriving BEq, Hashable, Inhabited
inductive NType : Type where
  | bool : NType
  | int : NType
  | var : ℕ → NType
  | arr : PType → NType → NType
  | rcd : TyField NType → NType
  | meet : NType → NType → NType
  | top : NType
  | fix : ℕ → NType → NType
  deriving BEq, Hashable, Inhabited
end
def TyField.Repr [Repr α] : TyField α → String
  | .nil => ""
  | .cons l τ .nil => l ++ " : " ++ (repr τ).pretty
  | .cons l τ flds => l ++ ":" ++ (repr τ).pretty ++ flds.Repr

mutual
def PType.Repr : PType → String
  | .bool => "bool"
  | .fix n τ => "μ v" ++ n.repr ++ "." ++ τ.Repr
  | .arr τ₁ τ₂ => τ₁.Repr ++ "→" ++ τ₂.Repr
  | .bot => "⊥"
  | .join τ₁ τ₂ => "(" ++ τ₁.Repr ++ "⊔" ++ τ₂.Repr ++ ")"
  | .var n => "v" ++ n.repr
  | .int => "ℤ"
  | .rcd fld => "{" ++ posrcd_repr fld ++ "}"

def posrcd_repr : TyField PType → String
  | .nil => ""
  | .cons l τ .nil => l ++ ":" ++ τ.Repr
  | .cons l τ flds => l ++ ":" ++ τ.Repr ++ posrcd_repr flds

def NType.Repr : NType → String
  | .bool => "bool"
  | .int => "ℤ"
  | .var n => "v" ++ n.repr
  | .fix n τ => "μ " ++ n.repr ++ "." ++ τ.Repr
  | .top => "⊤"
  | .meet τ₁ τ₂ => "(" ++ τ₁.Repr ++ "⊓" ++ τ₂.Repr ++ ")"
  | .arr τ₁ τ₂ => "(" ++ τ₁.Repr ++ "→" ++  τ₂.Repr ++ ")"
  | .rcd fld => "{" ++ negrcd_repr fld ++ "}"

def negrcd_repr : TyField NType → String
  | .nil => ""
  | .cons l τ .nil => l ++ ":" ++ τ.Repr
  | .cons l τ flds => l ++ ":" ++ τ.Repr ++ "," ++ negrcd_repr flds
end
def Ty.Repr : Ty → String
  | .pos τ => τ.Repr
  | .neg τ => τ.Repr

instance : Repr PType := {reprPrec := fun t prec ↦ t.Repr}
instance : Repr NType := {reprPrec := fun t prec ↦ t.Repr}
instance : Repr Ty := {reprPrec := fun t _ ↦ t.Repr }

abbrev MonoEnv := Std.TreeMap ℕ NType
abbrev Typing := MonoEnv × PType
abbrev Environment := Std.TreeMap ℕ Typing

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

def fields_of_list (l : List (String × α)) : TyField α :=
  match l with
    | [] => .nil
    | (l , τ) :: fs => .cons l τ (fields_of_list fs)
def TyField.toList : TyField α → List (String × α)
  | .nil => []
  | .cons l x fs => (l, x) :: fs.toList
def dom :  TyField α →  List String
  | TyField.nil=> {}
  | TyField.cons l _ ts => {l} ∪ dom ts

def TyField.map_of_rcd : TyField α → Std.HashMap String α
  | TyField.nil => Std.HashMap.emptyWithCapacity
  | .cons l τ fls => fls.map_of_rcd.insert l τ
def rcd_map (f : α → β) (rcd : TyField α) : TyField β :=
  match rcd with
    | .nil  => .nil
    | .cons l x ts => .cons l (f x) (rcd_map f ts)

def rcd_traverse {m : Type → Type} [Applicative m]
  {α β : Type} (f : α → m β) : TyField α → m (TyField β)
  | .nil => pure .nil
  | .cons l x fs => (TyField.cons l) <$> f x <*> (rcd_traverse f fs)

def lookup (f : TyField α) (name : String) : Option α :=
  match f with
    | .nil => .none
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
  | .nil => .nil
  | .cons name t fs => .cons name (apply_pos σ t) (apply_pos_rcd σ fs)
def apply_neg_rcd (σ : Bisubst) : TyField NType → TyField NType
  | .nil => .nil
  | .cons name t fs => .cons name (apply_neg σ t) (apply_neg_rcd σ fs)
end

def apply_to_cst (σ : Bisubst) (c : Constraint) : Constraint :=
  match c with
    | (τ₁, τ₂) => (apply_pos σ τ₁, apply_neg σ τ₂)

def compose (σ₁ σ₂ : Bisubst) : Bisubst :=
  -- (σ₁ ∘ σ₂): apply σ₁ to σ₂'s range, then union in σ₁'s own bindings.
  -- The union is essential: dropping σ₁'s exclusive keys loses already-solved
  -- constraints (mapped wins on shared keys, since those are σ₁ applied to σ₂).
  let mapped := σ₂.map (fun _ (τ₁, τ₂) ↦ (apply_pos σ₁ τ₁, apply_neg σ₁ τ₂))
  σ₁.mergeWith (fun _ _ m ↦ m) mapped

-- test
#eval compose (emptyBisubst.insert 0 (.var 1, .var 1)) (emptyBisubst.insert 0 (.bot, .var 0))

mutual
def ftv_pos (n : ℕ) : PType → Bool
  | .var m => m == n
  | .bot | .int | .bool  => false
  | .join τ₁ τ₂ => ftv_pos n τ₁ || ftv_pos n τ₂
  | .rcd f => ftv_posrcd n f
  | .arr τ₁ τ₂ => ftv_neg n τ₁ || ftv_pos n τ₂
  | .fix _ τ => ftv_pos n τ
def ftv_neg (n : ℕ) : NType → Bool
 | .var m => m == n
 | .top | .int | .bool => false
 | .meet τ₁ τ₂ => ftv_neg n τ₁ || ftv_neg n τ₂
 | .rcd f => ftv_negrcd n f
 | .arr τ₁ τ₂ => ftv_pos n τ₁ || ftv_neg n τ₂
 | .fix _ τ => ftv_neg n τ

def ftv_posrcd(n : ℕ) : TyField PType → Bool
  | .nil => false
  | .cons _ τ fs => ftv_pos n τ || ftv_posrcd n fs

def ftv_negrcd (n : ℕ) : TyField NType → Bool
  | .nil => false
  | .cons _ τ fs => ftv_neg n τ || ftv_negrcd n fs
end

mutual
def numBinders : Exp → ℕ
  | .bvar _|.lbool _ | .lint _ => 0
  | .lam e => numBinders e + 1
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

/- ===== Lattice normalization (Layer 1) =====
Smart constructors that keep ⊔/⊓ in a canonical form by applying the lattice laws:
  * idempotence/dedup (τ ⊔ τ = τ),
  * unit elimination (drop ⊥ in joins, ⊤ in meets),
  * same-head merging via the dual law:
      arrows  (A→B) ⊔ (C→D) = (A⊓C)→(B⊔D),  dually for meet,
      records {l:A} ⊔ {l:B} = {l:A⊔B} (join keeps common labels),
              {l:A} ⊓ {m:B} = {l:A, m:B} (meet unions labels). -/

def dedupP (l : List PType) : List PType :=
  l.foldr (fun x acc => if acc.any (· == x) then acc else x :: acc) []
def dedupN (l : List NType) : List NType :=
  l.foldr (fun x acc => if acc.any (· == x) then acc else x :: acc) []

/-- Flatten nested joins, dropping ⊥ (the unit of ⊔). -/
def joinComps : PType → List PType
  | .join a b => joinComps a ++ joinComps b
  | .bot => []
  | t => [t]
/-- Flatten nested meets, dropping ⊤ (the unit of ⊓). -/
def meetComps : NType → List NType
  | .meet a b => meetComps a ++ meetComps b
  | .top => []
  | t => [t]

mutual
partial def mkJoin (a b : PType) : PType := joinList (joinComps a ++ joinComps b)
partial def mkMeet (a b : NType) : NType := meetList (meetComps a ++ meetComps b)

partial def joinList (comps : List PType) : PType :=
  let comps := dedupP comps
  let doms := comps.filterMap (fun | .arr d _ => some d | _ => none)
  let cods := comps.filterMap (fun | .arr _ c => some c | _ => none)
  let rcds := comps.filterMap (fun | .rcd f => some f | _ => none)
  let others := comps.filter (fun | .arr _ _ => false | .rcd _ => false | _ => true)
  let arrPart : List PType :=
    match doms, cods with
    | d :: ds, c :: cs => [PType.arr (ds.foldl mkMeet d) (cs.foldl mkJoin c)]
    | _, _ => []
  let rcdPart : List PType :=
    match rcds with
    | [] => []
    | f :: fs => [PType.rcd (fs.foldl mkRcdJoin f)]
  match others ++ arrPart ++ rcdPart with
    | [] => .bot
    | t :: ts => ts.foldl PType.join t

partial def meetList (comps : List NType) : NType :=
  let comps := dedupN comps
  let doms := comps.filterMap (fun | .arr d _ => some d | _ => none)
  let cods := comps.filterMap (fun | .arr _ c => some c | _ => none)
  let rcds := comps.filterMap (fun | .rcd f => some f | _ => none)
  let others := comps.filter (fun | .arr _ _ => false | .rcd _ => false | _ => true)
  let arrPart : List NType :=
    match doms, cods with
    | d :: ds, c :: cs => [NType.arr (ds.foldl mkJoin d) (cs.foldl mkMeet c)]
    | _, _ => []
  let rcdPart : List NType :=
    match rcds with
    | [] => []
    | f :: fs => [NType.rcd (fs.foldl mkRcdMeet f)]
  match others ++ arrPart ++ rcdPart with
    | [] => .top
    | t :: ts => ts.foldl NType.meet t

/-- Join of records: keep only common labels, join their field types. -/
partial def mkRcdJoin (f g : TyField PType) : TyField PType :=
  fields_of_list <| f.toList.filterMap (fun (l, x) =>
    match lookup g l with
    | some y => some (l, mkJoin x y)
    | none => none)

/-- Meet of records: union labels, meet the field types of common labels. -/
partial def mkRcdMeet (f g : TyField NType) : TyField NType :=
  let merged := f.toList.map (fun (l, x) =>
    match lookup g l with
    | some y => (l, mkMeet x y)
    | none => (l, x))
  let extra := g.toList.filter (fun (l, _) => (lookup f l).isNone)
  fields_of_list (merged ++ extra)

partial def normPos : PType → PType
  | .join a b => mkJoin (normPos a) (normPos b)
  | .arr d c => .arr (normNeg d) (normPos c)
  | .rcd f => .rcd (normRcdPos f)
  | .fix n t => .fix n (normPos t)
  | t => t

partial def normNeg : NType → NType
  | .meet a b => mkMeet (normNeg a) (normNeg b)
  | .arr d c => .arr (normPos d) (normNeg c)
  | .rcd f => .rcd (normRcdNeg f)
  | .fix n t => .fix n (normNeg t)
  | t => t

partial def normRcdPos : TyField PType → TyField PType
  | .nil => .nil
  | .cons l x fs => .cons l (normPos x) (normRcdPos fs)

partial def normRcdNeg : TyField NType → TyField NType
  | .nil => .nil
  | .cons l x fs => .cons l (normNeg x) (normRcdNeg fs)
end

def meet_env (e1 e2 : MonoEnv) : MonoEnv :=
  e1.mergeWith (fun _ τ₁ τ₂ => mkMeet τ₁ τ₂) e2

def normTyping : Typing → Typing
  | (Δ, τ) => (Δ.map (fun _ t => normNeg t), normPos τ)

def normBisubst (σ : Bisubst) : Bisubst :=
  σ.map (fun _ (p, n) => (normPos p, normNeg n))

/- ===== Layer 2: occurrence-based simplification =====
Operates on the coalesced type scheme (Δ, τ): bounds are already inlined as ⊓/⊔,
so simplification is just a rewrite over the syntax tree, guided by where each
*free* type variable occurs and at which polarity. μ-bound variables are tracked
in `bnd` and excluded throughout. -/

mutual
/-- Free type-variable occurrences in a positive type, paired with `true`. -/
partial def occP (bnd : List ℕ) : PType → List (ℕ × Bool)
  | .var n => if bnd.contains n then [] else [(n, true)]
  | .bool | .int | .bot => []
  | .join a b => occP bnd a ++ occP bnd b
  | .arr d c => occN bnd d ++ occP bnd c
  | .rcd f => occPRcd bnd f
  | .fix n t => occP (n :: bnd) t
/-- Free type-variable occurrences in a negative type, paired with `false`. -/
partial def occN (bnd : List ℕ) : NType → List (ℕ × Bool)
  | .var n => if bnd.contains n then [] else [(n, false)]
  | .bool | .int | .top => []
  | .meet a b => occN bnd a ++ occN bnd b
  | .arr d c => occP bnd d ++ occN bnd c
  | .rcd f => occNRcd bnd f
  | .fix n t => occN (n :: bnd) t
partial def occPRcd (bnd : List ℕ) : TyField PType → List (ℕ × Bool)
  | .nil => []
  | .cons _ x fs => occP bnd x ++ occPRcd bnd fs
partial def occNRcd (bnd : List ℕ) : TyField NType → List (ℕ × Bool)
  | .nil => []
  | .cons _ x fs => occN bnd x ++ occNRcd bnd fs
end

/-- Variables occurring positively / negatively somewhere in the scheme
    (Δ entries are inputs ⇒ negative root, τ is the output ⇒ positive root). -/
def schemeOccs : Typing → (List ℕ × List ℕ)
  | (Δ, τ) =>
    let occs := occP [] τ ++ (Δ.toList.map (fun (_, b) => occN [] b)).flatten
    (occs.filterMap (fun (n, p) => if p then some n else none),
     occs.filterMap (fun (n, p) => if p then none else some n))

def applyTyping (σ : Bisubst) : Typing → Typing
  | (Δ, τ) => (Δ.map (fun _ b => apply_neg σ b), apply_pos σ τ)

/-- Replace variables occurring in only one polarity by the corresponding lattice
    extremum (⊥ for positive-only, ⊤ for negative-only); units vanish on renorm. -/
def dropSinglePolar (ty : Typing) : Typing :=
  let (pos, neg) := schemeOccs ty
  let σ := pos.foldl
    (fun σ n => if neg.contains n then σ else σ.insert n (.bot, .var n)) emptyBisubst
  let σ := neg.foldl
    (fun σ n => if pos.contains n then σ else σ.insert n (.var n, .top)) σ
  applyTyping σ ty

mutual
/-- Drop vacuous recursive binders: `μβ.τ` with `β ∉ τ` ⇒ `τ`. -/
partial def dropMuP : PType → PType
  | .fix n t => let t := dropMuP t; if ftv_pos n t then .fix n t else t
  | .join a b => .join (dropMuP a) (dropMuP b)
  | .arr d c => .arr (dropMuN d) (dropMuP c)
  | .rcd f => .rcd (dropMuPRcd f)
  | t => t
partial def dropMuN : NType → NType
  | .fix n t => let t := dropMuN t; if ftv_neg n t then .fix n t else t
  | .meet a b => .meet (dropMuN a) (dropMuN b)
  | .arr d c => .arr (dropMuP d) (dropMuN c)
  | .rcd f => .rcd (dropMuNRcd f)
  | t => t
partial def dropMuPRcd : TyField PType → TyField PType
  | .nil => .nil
  | .cons l x fs => .cons l (dropMuP x) (dropMuPRcd fs)
partial def dropMuNRcd : TyField NType → TyField NType
  | .nil => .nil
  | .cons l x fs => .cons l (dropMuN x) (dropMuNRcd fs)
end

def dropMuTyping : Typing → Typing
  | (Δ, τ) => (Δ.map (fun _ b => dropMuN b), dropMuP τ)

def typingEq (a b : Typing) : Bool :=
  a.1.toList == b.1.toList && a.2 == b.2

def simpStep (ty : Typing) : Typing :=
  normTyping (dropMuTyping (dropSinglePolar ty))

/-- Iterate simplification to a fixpoint (bounded by `fuel`). -/
def simpFix : ℕ → Typing → Typing
  | 0, ty => ty
  | fuel + 1, ty =>
    let ty' := simpStep ty
    if typingEq ty ty' then ty else simpFix fuel ty'

def simplify (ty : Typing) : Typing := simpFix 100 (normTyping ty)

-- Module for type automata, partly ported from Dolan's.
namespace Types

inductive Polarity
  | pos | neg
  deriving DecidableEq, Repr, Hashable, Ord

def Polarity.flip : Polarity → Polarity
  | .pos => .neg
  | .neg => .pos

abbrev SMap (α : Type) := Std.TreeMap String α

inductive TyArg (α : Type)
  | apos (a : α) | aneg (a : α) | aneutral (a : α)

inductive Components (α : Type)
  | func (reqs : SMap Unit) (res : α)
  | rcd (tagged : SMap (SMap α)) (untagged : Option (SMap α))
  | base (s : ℕ) (args : List (TyArg α))

inductive TypeLat (α : Type)
  | unit
  | unexpanded (t : Components α)
  | expanded (ts : List (Components α))
abbrev StateId := ℕ
abbrev StateSet := Std.TreeSet StateId

structure State where
  id : StateId
  pol : Polarity
  cons : TypeLat StateSet
  flow : StateSet
-- NFA
structure Graph where
  nextId : StateId
  nodes : Std.HashMap StateId State

abbrev AutoM := StateM Graph

end Types
