import Mathlib.Tactic
<<<<<<< HEAD
import Algsub.Basic

-- graph-based representation of inference
=======
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeMap
open Lean hiding Environment Exception
set_option linter.style.longLine false

namespace Types
inductive Polarity | pos | neg
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

def Polarity.flip : Polarity → Polarity
    | .pos => .neg | .neg => .pos

abbrev Symbol := String

inductive TyArg (α : Type) where
    | pos    (a : α)
    | neg    (a : α)
    | negPos (n p : α)
    | none
    deriving BEq, Repr

inductive Head (α : Type) where
    | func : α -> α -> Head α
    | rcd  : List (Symbol × α) → Head α
    | variant : List (Symbol × α) → Head α
    | base (stamp : Nat) (args : List (TyArg α))
  deriving BEq, Repr

section ListOrder
variable {β : Type} {R : β → β → Prop}

theorem forall₂_trans (tr : ∀ {a b c}, R a b → R b c → R a c) :
    ∀ {l₁ l₂ l₃}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₂ l₃ → List.Forall₂ R l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => .cons (tr h₁ h₂) (forall₂_trans tr t₁ t₂)

theorem forall₂_antisymm (anti : ∀ {a b}, R a b → R b a → a = b) :
    ∀ {l₁ l₂}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₂ l₁ → l₁ = l₂
  | _, _, .nil, _ => rfl
  | _, _, .cons h₁ t₁, .cons h₂ t₂ => by rw [anti h₁ h₂, forall₂_antisymm anti t₁ t₂]

theorem sublistForall₂_refl (refl : ∀ a, R a a) : ∀ l, List.SublistForall₂ R l l
  | [] => .nil
  | a :: l => .cons (refl a) (sublistForall₂_refl refl l)

theorem sublistForall₂_trans (tr : ∀ {a b c}, R a b → R b c → R a c) {l₁ l₂ l₃ : List β}
    (h₁ : List.SublistForall₂ R l₁ l₂) (h₂ : List.SublistForall₂ R l₂ l₃) :
    List.SublistForall₂ R l₁ l₃ :=
  haveI : IsTrans β R := ⟨fun _ _ _ => tr⟩
  IsTrans.trans _ _ _ h₁ h₂

-- mutual embeddings have equal lengths, so neither skips an element
theorem sublistForall₂_antisymm (anti : ∀ {a b}, R a b → R b a → a = b) {l₁ l₂ : List β}
    (h₁ : List.SublistForall₂ R l₁ l₂) (h₂ : List.SublistForall₂ R l₂ l₁) : l₁ = l₂ := by
  obtain ⟨m₁, f₁, s₁⟩ := List.sublistForall₂_iff.1 h₁
  obtain ⟨m₂, f₂, s₂⟩ := List.sublistForall₂_iff.1 h₂
  have := f₁.length_eq; have := f₂.length_eq; have := s₁.length_le; have := s₂.length_le
  obtain rfl := s₁.eq_of_length (by omega)
  obtain rfl := s₂.eq_of_length (by omega)
  exact forall₂_antisymm anti f₁ f₂

theorem sublistForall₂_of_cons {a : β} {l₁ l₂ : List β}
    (h : List.SublistForall₂ R (a :: l₁) l₂) : List.SublistForall₂ R l₁ l₂ := by
  obtain ⟨_, f, s⟩ := List.sublistForall₂_iff.1 h
  cases f with
  | cons _ f => exact List.sublistForall₂_iff.2 ⟨_, f, (List.sublist_cons_self _ _).trans s⟩

-- matching `a` against the first `b` it fits is never worse than skipping `b`, so greedy decides
instance decSublistForall₂ [DecidableRel R] : ∀ l₁ l₂, Decidable (List.SublistForall₂ R l₁ l₂)
  | [], _ => isTrue .nil
  | _ :: _, [] => isFalse nofun
  | a :: l₁, b :: l₂ =>
    if hr : R a b then
      haveI := decSublistForall₂ l₁ l₂
      decidable_of_iff _ ⟨.cons hr, fun
        | .cons _ h => h
        | .cons_right h => sublistForall₂_of_cons h⟩
    else
      haveI := decSublistForall₂ (a :: l₁) l₂
      decidable_of_iff _ ⟨.cons_right, fun
        | .cons h _ => absurd h hr
        | .cons_right h => h⟩
end ListOrder

-- labels must agree, payloads are compared by `R`
def fieldRel (R : α → α → Prop) (p q : Symbol × α) : Prop := p.1 = q.1 ∧ R p.2 q.2

instance [DecidableRel R] : DecidableRel (fieldRel R) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

theorem fieldRel.trans (tr : ∀ {a b c : α}, R a b → R b c → R a c) {p q r : Symbol × α} :
    fieldRel R p q → fieldRel R q r → fieldRel R p r
  | ⟨e₁, h₁⟩, ⟨e₂, h₂⟩ => ⟨e₁.trans e₂, tr h₁ h₂⟩

theorem fieldRel.antisymm (anti : ∀ {a b : α}, R a b → R b a → a = b) {p q : Symbol × α} :
    fieldRel R p q → fieldRel R q p → p = q
  | ⟨e, h₁⟩, ⟨_, h₂⟩ => Prod.ext e (anti h₁ h₂)

-- a `base` argument is ordered by its slot's variance
def TyArg.le [LE α] : TyArg α → TyArg α → Prop
  | .pos a,      .pos b        => a ≤ b
  | .neg a,      .neg b        => b ≤ a
  | .negPos n p, .negPos n' p' => n' ≤ n ∧ p ≤ p'
  | .none,       .none         => True
  | _,           _             => False

instance [LE α] : LE (TyArg α) := ⟨TyArg.le⟩

instance [LE α] [DecidableLE α] : DecidableLE (TyArg α) := fun a b ↦ by
  change Decidable (TyArg.le a b)
  cases a <;> cases b <;> dsimp only [TyArg.le] <;> infer_instance

instance [PartialOrder α] : PartialOrder (TyArg α) where
  le := (· ≤ ·)
  le_refl a := by cases a <;> dsimp only [LE.le, TyArg.le] <;> simp
  le_trans a b c h₁ h₂ := by
    cases a <;> cases b <;> try exact (h₁ : False).elim
    all_goals cases c <;> try exact (h₂ : False).elim
    · exact le_trans (α := α) h₁ h₂
    · exact le_trans (α := α) h₂ h₁
    · exact ⟨le_trans h₂.1 h₁.1, le_trans h₁.2 h₂.2⟩
    · trivial
  le_antisymm a b h₁ h₂ := by
    cases a <;> cases b <;> try exact (h₁ : False).elim
    · exact congrArg _ (le_antisymm (α := α) h₁ h₂)
    · exact congrArg _ (le_antisymm (α := α) h₂ h₁)
    · exact congrArg₂ _ (le_antisymm h₂.1 h₁.1) (le_antisymm h₁.2 h₂.2)
    · rfl

instance [BEq α] [Hashable α] : LE (Std.HashSet α) where
  le s₁ s₂ := s₁.all (s₂.contains ·)

-- `a ≤ b` unfolds to `a.all (b.contains ·) = true`, so decide it by `Bool` equality
instance [BEq α] [Hashable α] : DecidableLE (Std.HashSet α) :=
  fun a b ↦ instDecidableEqBool (a.all (b.contains ·)) true

-- Subtyping between heads: functions are contravariant in the domain, records lose fields going
-- up, variants gain cases. Field lists are matched in order (an order-preserving embedding), so
-- this is antisymmetric on lists, and it coincides with ordinary width/depth subtyping when
-- fields are kept sorted by label without duplicates.
def Head.le [LE α] : Head α → Head α → Prop
  | .func d₁ c₁, .func d₂ c₂     => d₂ ≤ d₁ ∧ c₁ ≤ c₂
  | .rcd fs₁, .rcd fs₂           => List.SublistForall₂ (fieldRel (· ≥ ·)) fs₂ fs₁
  | .variant cs₁, .variant cs₂   => List.SublistForall₂ (fieldRel (· ≤ ·)) cs₁ cs₂
  | .base k₁ as₁, .base k₂ as₂   => k₁ = k₂ ∧ List.Forall₂ (· ≤ ·) as₁ as₂
  | _, _                         => False  -- distinct constructors are incomparable

instance [LE α] : LE (Head α) := ⟨Head.le⟩

instance [LE α] [DecidableLE α] : DecidableLE (Head α) := fun a b ↦ by
  change Decidable (Head.le a b)
  cases a <;> cases b <;> dsimp only [Head.le] <;> infer_instance

instance [PartialOrder α] : PartialOrder (Head α) where
  le := (· ≤ ·)
  le_refl h := by
    cases h
    · exact ⟨le_rfl, le_rfl⟩
    · exact sublistForall₂_refl (fun _ ↦ ⟨rfl, le_rfl⟩) _
    · exact sublistForall₂_refl (fun _ ↦ ⟨rfl, le_rfl⟩) _
    · exact ⟨rfl, List.forall₂_same.2 fun _ _ ↦ le_rfl⟩
  le_trans a b c h₁ h₂ := by
    cases a <;> cases b <;> try exact (h₁ : False).elim
    all_goals cases c <;> try exact (h₂ : False).elim
    · exact ⟨le_trans h₂.1 h₁.1, le_trans h₁.2 h₂.2⟩
    · exact sublistForall₂_trans (R := fieldRel (· ≥ ·)) (fieldRel.trans ge_trans) h₂ h₁
    · exact sublistForall₂_trans (R := fieldRel (· ≤ ·))
        (fieldRel.trans (R := (· ≤ ·)) le_trans) h₁ h₂
    · exact ⟨h₁.1.trans h₂.1, forall₂_trans (R := (· ≤ ·)) le_trans h₁.2 h₂.2⟩
  le_antisymm a b h₁ h₂ := by
    cases a <;> cases b <;> try exact (h₁ : False).elim
    · exact congrArg₂ _ (le_antisymm h₂.1 h₁.1) (le_antisymm h₁.2 h₂.2)
    · exact congrArg _ <| sublistForall₂_antisymm (R := fieldRel (· ≥ ·))
        (fieldRel.antisymm ge_antisymm) h₂ h₁
    · exact congrArg _ <| sublistForall₂_antisymm (R := fieldRel (· ≤ ·))
        (fieldRel.antisymm le_antisymm) h₁ h₂
    · obtain ⟨rfl, h₁⟩ := h₁
      exact congrArg _ (forall₂_antisymm (R := (· ≤ ·)) le_antisymm h₁ h₂.2)


abbrev StateId := ℕ
abbrev DStateId := ℕ

structure State where
  pol : Polarity
  cons : List (Head (Std.HashSet StateId))
  flow : Std.HashSet StateId
deriving Repr, Inhabited
abbrev Automata := Array State

structure DState where
  pol : Polarity
  cons : List (Head StateId)
  flow : Std.HashSet DStateId
deriving Repr

abbrev DAutomata := Array DState

-- Type representation
inductive Ty where
    | var  (v : Symbol)          -- TNamed v []  (free, or bound by an enclosing rec)
    | zero                       -- ⊥ at +, ⊤ at −
    | add  (a b : Ty)            -- ⊔ at +, ⊓ at −
    | fix  (v : Symbol) (t : Ty) -- μv.t
    | cons (h : Head Ty)
    deriving Repr, Inhabited


inductive Node (ι : Type) where
  | var    (v : Symbol)   -- free variable
  | zero
-- | unit
  | sum    (a b : ι)
 -- | prod (a b : ι)
  | fix    (body : ι)
  | fixVar (binder : ι)   -- bound occurrence → its μ node
  | cons   (h : Head ι)
  deriving BEq, Repr, Inhabited

inductive Variance
  | VPos | VNeg | VNegPos | None
  deriving BEq, Repr

structure TyCtx where
  next : Nat := 1
  decls : Std.HashMap ℕ (Symbol × Array Variance)
    := Std.HashMap.ofList [(1, ("bool", {})), (2, ("int", {}))]
  byName : Std.HashMap Symbol ℕ := {}

structure Typechecker.Context where
  env : TyCtx := {}

structure Typechecker.State where
  ngen : ℕ  := 0
  nvargen : ℕ := 0
  seen : Std.HashSet (StateId × StateId) := {}


abbrev M := ReaderT Typechecker.Context
                      <| StateT Typechecker.State <| Except String

def M.run (x : M α) : Except String α := x {} |>.run' {}
-- Things needed to put automata back into type syntax
def mkFreshId : M ℕ := do{
  let s ← get;
  modify (fun s ↦ {s with ngen := s.ngen + 1});
  pure s.ngen
}
def TyArg.mapM [Monad m] (f : α → m β) : TyArg α → m (TyArg β)
  | .none => pure .none
  | .pos a => .pos <$> f a
  | .negPos a b => .negPos <$> f a <*> f b
  | .neg b => .neg <$> f b

def Head.mapM [Monad m] (f : α → m β) : Head α → m (Head β)
  | .func d c => .func <$> f d <*> f c
  | .rcd fs => .rcd <$> fs.mapM (fun (l, a) ↦ (l, · ) <$> f a)
  | .variant fs => .variant <$> fs.mapM (fun (l, a) ↦ (l, ·) <$> f a)
  | .base k args => .base k <$> args.mapM (TyArg.mapM f)

def Ty.sum : List Ty → Ty
  | [] => .zero
  | [t] => t
  | t :: ts => .add t (Ty.sum ts)

def flow_vars (aut : Automata) (q : StateId) (s : State) : List Ty :=
  match s.pol with
    | .neg => if s.flow.isEmpty then [] else [.var s!"v{q}"]
    | .pos => s.flow.toList.filter (· < aut.size) |>.map (fun n ↦ .var s!"v{n}")

def decode' (aut : Automata) : ℕ → List StateId → StateId → StateM (Std.HashSet StateId) Ty
  | 0, _, q => pure (.var s!"r{q}")
  | n + 1, stack, q => do{
    if stack.contains q then
      modify (·.insert q); return (.var s!"r{q}")
    let some s := aut[q]? | return .zero
    let decSet (ss : Std.HashSet StateId) : StateM _ Ty :=
        Ty.sum <$> ss.toList.mapM (decode' aut n (q :: stack))
      let heads ← s.cons.mapM (fun h => Ty.cons <$> h.mapM decSet)
      let body := Ty.sum (heads ++ flow_vars aut q s)
      let isRec := (← get).contains q;
      modify (·.erase q)
      return if isRec then .fix s!"r{q}" body else body
  }
def decode (A : Automata) (root : StateId) : Ty :=
    (decode' A (A.size + 1) [] root).run' {}

def create_state
  (p : Polarity) (cons : List (Head (List StateId))) (flow : List StateId) : State :=
  {pol := p,
   cons := cons.map (fun h ↦ (Head.mapM (m := Id) (fun l ↦ Std.HashSet.ofList l) h)),
    flow := .ofList flow}

def create_dstate (p : Polarity) (cons : List (Head DStateId)) (flow : List DStateId) : DState := {
  pol := p,
  cons := cons,
  flow := .ofList flow
}
-- inverse of above
abbrev FlatM := StateT (Array (Polarity × Node ℕ)) (Except String)

def reserve (p : Polarity) : FlatM ℕ := do{
   let i := (←get).size;
   modify (·.push (p, .zero));
   pure i;
}
def fill (i : ℕ) (p : Polarity) (n : Node ℕ) : FlatM Unit :=
  modify (·.set! i (p, n))

def push (p : Polarity) (n : Node ℕ) : FlatM ℕ := do{
  let i ← reserve p;
  fill i p n;
  pure i
}

-- polarity-aware traversal: domains and `neg` args flip the polarity
def TyArg.mapPolM [Monad m] (f : Polarity → α → m β) (p : Polarity) : TyArg α → m (TyArg β)
  | .none => pure .none
  | .pos a => .pos <$> f p a
  | .neg a => .neg <$> f p.flip a
  | .negPos n q => .negPos <$> f p.flip n <*> f p q

def Head.mapPolM [Monad m] (f : Polarity → α → m β) (p : Polarity) : Head α → m (Head β)
  | .func d c => .func <$> f p.flip d <*> f p c
  | .rcd fs => .rcd <$> fs.mapM (fun (l, a) ↦ (l, ·) <$> f p a)
  | .variant fs => .variant <$> fs.mapM (fun (l, a) ↦ (l, ·) <$> f p a)
  | .base k args => .base k <$> args.mapM (TyArg.mapPolM f p)

-- Step 1: one node per subterm; μ-bound occurrences point back at their binder
partial def flatten (env : List (Symbol × ℕ)) (p : Polarity) : Ty → FlatM ℕ
  | .var v => do{
    match env.lookup v with
    | some b =>
      let (pb, _) := (← get)[b]!;
      if pb ≠ p then throw s!"μ-variable {v} occurs at the wrong polarity";
      push p (.fixVar b)
    | none => push p (.var v)
  }
  | .zero => push p .zero
  | .add a b => do{
    let i ← flatten env p a;
    let j ← flatten env p b;
    push p (.sum i j)
  }
  | .fix v t => do{
    let i ← reserve p;
    let j ← flatten ((v, i) :: env) p t;
    fill i p (.fix j);
    pure i
  }
  | .cons h => do{
    let h' ← Head.mapPolM (fun q t ↦ flatten env q t) p h;
    push p (.cons h')
  }


def epsClosure (nodes : Array (Polarity × Node ℕ)) (i : ℕ) : Std.HashSet ℕ := Id.run do{
  let mut seen : Std.HashSet ℕ := {};
  let mut todo := [i];
  repeat
    match todo with
    | [] => break
    | j :: js =>
      todo := js;
      if seen.contains j then continue;
      seen := seen.insert j;
      match nodes[j]? with
      | some (_, .sum a b) => todo := a :: b :: todo
      | some (_, .fix b) | some (_, .fixVar b) => todo := b :: todo
      | _ => pure ()
  return seen
}

def toAutomata (nodes : Array (Polarity × Node ℕ)) (start : StateId := 0) : Automata := Id.run do{
  let clos := (Array.range nodes.size).map (epsClosure nodes);
  let varsOf (i : ℕ) : List Symbol := clos[i]!.toList.filterMap fun j ↦
    match nodes[j]! with | (_, .var v) => some v | _ => none;
  let mut negOcc : Std.HashMap Symbol (List StateId) := {};
  let mut posOcc : Std.HashMap Symbol (List StateId) := {};
  for i in [0:nodes.size] do
    for v in varsOf i do
      match nodes[i]!.1 with
      | .neg => negOcc := negOcc.alter v (some <| (start + i) :: ·.getD [])
      | .pos => posOcc := posOcc.alter v (some <| (start + i) :: ·.getD [])
  -- a bound occurrence has the same heads and variables as its binder, so point at the binder
  let target (k : ℕ) : ℕ := match nodes[k]! with | (_, .fixVar b) => b | _ => k;
  let mkState (i : ℕ) : State :=
    let p := nodes[i]!.1;
    let cons := clos[i]!.toList.filterMap fun j ↦
      match nodes[j]! with
      | (_, .cons h) =>
        some (Head.mapM (m := Id) (fun k ↦ ({start + target k} : Std.HashSet StateId)) h)
      | _ => none;
    let flow := match p with
      | .pos => {}
      | .neg => (varsOf i).foldl (fun s v ↦ s.insertMany (posOcc.getD v [])) {};
    {pol := p, cons := cons, flow := flow};
  return (Array.range nodes.size).map mkState
}


-- dense id of a key; a new key is appended to the array, which doubles as the worklist
def intern [BEq κ] [Hashable κ] (k : κ) : StateM (Std.HashMap κ ℕ × Array κ) ℕ :=
  modifyGet fun (ids, keys) ↦
    match ids[k]? with
    | some d => (d, ids, keys)
    | none   => (keys.size, ids.insert k keys.size, keys.push k)

-- Step 4: keep only the states reachable from `roots` along head transitions, renumbered in
-- order of discovery (so the roots come first). Sum operands and μ bodies are reachable only
-- through ε: their heads and variables were already copied into the state that absorbed them.
def trim (A : Automata) (roots : List StateId) : Automata × List StateId := Id.run do{
  let (rootIds, st) := (roots.mapM intern).run ({}, #[]);
  let mut st := st;
  let mut cons : Array (List (Head (Std.HashSet StateId))) := #[];
  while h : cons.size < st.2.size do
    let (hs, st') := (A[st.2[cons.size]]!.cons.mapM
      (Head.mapM fun (ss : Std.HashSet StateId) ↦
      Std.HashSet.ofList <$> ss.toList.mapM intern)).run st;
    cons := cons.push hs;
    st := st';
  let (ids, kept) := st;
  -- a flow edge into a dropped state is redundant: the state absorbing it has the same variables
  let states := kept.mapIdx fun i q ↦
    ({pol := A[q]!.pol, cons := cons[i]!, flow := .ofList (A[q]!.flow.toList.filterMap (ids[·]?))}
      : State);
  return (states, rootIds)
}

def encode (t : Ty) (p : Polarity := .pos) : Except String (Automata × StateId) := do{
  let (root, nodes) ← (flatten [] p t).run #[];
  let (A, roots) := trim (toAutomata nodes) [root];
  pure (A, roots.head!)
}

-- A DFA state is named by the set of NFA states it stands for. Keys must be canonical:
-- `HashSet.toList` order is arbitrary and `HashSet` isn't `Hashable`, so sort.
abbrev Subset := List StateId

def Subset.ofSet (s : Std.HashSet StateId) : Subset := s.toList.mergeSort (· ≤ ·)

def TyArg.union : TyArg (Std.HashSet StateId) →
    TyArg (Std.HashSet StateId) → TyArg (Std.HashSet StateId)
  | .pos a,      .pos b        => .pos (a.insertMany b)
  | .neg a,      .neg b        => .neg (a.insertMany b)
  | .negPos n p, .negPos n' p' => .negPos (n.insertMany n') (p.insertMany p')
  | a,           _             => a  -- variance mismatch: impossible for a well-formed stamp

-- join (+) keeps the common fields, meet (−) keeps all of them
def mergeRcd (p : Polarity) (xs ys : List (Symbol × Std.HashSet StateId)) :
    List (Symbol × Std.HashSet StateId) :=
  match p with
  | .pos => xs.filterMap fun (l, a) ↦ (ys.lookup l).map fun b ↦ (l, a.insertMany b)
  | .neg => xs.map (fun (l, a) ↦ (l, match ys.lookup l with | some b => a.insertMany b | none => a))
            ++ ys.filter (fun (l, _) ↦ (xs.lookup l).isNone)

-- At most one head per constructor (`func`, `rcd`, each `base` stamp), successor sets unioned.
-- Union is the right operation in every position because successors already carry the
-- flipped polarity: (a₁→b₁) ⊔ (a₂→b₂) = (a₁⊓a₂) → (b₁⊔b₂), and a₁, a₂ are − states.
def mergeHeads (p : Polarity) (hs : List (Head (Std.HashSet StateId))) :
    List (Head (Std.HashSet StateId)) :=
  hs.foldl (fun acc h ↦ add h acc) []
where
  add (h : Head (Std.HashSet StateId)) : List (Head (Std.HashSet StateId)) → List (Head (Std.HashSet StateId))
    | [] => [h]
    | h' :: hs => match h', h with
      | .func d c, .func d' c' => .func (d.insertMany d') (c.insertMany c') :: hs
      | .rcd fs, .rcd fs' => .rcd (mergeRcd p fs fs') :: hs
      | .base k as, .base k' as' =>
        if k = k' then .base k (List.zipWith TyArg.union as as') :: hs else h' :: add h hs
      | _, _ => h' :: add h hs

abbrev DetM := StateM (Std.HashMap (Polarity × Subset) DStateId × Array (Polarity × Subset))

-- a DFA state is interned under its polarity and subset
def determinise (aut : Automata) (roots : List StateId) : DAutomata × List DStateId := Id.run do{
  let polOf (q : StateId) := (aut[q]?.map (·.pol)).getD .pos;
  let (rootIds, st) := (roots.mapM fun q ↦ intern (polOf q, [q])).run (({}, #[]) : _ × Array _);
  let mut st := st;
  let mut cons : Array (List (Head DStateId)) := #[];
  -- subset construction over the reachable subsets only; flow edges are not transitions
  while h : cons.size < st.2.size do
    let (p, k) := st.2[cons.size];
    let heads := mergeHeads p (k.filterMap (aut[·]?) |>.flatMap (·.cons));
    let (hs, st') := (heads.mapM (Head.mapPolM (fun p' s ↦ intern (p', Subset.ofSet s)) p)).run st;
    cons := cons.push hs;
    st := st';
  let sets := st.2;
  -- flow edges need every DFA state to exist: X ⇝ Y iff ∃ q ∈ X, q' ∈ Y, q ⇝ q'
  let mut owners : Std.HashMap StateId (List DStateId) := {};
  for d in [0:sets.size] do
    for q in sets[d]!.2 do
      owners := owners.alter q (some <| d :: ·.getD []);
  let flowOf (k : Subset) : Std.HashSet DStateId :=
    (k.filterMap (aut[·]?)).foldl
      (fun acc s ↦ s.flow.fold (fun acc q' ↦ acc.insertMany (owners.getD q' [])) acc) {};
  let states := sets.mapIdx fun d (p, k) ↦ ({pol := p, cons := cons[d]!, flow := flowOf k} : DState);
  return (states, rootIds)
}


inductive HeadTag | func | rcd | variant | base (k : ℕ)
  deriving BEq, Hashable, Ord

def Head.tag : Head α → HeadTag
  | .func .. => .func | .rcd _ => .rcd | .variant _ => .variant | .base k _ => .base k

-- the slot a child hangs off; `p` picks the half of a `negPos` argument
inductive Letter
  | dom | cod
  | field (l : Symbol)
  | arg (k i : ℕ) (p : Polarity)
  deriving BEq, Hashable, Ord

-- a record's field set is recovered from its `field` letters, so `HeadTag.rcd` needn't carry it
def Head.edges : Head α → List (Letter × α)
  | .func d c => [(.dom, d), (.cod, c)]
  | .rcd fs | .variant fs => fs.map fun (l, a) ↦ (.field l, a)
  | .base k args => args.zipIdx.flatMap fun
    | (.pos a, i) => [(.arg k i .pos, a)]
    | (.neg a, i) => [(.arg k i .neg, a)]
    | (.negPos n q, i) => [(.arg k i .neg, n), (.arg k i .pos, q)]
    | (.none, _) => []

-- number the distinct keys in order of first appearance
def classify [BEq κ] [Hashable κ] (keys : Array κ) : Array ℕ × ℕ := Id.run do{
  let mut ids : Std.HashMap κ ℕ := {};
  let mut cls := #[];
  for k in keys do
    match ids[k]? with
    | some c => cls := cls.push c
    | none => cls := cls.push ids.size; ids := ids.insert k ids.size
  return (cls, ids.size)
}


def minimise (A : DAutomata) (roots : List DStateId) : DAutomata × List DStateId := Id.run do{
  -- `mergeHeads` leaves at most one head per constructor but in no canonical order, so sort
  let edges := A.map fun s ↦
    (s.cons.flatMap Head.edges).mergeSort fun a b ↦ (compare a.1 b.1).isLE;
  let preds : Std.HashMap DStateId (List DStateId) :=
    A.zipIdx.foldl (fun m (s, n) ↦ s.flow.fold (fun m p ↦ m.alter p (some <| n :: ·.getD [])) m) {};
  let (cls, n) := classify <| A.zipIdx.map fun (s, q) ↦
    (s.pol, (s.cons.map Head.tag).mergeSort (fun a b ↦ (compare a b).isLE),
     Subset.ofSet s.flow, (preds.getD q []).mergeSort (· ≤ ·));
  let mut cls := cls;
  let mut n := n;
  -- each round only splits classes, so an unchanged count means the partition is stable
  repeat
    let cur := cls;
    let (cls', n') := classify <| (Array.range A.size).map fun q ↦
      (cur[q]!, edges[q]!.map fun (l, t) ↦ (l, cur[t]!));
    if n' == n then break;
    cls := cls'; n := n';
  -- classes are numbered by first appearance, so the first member of each is met in order
  let mut reps : Array DState := #[];
  for (s, q) in A.zipIdx do
    if cls[q]! == reps.size then reps := reps.push s
  let states := reps.map fun s ↦
    ({pol := s.pol,
      cons := s.cons.map (Head.mapM (m := Id) (cls[·]!)),
      flow := .ofList (s.flow.toList.filterMap (cls[·]?))} : DState);
  return (states, roots.map (cls[·]!))
}

-- a DFA is an NFA with singleton successor sets, so `decode` can be reused
def DAutomata.toAutomata (A : DAutomata) : Automata :=
  A.map fun s ↦
  {pol := s.pol,
   cons := s.cons.map (Head.mapM (m := Id) fun d ↦ ({d} : Std.HashSet StateId)),
   flow := s.flow}

def detRoundTrip (t : Ty) (p : Polarity := .pos) : Except String Ty := do{
  let (A, r) ← encode t p;
  let (D, rs) := determinise A [r];
  pure (decode D.toAutomata rs.head!)
}

def show_automata (t : Ty) (p : Polarity := .pos) := do{
  let (A, _) <- encode t p;
  pure A;
  }
def simplify (t : Ty) (p : Polarity := .pos) : Except String Ty := do{
  let (A, r) ← encode t p;
  let (D, rs) := determinise A [r];
  let (D, rs) := minimise D rs;
  pure (decode D.toAutomata rs.head!)
}

abbrev Typing := Std.HashMap String Ty × Ty
-- scheme automata
structure SAutomata where
  scheme : Automata
  env : Std.HashMap String StateId
  res : StateId
  deriving Repr
-- Convert type scheme to scheme automata. All types share one node array, so a variable occurring
-- in both the environment and the result gets flow edges between them; trimming from every root
-- at once then drops the ε-only nodes. Returns the root of each environment entry and of the result.
def encode_typing (typ : Typing) :
    Except String SAutomata := do{
  let (env, ty) := typ;
  let ((envRoots, root), nodes) ← (show FlatM _ from do{
    let envRoots ← env.toList.mapM fun (x, t) ↦ (x, ·) <$> flatten [] .neg t;
    pure (envRoots, ← flatten [] .pos ty)
  }).run #[];
  let (A, roots) := trim (toAutomata nodes) (root :: envRoots.map (·.2));
  pure {scheme := A, env := .ofList (envRoots.map (·.1) |>.zip roots.tail), res := roots.head!}
}

def decode_typing (aut : SAutomata) : Typing :=
  (aut.env.map (fun _ id => decode aut.scheme id), decode aut.scheme aut.res)

def simplify_typing (typ : Typing) := do{
  let aut <- encode_typing typ;
  let keys := aut.env.keys;
  let (det, dstates) := determinise aut.scheme (aut.res :: aut.env.values);
  let (d_minimised, dstates) := minimise det dstates;
  pure (decode_typing {scheme := d_minimised.toAutomata,
                       env := Std.HashMap.ofList (List.zip keys dstates.tail),
                       res := dstates.head!});
}

-- add head constructors/transitions/flow edges from q2 to q1
-- since flow edges are symmetric, not directed, it suffices to copy flow edges of q2 to q1

def SAutomata.merge (aut : SAutomata) (q1 q2 : StateId)
                    {h₁ : q1 < aut.scheme.size} {h₂ : q2 < aut.scheme.size}
                    : ExceptT String (StateM SAutomata) Unit :=
    match s₁.pol, s₂.pol with
      | .pos, .pos => do{
        let head := mergeHeads .pos (s₁.cons ++ s₂.cons);
        set ({scheme := aut.scheme.set q1 {pol := s₁.pol, cons := head, flow := s₁.flow ∪ s₂.flow}, env := aut.env, res := aut.res} : SAutomata)
        }
      | .neg, .neg =>
        let head := mergeHeads .neg (s₁.cons ++ s₂.cons);
        set ({scheme :=
            aut.scheme.set q1 {pol := s₁.pol, cons := head, flow := s₁.flow ∪ s₂.flow},
              env := aut.env, res := aut.res} : SAutomata)
      | _, _ => throw s!"Cannot merge states of distinct polarities"
    where
      s₁ := aut.scheme[q1]'h₁
      s₂ := aut.scheme[q2]'h₂

#eval detRoundTrip (.add (.cons (.rcd [("x", .add (.var "a3") (.var "a1")), ("y", .var "a2")])) (.cons (.func (.var "a1") (.var "a2"))))

#eval show_automata (.cons (.func (.var "a") (.var "a")))
#eval show_automata (.cons (.base 1 []))
#eval encode_typing (Std.HashMap.ofList [("x", .add (.var "a") (.cons (.func (.var "b") (.var "c"))))], (.add (.var "a") (.cons (.func (.var "b") (.var "c")))))
/-
Except.ok { scheme := #[{ pol := Types.Polarity.pos,
                cons := [Types.Head.func (Std.HashSet.ofList [2]) (Std.HashSet.ofList [3])],
                flow := Std.HashSet.ofList [1] },
              { pol := Types.Polarity.neg,
                cons := [Types.Head.func (Std.HashSet.ofList [4]) (Std.HashSet.ofList [5])],
                flow := Std.HashSet.ofList [0] },
              { pol := Types.Polarity.neg, cons := [], flow := Std.HashSet.ofList [4] },
              { pol := Types.Polarity.pos, cons := [], flow := Std.HashSet.ofList [5] },
              { pol := Types.Polarity.pos, cons := [], flow := Std.HashSet.ofList [2] },
              { pol := Types.Polarity.neg, cons := [], flow := Std.HashSet.ofList [3] }],
  env := Std.HashMap.ofList [("x", 1)],
  res := 0 }-/
#eval encode_typing (Std.HashMap.ofList [("x", (.cons (.func (.var "b") (.var "c"))))], (.cons (.func (.var "b") (.var "c"))))
/-
Except.ok { scheme := #[{ pol := Types.Polarity.pos,
                cons := [Types.Head.func (Std.HashSet.ofList [2]) (Std.HashSet.ofList [3])],
                flow := Std.HashSet.ofList [] },
              { pol := Types.Polarity.neg,
                cons := [Types.Head.func (Std.HashSet.ofList [4]) (Std.HashSet.ofList [5])],
                flow := Std.HashSet.ofList [] },
              { pol := Types.Polarity.neg, cons := [], flow := Std.HashSet.ofList [4] },
              { pol := Types.Polarity.pos, cons := [], flow := Std.HashSet.ofList [5] },
              { pol := Types.Polarity.pos, cons := [], flow := Std.HashSet.ofList [2] },
              { pol := Types.Polarity.neg, cons := [], flow := Std.HashSet.ofList [3] }],
  env := Std.HashMap.ofList [("x", 1)],
  res := 0 }-/

#eval simplify_typing ({}, .cons (.func (.cons (.func (.var "a") (.var "b"))) (.cons (.func (.var "a") (.var "b")))))
#eval encode_typing ({}, (.cons (.func (.var "b") (.cons (.func (.var "c") (.add (.var "b") (.var "c")))))))
#eval simplify_typing ({}, (.cons (.func (.var "a") (.cons (.func (.var "a") (.var "a"))))))
#eval simplify_typing ({}, (.cons (.func (.add (.cons (.func (.var "a") (.var "b"))) (.cons (.func (.var "b") (.var "c")))) (.cons (.func (.var "a") (.var "c"))))))
end Types
>>>>>>> 2a25d7c (- Add scratch of automata encoding of types)
