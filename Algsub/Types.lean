import Mathlib.Tactic
<<<<<<< HEAD
import Algsub.Basic

-- graph-based representation of inference
=======
import Std.Data.HashMap
import Std.Data.HashSet
import Std.Data.TreeMap
open Lean hiding Environment Exception
open Meta


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
  decls : Std.HashMap ℕ (Symbol × Array Variance) := {}
  byName : Std.HashMap Symbol ℕ := {}

structure Typechecker.Context where
  env : TyCtx := {}

structure Typechecker.State where
  ngen : ℕ  := 0
  nvargen : ℕ := 0
  seen : Std.HashSet (StateId × StateId) := {}


abbrev M := ReaderT Context <| StateT Typechecker.State <| Except String

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
  | .rcd fs | .variant fs => .rcd <$> fs.mapM (fun (l, a) ↦ (l, · ) <$> f a)
  | .base k args => .base k <$> args.mapM (TyArg.mapM f)

def Ty.sum : List Ty → Ty
  | [] => .zero
  | [t] => t
  | t :: ts => .add t (Ty.sum ts)

def flow_vars (aut : Automata) (q : StateId) (s : State) : List Ty :=
  match s.pol with
    | .neg => if s.flow.isEmpty then [] else [.var s!"v{q}"]
    | .pos => s.flow.toList.filter (· < aut.size) |>.map (fun n ↦ .var s!"v{n}")

def flow_pair : M Automata := do{
  let id_pos ← mkFreshId;
  let id_neg ← mkFreshId;
  let pos : State := {pol := .pos, cons := [], flow := {id_neg}};
  let neg : State := {pol := .neg, cons := [], flow := {id_pos}};
  pure #[pos, neg]
}
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
  | .rcd fs | .variant fs => .rcd <$> fs.mapM (fun (l, a) ↦ (l, ·) <$> f p a)
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

-- Step 3: every node becomes a state holding the heads of its ε-closure;
-- flow edges join each negative and positive state mentioning the same variable.
-- Node `i` becomes state `start + i`, so the result can be appended to an automaton of size `start`
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
    let other := match p with | .pos => negOcc | .neg => posOcc;
    let flow := (varsOf i).foldl (fun s v ↦ s.insertMany (other.getD v [])) {};
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
      (Head.mapM fun (ss : Std.HashSet StateId) ↦ Std.HashSet.ofList <$> ss.toList.mapM intern)).run st;
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

def TyArg.union : TyArg (Std.HashSet StateId) → TyArg (Std.HashSet StateId) → TyArg (Std.HashSet StateId)
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
  let (cls, n) := classify <| A.map fun s ↦
    (s.pol, (s.cons.map Head.tag).mergeSort (fun a b ↦ (compare a b).isLE),
     Subset.ofSet s.flow);
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
  A.map fun s ↦ {pol := s.pol, cons := s.cons.map (Head.mapM (m := Id) fun d ↦ ({d} : Std.HashSet StateId)), flow := s.flow}

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

-- Convert type scheme to scheme automata. All types share one node array, so a variable occurring
-- in both the environment and the result gets flow edges between them; trimming from every root
-- at once then drops the ε-only nodes. Returns the root of each environment entry and of the result.
def encode_typing (typ : Typing) :
    Except String (Automata × Std.HashMap String StateId × StateId) := do{
  let (env, ty) := typ;
  let ((envRoots, root), nodes) ← (show FlatM _ from do{
    let envRoots ← env.toList.mapM fun (x, t) ↦ (x, ·) <$> flatten [] .neg t;
    pure (envRoots, ← flatten [] .pos ty)
  }).run #[];
  let (A, roots) := trim (toAutomata nodes) (root :: envRoots.map (·.2));
  pure (A, .ofList (envRoots.map (·.1) |>.zip roots.tail), roots.head!)
}


-- {x : a1, y : a2} ∩ {x : bool, y : a3} -> {x : bool, y : ⊥}
#eval show_automata (.add (.cons (.rcd [("x", .var "a1"), ("y", .var "a2")]))
              (.cons (.rcd [("x", (.cons (.base 1 []))), ("y", .var "a3")])))

#eval show_automata (.cons (.func (.var "a") (.var "a")))
#eval show_automata (.cons (.base 1 []))
#eval encode_typing (Std.HashMap.ofList [("x", Ty.var "a1")], (.cons (.base 1 [])))
#eval encode_typing (Std.HashMap.ofList [("x", .add (.var "c") (.cons (.func (.var "a") (.var "b"))))], (.add (.var "c") (.cons (.func (.var "a") (.var "b")))))
end Types
>>>>>>> 2a25d7c (- Add scratch of automata encoding of types)
