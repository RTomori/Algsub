import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.AList

inductive Typ where
  | typ_base : Typ
  | Typ_arrow : Typ → Typ → Typ

inductive Exp where
  | bvar : ℕ → Exp
  | fvar : String → Exp
  | abs : Exp → Exp
  | app : Exp → Exp → Exp
  deriving BEq

def Exp.ofNat (n : Nat) : Exp := Exp.bvar n
def Exp.ofString (x : String) : Exp := Exp.fvar x

instance : Coe Nat Exp where
  coe n := Exp.ofNat n

instance : Coe String Exp where
  coe x := Exp.ofString x

@[simp, grind]
def subst (z : String) (u : Exp) (e : Exp) : Exp :=
  match e with
    | Exp.bvar i => Exp.bvar i
    | Exp.fvar x => if x = z then u else (Exp.fvar x)
    | Exp.abs e1 => Exp.abs (subst z u e1)
    | Exp.app e1 e2 => Exp.app (subst z u e1) (subst z u e2)


notation : 67 "[" x "↦" u "]" e => subst x u e

@[simp, grind]
def fv (e : Exp) : Set String :=
  match e with
    | Exp.bvar _ => {}
    | Exp.fvar x => {x}
    | Exp.abs e => fv e
    | Exp.app e1 e2 => fv e1 ∪   fv e2

lemma subst_fresh : ∀ x e u,  x ∉ fv e → ([x ↦ u] e) = e := by
  intros x e u he
  induction e with
    | bvar i => simp
    | fvar y => simp at he; simp; intro hy; apply False.elim (he (Eq.symm hy))
    | app e1 e2 ih1 ih2 =>
      simp at he; simp; apply And.intro;
      · apply ih1; exact he.left
      · apply ih2; exact he.right
    | abs e he' => simp; apply he'; simp at he; exact he

@[simp]
def open_rec (k : ℕ) (u : Exp) : Exp → Exp
  | Exp.bvar i => if k = i then u else Exp.bvar i
  | Exp.fvar x => Exp.fvar x
  | Exp.abs e1 => Exp.abs (open_rec (k + 1) u e1)
  | Exp.app e1 e2 => Exp.app (open_rec k u e1) (open_rec k u e2)

notation :67 "{" k "↦" u "}" t => open_rec k u t

@[simp, grind]
def Exp.open e u := open_rec 0 u e

lemma demo_open :
  ∀ Y,  Exp.open (Exp.app (Exp.abs (Exp.app (Exp.bvar 1) (Exp.bvar 0))) (Exp.bvar 0)) Y = Exp.app (Exp.abs (Exp.app Y (Exp.bvar 0))) Y := by
    intro Y; simp

inductive lc : Exp → Prop where
  | lc_var : ∀ x, lc (Exp.fvar x)
  | lc_abs : ∀ (L : Finset String) e, (∀ x ∉ L , lc (Exp.open e x)) → lc (Exp.abs e)
  | lc_app : ∀ e1 e2, lc e1 → lc e2 → lc (Exp.app e1 e2)

lemma open_rec_lc_0 : ∀ k u e, lc e → e = {k ↦ u} e := by
  intros k u e hlc
  induction hlc generalizing k with
    | lc_var x => simp
    | lc_app e1 e2 hlc1 hlc2 he1 he2 =>
        simp; grind
    | lc_abs x e hlce he => simp; simp at he; sorry

lemma open_rec_lc_core : ∀ e j v i u, i ≠ j →
     ({j ↦ v} e) = ({i ↦ u}({j ↦ v} e)) → (e = ({i ↦ u} e)) := by
  intro e j v i u Neq H
  induction e generalizing i j with
    | fvar x => simp
    | bvar n =>
        simp; intro hin;
        cases (eq_or_ne j n) with
          | inl hjn =>
              cases (eq_or_ne i n) with
                | inl hin => have hij : i = j := Eq.trans hin (Eq.symm hjn);
                                       apply False.elim (Neq hij)
                | inr hnin => apply False.elim (hnin hin)
          | inr hnjn =>
              cases (eq_or_ne i n) with
                | inl hin => simp[hin, hnjn] at H; grind
                | inr hnin => apply False.elim (hnin hin)
    | abs e IHe =>
        simp
        simp at H; grind
    | app e1 e2 he1 he2 =>
        simp; apply And.intro <;> simp at H
        · grind
        · grind

@[simp, grind =_]
lemma open_rec_lc : ∀ k u e, lc e → e = {k ↦ u} e := by
  intros k u e LC;
  induction LC generalizing k with
    | lc_var x => simp
    | lc_abs L e1 hlc1 ih1 => sorry
    | lc_app e1 e2 hlc1 hlc2 ih1 ih2 => simp; grind

lemma subst_open_rec :
  ∀ e1 e2 u x k, lc u → ([x ↦ u] ({k ↦ e2} e1)) = ({k ↦ [x ↦ u] e2} ([x↦ u] e1)) := by
  intros e1 e2 u x k hlc
  induction e1 with
    | fvar y =>
        cases eq_or_ne x y with
          | inl hxy => simp[hxy]; grind
          | inr hnxy => have hnyx : y≠ x := Ne.symm hnxy; simp[hnyx]
    | bvar i =>
          cases eq_or_ne i k with
            | inl hik => simp[hik]
            | inr hnik => simp; grind
    | abs e1 he1 => simp; sorry
    | app e e' he he' => simp; grind

lemma subst_open_var :
  ∀ x y u e, y ≠ x → lc u → Exp.open ([x ↦ u] e) y = [x ↦ u] (Exp.open e y) := by
  intros x y u e hyx hlc
  induction e with
    | fvar w =>
        cases eq_or_ne w x with
          | inl hwx => simp[hwx]; grind
          | inr hnwx => simp[hnwx]
    | bvar i =>
        cases i with
          | zero => sorry
          | succ n' => simp
    | abs e1 he1 => simp; sorry
    | app e1 e2 he1 he2 =>
      simp; apply And.intro
      · grind
      · grind

lemma subst_lc : ∀   x u e, lc e → lc u → lc ([x ↦ u] e) := by
  intros x u e He Hu
  induction He with
    | lc_var y =>
          cases eq_or_ne y x with
            | inl hxy => grind
            | inr hnyx => simp[hnyx]; apply lc.lc_var
    | lc_abs L e0 Hlc IHe0 => sorry
    | lc_app e1 e2 hlc1 hlc2 IHe1 IHe2 => simp; apply lc.lc_app <;> grind

variable [DecidableEq α]
abbrev Context := List (String × Typ)

def toKeys (Γ : Context) : List String :=
  match Γ with
    | [] => []
    | (name, _) :: cs => name :: toKeys cs

def mem (Γ : Context) : Finset String := (toKeys Γ).toFinset

def get (x : String) : Context → Option Typ
  | [] => Option.none
  | (y, a) :: E' => if x = y then Option.some a else get x E'

inductive ok : Context → Prop where
  | ok_nil : ok []
  | ok_cons : ∀ E x a, ok E → x ∉ mem E → ok ((x , a) :: E)

def binds x b (E : Context) := get x E = Option.some b

inductive Typing : Context → Exp → Typ → Prop where
  | typing_var : ∀ E x T, ok E → binds x T E → Typing E x T
  | typing_abs : ∀ (L : Finset String) E e T1 T2,
        (∀ x ∉ L, (Typing ((x, T1) :: E) (Exp.open e x) T2))
        → Typing E (e.abs) (Typ.Typ_arrow T1 T2)
  | typing_app : ∀ E e1 e2 T1 T2, Typing E e1 (Typ.Typ_arrow T1 T2) → Typing E e2 T1
        → Typing E (e1.app e2) T2

lemma weakening' : ∀ E F e T, Typing E e T → ok (E ++ F) → Typing (E ++ F) e T := by sorry
