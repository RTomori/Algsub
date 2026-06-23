import Mathlib.Tactic
import Std.Data.TreeMap
import Std.Data.HashSet

inductive Ty : Type where
  | Ty_Top : Ty
  | Ty_Bot : Ty
  | Ty_Bool : Ty
  | Ty_Join : Ty → Ty → Ty
  | Ty_Meet : Ty → Ty → Ty
  | Ty_RNil : Ty
  | Ty_RCons : String → Ty → Ty → Ty
  | Ty_Arrow : Ty → Ty → Ty
