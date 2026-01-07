import Mathlib.Data.Rat.Defs
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.WithBot
import Batteries.Data.Vector
import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.HashSet

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type

export ToType (toType)

inductive STy : Type where
| empty
| unit
| bool
| fin (n : Nat)
| uint8
| uint16
| char
| uint32
| uint64
| nat
| rat
| string
| plift (p : Prop)
| nonote

instance : ToType STy where
  toType
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .fin n => Fin n
  | .uint8 => UInt8
  | .uint16 => UInt16
  | .char => Char
  | .uint32 => UInt32
  | .uint64 => UInt64
  | .nat => Nat
  | .rat => Rat
  | .string => String
  | .plift p => PLift p
  | .nonote => NONote

inductive XTy (P : Type) [ToType P] : Type where
| lift (x : P) : XTy P
| prod (x y : XTy P) : XTy P
| sum (x y : XTy P) : XTy P
| vec (x : XTy P) (n : Nat) : XTy P
| array (x : XTy P) : XTy P
| list (x : XTy P) : XTy P
| option (x : XTy P) : XTy P
| multiset (x : XTy P) : XTy P
| finset (x : XTy P) : XTy P
| quot (x : P) (r : toType x → toType x → Prop) : XTy P
| quotient (x : P) (s : Setoid (toType x)) : XTy P
| squash (x : XTy P) : XTy P
| subtype (x : P) (p : toType x → Prop) : XTy P
| hashmap (k : P) [Hashable (toType k)] [BEq (toType k)] (v : XTy P) : XTy P
| dhashmap (k : P) [Hashable (toType k)] [BEq (toType k)]
    (v : toType k → XTy P) : XTy P
| hashset (k : P) [Hashable (toType k)] [BEq (toType k)] : XTy P
| treemap (k : P) [Ord (toType k)] (v : XTy P) : XTy P
| dtreemap (k : P) [Ord (toType k)] (v : toType k → XTy P) : XTy P
| treeset (k : P) [Ord (toType k)] : XTy P
| f (x y : XTy P) : XTy P
| sigma (x : P) (y : toType x → XTy P) : XTy P
| pi (x : P) (y : toType x → XTy P) : XTy P
| w (d : P) (a b : toType d → XTy P) : XTy P
| thunk (x : XTy P) : XTy P

instance {P} [ToType P] : ToType (XTy P) where
  toType t :=
    let rec go : XTy P → Type
      | .lift x => toType x
      | .prod x y => go x × go y
      | .sum x y => go x ⊕ go y
      | .vec x n => Vector (go x) n
      | .array x => Array (go x)
      | .list x => List (go x)
      | .option x => Option (go x)
      | .multiset x => Multiset (go x)
      | .finset x => Finset (go x)
      | .quot _ r => Quot r
      | .quotient _ s => Quotient s
      | .squash x => Squash (go x)
      | .subtype x p => { a : toType x // p a }
      | XTy.hashmap k v => Std.HashMap (toType k) (go v)
      | XTy.dhashmap k v => Std.DHashMap (toType k) (fun a => go (v a))
      | XTy.hashset k => Std.HashSet (toType k)
      | XTy.treemap k v => Std.TreeMap (toType k) (go v)
      | XTy.dtreemap k v => Std.DTreeMap (toType k) (fun a => go (v a))
      | XTy.treeset k => Std.TreeSet (toType k)
      | .f x y => go x → go y
      | .sigma x y => (a : toType x) × go (y a)
      | .pi x y => (a : toType x) → go (y a)
      | .w d a b =>
          WType
            (fun (x : ((x : toType d) × go (a x))) => go (b x.1))
      | .thunk x => Thunk (go x)
    go t

-- Universe Hierarchy Construction

structure TyBundle where
  T : Type
  [toType : ToType T]

attribute [instance] TyBundle.toType

@[reducible] def iterXTyBundle (P : Type) [ToType P] : Nat → TyBundle
  | 0 => ⟨P⟩
  | n + 1 =>
      let prev := iterXTyBundle P n
      letI : ToType prev.T := prev.toType
      ⟨XTy prev.T⟩

@[reducible] def IterXTy (n : Nat) (P : Type) [ToType P] : Type :=
  (iterXTyBundle P n).T

instance instToTypeIterXTy (n : Nat) (P : Type) [ToType P] : ToType (IterXTy n P) :=
  (iterXTyBundle P n).toType

@[reducible] def nTyLimitBundle {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι] : ι → TyBundle :=
  (inferInstance : WellFoundedLT ι).wf.fix fun i rec =>
    let baseBundle : { x : WithBot ι // x < i } → TyBundle
      | ⟨⊥, _⟩ => ⟨α⟩
      | ⟨some a, ha⟩ =>
          have ha' : a < i := by
            cases ha with
            | coe_lt_coe h => exact h
          rec a ha'
    let T :=
      Σ x : { x : WithBot ι // x < i }, Σ n : Nat,
        IterXTy n (baseBundle x).T
    letI : ToType T :=
      { toType := fun t =>
          let ⟨x, n, v⟩ := t
          letI : ToType (baseBundle x).T := (baseBundle x).toType
          letI : ToType (IterXTy n (baseBundle x).T) :=
            instToTypeIterXTy n (baseBundle x).T
          toType v }
    ⟨T⟩

abbrev TyIndex (ι : Type) := WithBot ι × Nat

def pred {ι} (i : TyIndex ι) : TyIndex ι := (i.1, i.2 - 1)
def succ {ι} (i : TyIndex ι) : TyIndex ι := (i.1, i.2 + 1)

@[simp]
lemma pred_succ {ι} (i : TyIndex ι) : pred (succ i) = i := by
  simp [pred, succ]

abbrev isSucc {ι} (i : TyIndex ι) : Prop := i.2 ≠ 0

lemma isSucc_succ {ι} (i : TyIndex ι) : isSucc (succ i) := by
  simp [isSucc, succ]

lemma succ_pred {ι} {i : TyIndex ι} (h : isSucc i) : succ (pred i) = i := by
  cases i
  simp [pred, succ]
  apply Nat.succ_pred
  exact h

def toXTyIdx {ι} (i : TyIndex ι) : TyIndex ι := if isSucc i then i else succ i

lemma isSucc_toXTyIdx {ι} (i : TyIndex ι) : isSucc (toXTyIdx i) := by
  unfold toXTyIdx
  split
  · assumption
  · apply isSucc_succ

lemma pred_toXTyIdx {ι} (i : TyIndex ι) : pred (toXTyIdx i) = pred i := by
  unfold toXTyIdx
  split
  · rfl
  · rw [pred_succ]
    unfold isSucc at *
    cases i; simp at *
    apply Nat.sub_eq_zero_of_le
    exact Nat.one_le_iff_ne_zero.not.mp ‹_›

@[reducible] def nTyBundle {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι] :
    (n : TyIndex ι) → TyBundle
  | (i, k) =>
      let base : TyBundle := match i with
        | ⊥ => ⟨α⟩
        | some i => nTyLimitBundle (α:=α) (ι:=ι) i
      letI : ToType base.T := base.toType
      iterXTyBundle base.T k

@[reducible] def NTy {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι]
    (n : TyIndex ι) : Type :=
  (nTyBundle (α:=α) (ι:=ι) n).T
instance instToTypeNTy {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι]
    (n : TyIndex ι) : ToType (NTy (α:=α) (ι:=ι) n) :=
  (nTyBundle (α:=α) (ι:=ι) n).toType

lemma NTy_eq_XTy_pred {α ι} [ToType α] [LT ι] [WellFoundedLT ι] (i : TyIndex ι) (h : isSucc i) :
    NTy (α:=α) (ι:=ι) i = XTy (NTy (α:=α) (ι:=ι) (pred i)) := by
  unfold NTy nTyBundle
  cases i with | mk i k =>
  dsimp
  dsimp [pred]
  have : k = k - 1 + 1 := by
    rw [Nat.sub_add_cancel]
    exact Nat.pos_of_ne_zero h
  rw [this, iterXTyBundle]
  rfl

lemma NTy_toXTyIdx {α ι} [ToType α] [LT ι] [WellFoundedLT ι] (i : TyIndex ι) :
    NTy (α:=α) (ι:=ι) (toXTyIdx i) = XTy (NTy (α:=α) (ι:=ι) (pred i)) := by
  rw [NTy_eq_XTy_pred _ (isSucc_toXTyIdx i)]
  rw [pred_toXTyIdx]

-- Definition of Ty
def Ty (α ι : Type) [ToType α] [LT ι] [WellFoundedLT ι] := Σ n : TyIndex ι, NTy (α:=α) (ι:=ι) n

instance {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι] : ToType (Ty α ι) where
  toType t := toType t.2

-- Lift/Coercions

instance {P : Type} [ToType P] : Coe P (XTy P) where
  coe := XTy.lift

instance {α ι : Type} [ToType α] [LT ι] [WellFoundedLT ι] {n : TyIndex ι} :
    CoeOut (NTy (α:=α) (ι:=ι) n) (Ty α ι) where
  coe t := ⟨n, t⟩
