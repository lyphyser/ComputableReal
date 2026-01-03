import Mathlib.Data.Rat.Defs
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Prod.Lex
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

structure NTyPack where
  T : Type
  [toType : ToType T]

attribute [instance] NTyPack.toType

@[reducible] def NTyStruct : (n : Nat) → NTyPack
| 0 =>
  ⟨STy⟩
| n + 1 =>
  let prev := NTyStruct n
  letI : ToType prev.T := prev.toType
  ⟨XTy prev.T⟩

@[reducible] def NTy (n : Nat) : Type := (NTyStruct n).T
instance instToTypeNTy (n : Nat) : ToType (NTy n) :=
  (NTyStruct n).toType

-- Definition of CTy (Code Type) and Ty
def CTy := Σ n, NTy n

def Ty := CTy

instance : ToType Ty where
  toType t := toType t.2

-- Lift/Coercions

instance {P : Type} [ToType P] : Coe P (XTy P) where
  coe := XTy.lift

def lift_nty (m : Nat) {n : Nat} (x : NTy n) : NTy (n + m) :=
  match m with
  | 0 => x
  | m + 1 =>
    XTy.lift (lift_nty m x)

instance (n m : Nat) : Coe (NTy n) (NTy (n + m)) where
  coe := lift_nty m

instance {n} : CoeOut (NTy n) CTy where
  coe t := ⟨n, t⟩
