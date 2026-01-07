import Mathlib.Data.Rat.Defs
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.RelClasses
import Mathlib.Order.WithBot
import Mathlib.Data.Prod.Lex
import Batteries.Data.Vector
import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.HashSet

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type

export ToType (toType)

structure TyBundle where
  T : Type
  [toType : ToType T]

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

def XTy.toTypeRec {P} [ToType P] : XTy P → Type
  | .lift x => toType x
  | .prod x y => toTypeRec x × toTypeRec y
  | .sum x y => toTypeRec x ⊕ toTypeRec y
  | .vec x n => Vector (toTypeRec x) n
  | .array x => Array (toTypeRec x)
  | .list x => List (toTypeRec x)
  | .option x => Option (toTypeRec x)
  | .multiset x => Multiset (toTypeRec x)
  | .finset x => Finset (toTypeRec x)
  | .quot _ r => Quot r
  | .quotient _ s => Quotient s
  | .squash x => Squash (toTypeRec x)
  | .subtype x p => { a : toType x // p a }
  | XTy.hashmap k v => Std.HashMap (toType k) (toTypeRec v)
  | XTy.dhashmap k v => Std.DHashMap (toType k) (fun a => toTypeRec (v a))
  | XTy.hashset k => Std.HashSet (toType k)
  | XTy.treemap k v => Std.TreeMap (toType k) (toTypeRec v)
  | XTy.dtreemap k v => Std.DTreeMap (toType k) (fun a => toTypeRec (v a))
  | XTy.treeset k => Std.TreeSet (toType k)
  | .f x y => toTypeRec x → toTypeRec y
  | .sigma x y => (a : toType x) × toTypeRec (y a)
  | .pi x y => (a : toType x) → toTypeRec (y a)
  | .w d a b =>
      WType
        (fun (x : ((x : toType d) × toTypeRec (a x))) => toTypeRec (b x.1))
  | .thunk x => Thunk (toTypeRec x)

def instToTypeXTy {P} [ToType P] : ToType (XTy P) := ⟨XTy.toTypeRec⟩

-- Index Type with Lexicographic Order
abbrev Index (ι : Type) := Lex (WithBot ι × Nat)

variable {α ι : Type} [ToType α] [LinearOrder ι] [WellFoundedLT ι]

def PreNTyBundleStep (n : Index ι) (rec : (m : Index ι) → m < n → TyBundle) : TyBundle :=
  letI : LinearOrder (Index ι) := sorry
  match n with
  | (⊥, 0) => { T := α }
  | (u, k+1) =>
      let prev := rec (u, k) sorry
      -- We need ToType (prev.T).
      -- prev is TyBundle, so it has it.
      -- But XTy needs it.
      letI : ToType prev.T := prev.toType
      letI : ToType (XTy prev.T) := instToTypeXTy
      { T := XTy prev.T }
  | (some u, 0) =>
      let T := Σ m : { m : Index ι // m < (some u, 0) }, XTy (rec m.1 m.2).T
      letI : ToType T := { toType := fun ⟨m, val⟩ =>
          letI := TyBundle.toType (rec m.1 m.2)
          letI := instToTypeXTy
          toType val
        }
      { T := T }

def PreNTyBundle : Index ι → TyBundle :=
  (sorry : WellFoundedLT (Index ι)).wf.fix PreNTyBundleStep

theorem PreNTyBundle_eq (n : Index ι) :
    PreNTyBundle n = PreNTyBundleStep n (fun m _ => PreNTyBundle m) :=
  (sorry : WellFoundedLT (Index ι)).wf.fix_eq PreNTyBundleStep n

def NTy (n : Index ι) : Type :=
  letI : ToType (PreNTyBundle n).T := TyBundle.toType (PreNTyBundle n)
  letI : ToType (XTy (PreNTyBundle n).T) := instToTypeXTy
  XTy (PreNTyBundle n).T

instance instToTypeNTy (n : Index ι) : ToType (NTy n) :=
  inferInstance

-- Coercions

instance : Coe α (NTy (⊥, 0)) where
  coe x :=
    cast (by
      unfold NTy
      rw [PreNTyBundle_eq]
      rfl
    ) (XTy.lift x)

instance instCoeOutNTyTy {n : Index ι} : CoeOut (NTy n) (Σ n : Index ι, NTy n) where
  coe t := ⟨n, t⟩

-- Definition of Ty wrapper
def Ty (α ι : Type) [ToType α] [LinearOrder ι] [WellFoundedLT ι] := Σ n : Index ι, NTy n

instance : ToType (Ty α ι) where
  toType t := toType t.2

-- Lift logic

def NTy.lift {i j : Index ι} (h : i ≤ j) (x : NTy i) : NTy j := by
  letI : LinearOrder (Index ι) := sorry
  if h_eq : i = j then
    subst h_eq
    exact x
  else
    let rec go (k : Nat) (val : NTy i) : NTy j := sorry
    exact go 0 x

-- Constructors

variable {i j : Index ι}

def NTy.prod (x : NTy i) (y : NTy j) : NTy (max i j) :=
  letI : LinearOrder (Index ι) := sorry
  let c := max i j
  let x' : NTy c := NTy.lift (sorry) x
  let y' : NTy c := NTy.lift (sorry) y
  let P := (PreNTyBundle c).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle c)
  let x_val : XTy P := cast (by sorry) x'
  let y_val : XTy P := cast (by sorry) y'
  cast (by sorry) (@XTy.prod P inst x_val y_val)

def NTy.sum (x : NTy i) (y : NTy j) : NTy (max i j) :=
  letI : LinearOrder (Index ι) := sorry
  let c := max i j
  let x' : NTy c := NTy.lift (sorry) x
  let y' : NTy c := NTy.lift (sorry) y
  let P := (PreNTyBundle c).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle c)
  let x_val : XTy P := cast (by sorry) x'
  let y_val : XTy P := cast (by sorry) y'
  cast (by sorry) (@XTy.sum P inst x_val y_val)

def NTy.vec (x : NTy i) (n : Nat) : NTy i :=
  letI : LinearOrder (Index ι) := sorry
  let P := (PreNTyBundle i).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle i)
  let x_val : XTy P := cast (by sorry) x
  cast (by sorry) (@XTy.vec P inst x_val n)

def NTy.list (x : NTy i) : NTy i :=
  letI : LinearOrder (Index ι) := sorry
  let P := (PreNTyBundle i).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle i)
  let x_val : XTy P := cast (by sorry) x
  cast (by sorry) (@XTy.list P inst x_val)

def NTy.option (x : NTy i) : NTy i :=
  letI : LinearOrder (Index ι) := sorry
  let P := (PreNTyBundle i).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle i)
  let x_val : XTy P := cast (by sorry) x
  cast (by sorry) (@XTy.option P inst x_val)

def NTy.arrow (x : NTy i) (y : NTy j) : NTy (max i j) :=
  letI : LinearOrder (Index ι) := sorry
  let c := max i j
  let x' : NTy c := NTy.lift (sorry) x
  let y' : NTy c := NTy.lift (sorry) y
  let P := (PreNTyBundle c).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle c)
  let x_val : XTy P := cast (by sorry) x'
  let y_val : XTy P := cast (by sorry) y'
  cast (by sorry) (@XTy.f P inst x_val y_val)

-- Ty wrappers

namespace Ty

variable (x y : Ty STy ι)

def prod : Ty STy ι :=
  letI : LinearOrder (Index ι) := sorry
  let c := max x.1 y.1
  let x' : NTy c := NTy.lift (sorry) x.2
  let y' : NTy c := NTy.lift (sorry) y.2
  let P := (PreNTyBundle c).T
  let inst : ToType P := TyBundle.toType (PreNTyBundle c)
  let x_val : XTy P := cast (by sorry) x'
  let y_val : XTy P := cast (by sorry) y'
  ⟨c, cast (by sorry) (@XTy.prod P inst x_val y_val)⟩

end Ty
