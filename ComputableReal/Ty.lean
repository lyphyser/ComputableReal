import Mathlib.Data.Rat.Defs
import Mathlib.Data.W.Basic
import Mathlib.SetTheory.Ordinal.Notation
import Mathlib.Data.Quot
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Batteries.Data.Vector
import Std.Data.HashMap
import Std.Data.DHashMap
import Std.Data.HashSet
import Batteries.Data.RBMap

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type
  isHash : α → Bool
  isOrd  : α → Bool
  -- Conditional instances
  instHash : ∀ x, isHash x → Hashable (toType x)
  instBEq  : ∀ x, (isHash x || isOrd x) → BEq (toType x)
  instOrd  : ∀ x, isOrd x → Ord (toType x)

export ToType (toType isHash isOrd instHash instBEq instOrd)

/-- Simple Types (Primitives) -/
inductive STy : Type where
| empty | unit | bool | fin (n : Nat)
| uint8 | uint16 | char | uint32 | uint64
| nat | rat | string | plift (p : Prop)
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

  isHash
  | .empty | .plift _ | .nonote => false
  | _ => true

  isOrd
  | .empty | .plift _ | .nonote => false
  | _ => true

  instHash s h := by
    cases s <;> try (simp [isHash] at h; done)
    all_goals exact inferInstance

  instBEq s cond := by
    cases s <;> try (simp [isHash, isOrd] at cond; done)
    all_goals exact inferInstance

  instOrd s o := by
    cases s <;> try (simp [isOrd] at o; done)
    all_goals exact inferInstance

/-- Complex Types indexed by Hashable (h) and Orderable (o) -/
inductive XTy (P : Type) [ToType P] : Bool → Bool → Type where
| lift (x : P) : XTy P (isHash x) (isOrd x)

-- Combinators
| prod {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2)
  : XTy P (h1 && h2) (o1 && o2)
| sum {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2)
  : XTy P (h1 && h2) (o1 && o2)
| vec {h o} (x : XTy P h o) (n : Nat)
  : XTy P h o
| array {h o} (x : XTy P h o)
  : XTy P h o
| list {h o} (x : XTy P h o)
  : XTy P h o
| option {h o} (x : XTy P h o)
  : XTy P h o

-- Collections
| multiset {h o} (x : XTy P h o)
  : XTy P false false
| finset {h o} (x : XTy P h o)
  : XTy P false false

-- Quotients and Squashing
-- quot takes P (previous level code) and a relation
| quot (x : P) (r : toType x → toType x → Prop)
  : XTy P false false
-- quotient takes P and a Setoid
| quotient (x : P) (s : Setoid (toType x))
  : XTy P false false
-- squash takes an XTy and resolves to Squash (subsingleton)
| squash {h o} (x : XTy P h o)
  : XTy P true true

-- Subtypes
| subtype {h o} (x : P) (p : toType x → Prop)
  : XTy P (isHash x && h) (isOrd x && o)

-- Maps/Sets
| hashmap {hv ov} (k : XTy P true ok) (v : XTy P hv ov)
  : XTy P false false
| dhashmap (k : XTy P true ok) (v : toType k → XTy P false false)
  : XTy P false false
| hashset (k : XTy P true ok)
  : XTy P false false

| treemap {hv ov} (k : XTy P hk true) (v : XTy P hv ov)
  : XTy P false false
| dtreemap (k : XTy P hk true) (v : toType k → XTy P false false)
  : XTy P false false
| treeset (k : XTy P hk true)
  : XTy P false false

-- Functional
| f {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2)
  : XTy P false false
| sigma (x : P) (y : toType x → XTy P false false)
  : XTy P false false
| pi (x : P) (y : toType x → XTy P false false)
  : XTy P false false
| w (d : P) (a : toType d → XTy P false false) (b : toType d → XTy P false false)
  : XTy P false false
| thunk {h o} (x : XTy P h o)
  : XTy P false false

/-- Helpers for instances on Squash --/
-- Squash α is usually defined as Quot (fun _ _ => True) or via Trunc
-- We ensure instances for the Squash type
instance : Hashable (Squash α) where hash _ := 0
instance : BEq (Squash α) where beq _ _ := true
instance : Ord (Squash α) where compare _ _ := .eq

/-- Decoding function for XTy -/
def XTy.toType {P : Type} [ToType P] {h o} : XTy P h o → Type
| .lift x => ToType.toType x
| .prod x y => XTy.toType x × XTy.toType y
| .sum x y => XTy.toType x ⊕ XTy.toType y
| .vec x n => Vector (XTy.toType x) n
| .array x => Array (XTy.toType x)
| .list x => List (XTy.toType x)
| .option x => Option (XTy.toType x)
| .multiset x => Multiset (XTy.toType x)
| .finset x => Finset (XTy.toType x)
| .quot x r => Quot r
| .quotient x s => Quotient s
| .squash x => Squash (XTy.toType x)
| .hashmap k v => Std.HashMap (XTy.toType k) (XTy.toType v)
| .dhashmap k v => Std.DHashMap (XTy.toType k) (fun a => XTy.toType (v a))
| .hashset k => Std.HashSet (XTy.toType k)
| .treemap k v => Batteries.RBMap (XTy.toType k) (XTy.toType v) compare
| .dtreemap k v => Batteries.RBMap (XTy.toType k) (fun a => XTy.toType (v a)) compare
| .treeset k => Batteries.RBSet (XTy.toType k) compare
| .f x y => XTy.toType x → XTy.toType y
| .sigma x y => (a : ToType.toType x) × XTy.toType (y a)
| .pi x y => (a : ToType.toType x) → XTy.toType (y a)
| .w d a b => WType (fun (x: ((x : ToType.toType d) × XTy.toType (a x))) => XTy.toType (b x.1))
| .subtype x p => { a : ToType.toType x // p a }
| .thunk x => Thunk (XTy.toType x)

-- Instances for XTy
instance {P : Type} [ToType P] {h o} (t : XTy P h o) (eq : h = true) : Hashable (XTy.toType t) := by
  induction t <;> try (simp at eq; done)
  case lift x => exact ToType.instHash x eq
  case squash x => exact inferInstance
  case prod x y ihx ihy =>
    simp at eq; exact @instHashProd _ _ (ihx eq.1) (ihy eq.2)
  case sum x y ihx ihy =>
    simp at eq; exact @instHashSum _ _ (ihx eq.1) (ihy eq.2)
  case vec x n ih => exact @Vector.instHash _ _ (ih eq)
  case array x ih => exact @Array.hashable _ (ih eq)
  case list x ih => exact @List.hashable _ (ih eq)
  case option x ih => exact @instHashOption _ (ih eq)
  case subtype x p =>
    simp at eq; exact @instHashSubtype _ _ (ToType.instHash x eq.1)

instance {P : Type} [ToType P] {h o} (t : XTy P h o) (eq : o = true) : Ord (XTy.toType t) := by
  induction t <;> try (simp at eq; done)
  case lift x => exact ToType.instOrd x eq
  case squash x => exact inferInstance
  case prod x y ihx ihy =>
    simp at eq; exact @instOrdProd _ _ (ihx eq.1) (ihy eq.2)
  case sum x y ihx ihy =>
    simp at eq; exact @instOrdSum _ _ (ihx eq.1) (ihy eq.2)
  case vec x n ih => exact @Vector.instOrd _ _ (ih eq)
  case array x ih => exact @Array.ord _ (ih eq)
  case list x ih => exact @List.instOrd _ (ih eq)
  case option x ih => exact @instOrdOption _ (ih eq)
  case subtype x p =>
    simp at eq; exact @instOrdSubtype _ _ (ToType.instOrd x eq.1)

instance {P : Type} [ToType P] {h o} (t : XTy P h o) (cond : h || o) : BEq (XTy.toType t) := by
  induction t
  case lift x => exact ToType.instBEq x cond
  case squash => exact inferInstance
  case prod x y ihx ihy =>
    have cx := Bool.or_and_distrib_right.mp cond
    exact @instBEqProd _ _ (ihx cx.1) (ihy cx.2)
  case sum x y ihx ihy =>
    have cx := Bool.or_and_distrib_right.mp cond
    exact @instBEqSum _ _ (ihx cx.1) (ihy cx.2)
  case vec x n ih => exact @Vector.instBEq _ _ (ih cond)
  case array x ih => exact @Array.be _ (ih cond)
  case list x ih => exact @List.instBEq _ (ih cond)
  case option x ih => exact @instBEqOption _ (ih cond)
  case subtype x p =>
    have ⟨_, _⟩ := Bool.or_and_distrib_right.mp cond
    exact @instBEqSubtype _ _ (ToType.instBEq x (by simp_all))
  all_goals try (simp at cond; done)

-- Universe Hierarchy Construction

abbrev NTy : (n : Nat) → Bool → Bool → Type
| 0 => fun h o => if h && o then STy else Empty
| n + 1 => fun h o =>
    let P := Σ h' o', NTy n h' o'
    XTy P h o

instance (n : Nat) : ToType (Σ h o, NTy n h o) where
  toType x := match n with
    | 0 => match x.1, x.2.1, x.2.2 with
      | true, true, s => ToType.toType s
      | _, _, e => Empty
    | n + 1 => XTy.toType x.2.2

  isHash x := x.1
  isOrd x := x.2.1

  instHash x h := match n with
    | 0 => match x.1, x.2.1, x.2.2 with
      | true, true, s => ToType.instHash s rfl
      | _, _, _ => by simp at h
    | n + 1 => by
       simp at h; apply (inferInstance : Hashable (XTy.toType x.2.2)) (eq := h)

  instBEq x cond := match n with
    | 0 => match x.1, x.2.1, x.2.2 with
      | true, true, s => ToType.instBEq s (by simp)
      | _, _, _ => by simp at cond
    | n + 1 => by
       apply (inferInstance : BEq (XTy.toType x.2.2)) (cond := cond)

  instOrd x o := match n with
    | 0 => match x.1, x.2.1, x.2.2 with
      | true, true, s => ToType.instOrd s rfl
      | _, _, _ => by simp at o
    | n + 1 => by
       simp at o; apply (inferInstance : Ord (XTy.toType x.2.2)) (eq := o)

-- Definition of CTy (Code Type) and Ty
def CTy (h o : Bool) := (n : Nat) × NTy n h o

instance {h o} : Coe (NTy n h o) (CTy h o) := ⟨fun t => ⟨n, t⟩⟩

def Ty := Σ (h o : Bool), CTy h o

instance : ToType Ty where
  toType t := match t.2.2.1 with
    | 0 => match t.1, t.2.1, t.2.2.2 with
       | true, true, s => ToType.toType s
       | _, _, e => Empty
    | n + 1 => XTy.toType t.2.2.2

  isHash t := t.1
  isOrd t  := t.2.1

  instHash t h := match t.2.2.1 with
    | 0 => match t.1, t.2.1, t.2.2.2 with
       | true, true, s => ToType.instHash s rfl
       | _, _, _ => by simp at h
    | n + 1 => by
       simp at h; apply (inferInstance : Hashable (XTy.toType t.2.2.2)) (eq := h)

  instBEq t cond := match t.2.2.1 with
    | 0 => match t.1, t.2.1, t.2.2.2 with
       | true, true, s => ToType.instBEq s (by simp)
       | _, _, _ => by simp at cond
    | n + 1 => by
       apply (inferInstance : BEq (XTy.toType t.2.2.2)) (cond := cond)

  instOrd t o := match t.2.2.1 with
    | 0 => match t.1, t.2.1, t.2.2.2 with
       | true, true, s => ToType.instOrd s rfl
       | _, _, _ => by simp at o
    | n + 1 => by
       simp at o; apply (inferInstance : Ord (XTy.toType t.2.2.2)) (eq := o)

-- Lift/Coercions

instance {P : Type} [ToType P] : Coe P (Σ h o, XTy P h o) where
  coe x := ⟨isHash x, isOrd x, XTy.lift x⟩

def lift_nty (m : Nat) {n : Nat} {h o} (x : NTy n h o) : NTy (n + m) h o :=
  match m with
  | 0 => x
  | m + 1 =>
      let x' := lift_nty m x
      XTy.lift (⟨h, o, x'⟩ : Σ h o, NTy (n+m) h o)

instance (n m : Nat) {h o} : Coe (NTy n h o) (NTy (n + m) h o) where
  coe := lift_nty m

instance {n h o} : CoeOut (NTy n h o) (CTy h o) where
  coe t := ⟨n, t⟩

instance {h o} : CoeOut (CTy h o) Ty where
  coe t := ⟨h, o, t⟩
