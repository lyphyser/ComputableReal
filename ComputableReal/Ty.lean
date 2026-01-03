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

structure Decoded (h o : Bool) where
  type : Type
  hashable : h = true → Hashable type := by
    intro _; exfalso; contradiction
  ord : o = true → Ord type := by
    intro _; exfalso; contradiction
  beq : h = true ∨ o = true → BEq type := by
    intro _; exfalso; contradiction

def Decoded.map {h o} (d : Decoded h o) (f : Type → Type)
    (hashable : ∀ (α : Type) [Hashable α], Hashable (f α) := by
      intro α inst; infer_instance)
    (ord : ∀ (α : Type) [Ord α], Ord (f α) := by
      intro α inst; infer_instance)
    (beq : ∀ (α : Type) [BEq α], BEq (f α) := by
      intro α inst; infer_instance) : Decoded h o :=
  {
    type := f d.type
    hashable := fun heq => by
      haveI := d.hashable heq
      exact (hashable d.type)
    ord := fun oeq => by
      haveI := d.ord oeq
      exact (ord d.type)
    beq := fun hbeq => by
      haveI := d.beq hbeq
      exact (beq d.type)
  }

def Decoded.map2 {h1 o1 h2 o2} (d1 : Decoded h1 o1) (d2 : Decoded h2 o2)
    (f : Type → Type → Type)
    (hashable : ∀ (α β : Type) [Hashable α] [Hashable β], Hashable (f α β) := by
      intro α β instα instβ; infer_instance)
    (ord : ∀ (α β : Type) [Ord α] [Ord β], Ord (f α β) := by
      intro α β instα instβ; infer_instance)
    (beq : ∀ (α β : Type) [BEq α] [BEq β], BEq (f α β) := by
      intro α β instα instβ; infer_instance) :
    Decoded (h1 && h2) (o1 && o2) :=
  {
    type := f d1.type d2.type
    hashable := fun heq => by
      have h_and : h1 = true ∧ h2 = true := by simp_all [Bool.and_eq_true]
      haveI := d1.hashable h_and.1
      haveI := d2.hashable h_and.2
      exact (hashable d1.type d2.type)
    ord := fun oeq => by
      have o_and : o1 = true ∧ o2 = true := by simp_all [Bool.and_eq_true]
      haveI := d1.ord o_and.1
      haveI := d2.ord o_and.2
      exact (ord d1.type d2.type)
    beq := fun hbeq => by
      have c1 : h1 = true ∨ o1 = true := by
        cases hbeq <;> simp_all [Bool.and_eq_true]
      have c2 : h2 = true ∨ o2 = true := by
        cases hbeq <;> simp_all [Bool.and_eq_true]
      haveI := d1.beq c1
      haveI := d2.beq c2
      exact (beq d1.type d2.type)
  }

class Decodable (α : Type) (h o : outParam Bool) where
  decode : α → Decoded h o

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type

instance instToTypeDecodable {α h o} [Decodable α h o] : ToType α where
  toType x := (Decodable.decode x).type

export ToType (toType)

-- Instances for primitives
instance : Hashable Empty where hash _ := 0
instance : Ord Empty where compare _ _ := .eq
instance : BEq Empty where beq _ _ := true

instance : Hashable (PLift p) where hash _ := 0
instance : Ord (PLift p) where compare _ _ := .eq
instance : BEq (PLift p) where beq _ _ := true

deriving instance Hashable for PNat

instance : Hashable NONote where
  hash o := o.recOn 0 (fun _ n _ _ he ha => mixHash (mixHash he (hash n)) ha)
instance : Ord NONote where compare := NONote.cmp

instance : Hashable Rat where hash x := mixHash (hash x.num) (hash x.den)

instance [Hashable α] [Hashable β] : Hashable (α ⊕ β) where
  hash
  | .inl a => mixHash 0 (hash a)
  | .inr b => mixHash 1 (hash b)

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := compare (toLex x) (toLex y)

instance [Ord α] [Ord β] : Ord (α ⊕ β) where
  compare
  | .inl a, .inl b => compare a b
  | .inl _, .inr _ => .lt
  | .inr _, .inl _ => .gt
  | .inr a, .inr b => compare a b

instance [Hashable α] : Hashable (Vector α n) where
  hash v := hash v.toArray

instance [Hashable α] {p : α → Prop} : Hashable { x // p x } where
  hash x := hash x.val

instance [Ord α] {p : α → Prop} : Ord { x // p x } where
  compare x y := compare x.val y.val

instance [BEq α] {p : α → Prop} : BEq { x // p x } where
  beq x y := x.val == y.val

-- Squash is already defined in Mathlib
instance : Hashable (Squash α) where hash _ := 0
instance : BEq (Squash α) where beq _ _ := true
instance : Ord (Squash α) where compare _ _ := .eq

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

def STy.toType : STy → Type
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

instance : Decodable STy true true where
  decode s :=
    {
      type := STy.toType s
      hashable := fun _ => by
        cases s <;> (simp [STy.toType] at *; infer_instance)
      ord := fun _ => by
        cases s <;> (simp [STy.toType] at *; infer_instance)
      beq := fun _ => by
        cases s <;> (simp [STy.toType] at *; infer_instance)
    }

instance {P : Bool → Bool → Type} [∀ h o, Decodable (P h o) h o] {o} (x : P true o) :
    Hashable (toType x) :=
  (Decodable.decode x).hashable rfl

instance {P : Bool → Bool → Type} [∀ h o, Decodable (P h o) h o] {h} (x : P h true) :
    Ord (toType x) :=
  (Decodable.decode x).ord rfl

instance {P : Bool → Bool → Type} [∀ h o, Decodable (P h o) h o] {o} (x : P true o) :
    BEq (toType x) :=
  (Decodable.decode x).beq (Or.inl rfl)

instance {P : Bool → Bool → Type} [∀ h o, Decodable (P h o) h o] {h} (x : P h true) :
    BEq (toType x) :=
  (Decodable.decode x).beq (Or.inr rfl)

inductive XTy (P : Bool → Bool → Type) [∀ h o, ToType (P h o)] : Bool → Bool → Type where
| lift {h o} (x : P h o) : XTy P h o
| prod {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P (h1 && h2) (o1 && o2)
| sum {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P (h1 && h2) (o1 && o2)
| vec {h o} (x : XTy P h o) (n : Nat) : XTy P h o
| array {h o} (x : XTy P h o) : XTy P h o
| list {h o} (x : XTy P h o) : XTy P h o
| option {h o} (x : XTy P h o) : XTy P h o
| multiset {h o} (x : XTy P h o) : XTy P false false
| finset {h o} (x : XTy P h o) : XTy P false false
| quot {h o} (x : P h o) (r : toType x → toType x → Prop) : XTy P false false
| quotient {h o} (x : P h o) (s : Setoid (toType x)) : XTy P false false
| squash {h o} (x : XTy P h o) : XTy P true true
| subtype {h o} (x : P h o) (p : toType x → Prop) : XTy P h o
| hashmap {hv ov} (k : XTy P true ok) (v : XTy P hv ov) : XTy P false false
| dhashmap {ok} (k : P true ok) (v : toType k → XTy P false false) : XTy P false false
| hashset (k : XTy P true ok) : XTy P false false
| treemap {hv ov} (k : XTy P hk true) (v : XTy P hv ov) : XTy P false false
| dtreemap {hk} (k : P hk true) (v : toType k → XTy P false false) : XTy P false false
| treeset (k : XTy P hk true) : XTy P false false
| f {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P false false
| sigma {h o} (x : P h o) (y : toType x → XTy P false false) : XTy P false false
| pi {h o} (x : P h o) (y : toType x → XTy P false false) : XTy P false false
| w {h o} (d : P h o) (a : toType d → XTy P false false) (b : toType d → XTy P false false) : XTy P false false
| thunk {h o} (x : XTy P h o) : XTy P false false

def decode {P} [∀ h o, Decodable (P h o) h o] {h o} (t : XTy P h o) : Decoded h o :=
  match t with
  | .lift x =>
      Decodable.decode x
  | .prod x y =>
      Decoded.map2 (decode x) (decode y) (· × ·)
  | .sum x y =>
      Decoded.map2 (decode x) (decode y) (· ⊕ ·)
  | .vec x n =>
      (decode x).map (fun t => Vector t n)
  | .array x =>
      (decode x).map Array
  | .list x =>
      (decode x).map List
  | .option x =>
      (decode x).map Option
  | .multiset x =>
      { type := Multiset (decode x).type }
  | .finset x =>
      { type := Finset (decode x).type }
  | .quot x r =>
      { type := Quot r }
  | .quotient x s =>
      { type := Quotient s }
  | .squash x =>
      {
        type := Squash (decode x).type
        hashable := fun _ => inferInstance
        ord := fun _ => inferInstance
        beq := fun _ => inferInstance
      }
  | .subtype x p =>
      let d := Decodable.decode x
      {
        type := { a : toType x // p a }
        hashable := fun heq => by
          haveI := d.hashable heq
          infer_instance
        ord := fun oeq => by
          haveI := d.ord oeq
          infer_instance
        beq := fun beq => by
          haveI := d.beq beq
          infer_instance
      }
  | .hashmap k v =>
      let kd := decode k
      let vd := decode v
      haveI := kd.hashable rfl
      haveI := kd.beq (Or.inl rfl)
      { type := Std.HashMap kd.type vd.type }
  | .dhashmap k v =>
      let kd := Decodable.decode k
      haveI := kd.hashable rfl
      haveI := kd.beq (Or.inl rfl)
      { type := Std.DHashMap kd.type (fun a => (decode (v a)).type) }
  | .hashset k =>
      let kd := decode k
      haveI := kd.hashable rfl
      haveI := kd.beq (Or.inl rfl)
      { type := Std.HashSet kd.type }
  | .treemap k v =>
      let kd := decode k
      let vd := decode v
      haveI := kd.ord rfl
      { type := Std.TreeMap kd.type vd.type }
  | .dtreemap k v =>
      let kd := Decodable.decode k
      haveI := kd.ord rfl
      { type := Std.DTreeMap kd.type (fun a => (decode (v a)).type) }
  | .treeset k =>
      let kd := decode k
      haveI := kd.ord rfl
      { type := Std.TreeSet kd.type }
  | .f x y =>
      { type := (decode x).type → (decode y).type }
  | .sigma x y =>
      { type := (a : toType x) × (decode (y a)).type }
  | .pi x y =>
      { type := (a : toType x) → (decode (y a)).type }
  | .w d a b =>
      {
        type := WType
          (fun (x : ((x : toType d) × (decode (a x)).type)) => (decode (b x.1)).type)
      }
  | .thunk x =>
      { type := Thunk (decode x).type }

instance instDecodableXTy {P} [∀ h o, Decodable (P h o) h o] {h o} :
    Decodable (XTy P h o) h o where
  decode := decode

-- Universe Hierarchy Construction

structure NTyPack where
  T : Bool → Bool → Type
  [decodable : ∀ h o, Decodable (T h o) h o]

attribute [instance] NTyPack.decodable

@[reducible] def NTyStruct : (n : Nat) → NTyPack
| 0 =>
  let T := fun h o => if h && o then STy else Empty
  letI : ∀ h o, Decodable (T h o) h o
    | true, true =>
        {
          decode := fun x =>
            {
              type := STy.toType (show STy from x)
              hashable := fun _ => by
                cases x <;> (simp [STy.toType] at *; infer_instance)
              ord := fun _ => by
                cases x <;> (simp [STy.toType] at *; infer_instance)
              beq := fun _ => by
                cases x <;> (simp [STy.toType] at *; infer_instance)
            }
        }
    | true, false
    | false, true
    | false, false =>
        {
          decode := by
            intro x
            cases x
        }
  ⟨T⟩
| n + 1 =>
  let prev := NTyStruct n
  letI : ∀ h o, Decodable (prev.T h o) h o := prev.decodable
  let T := fun h o => XTy prev.T h o
  letI : ∀ h o, Decodable (T h o) h o := by
    intro h o
    infer_instance
  ⟨T⟩

@[reducible] def NTy (n : Nat) (h o : Bool) : Type := (NTyStruct n).T h o
instance instDecodableNTy (n : Nat) : ∀ h o, Decodable (NTy n h o) h o :=
  (NTyStruct n).decodable

-- Definition of CTy (Code Type) and Ty
def CTy (h o : Bool) := (n : Nat) × NTy n h o

def Ty := Σ (h o : Bool), CTy h o

instance : ToType Ty where
  toType t := toType t.2.2.2

-- Lift/Coercions

instance {P : Bool → Bool → Type} [∀ h o, ToType (P h o)] {h o} :
    Coe (P h o) (XTy P h o) where
  coe := XTy.lift

def lift_nty (m : Nat) {n : Nat} {h o} (x : NTy n h o) : NTy (n + m) h o :=
  match m with
  | 0 => x
  | m + 1 =>
    XTy.lift (lift_nty m x)

instance (n m : Nat) {h o} : Coe (NTy n h o) (NTy (n + m) h o) where
  coe := lift_nty m

instance {n h o} : CoeOut (NTy n h o) (CTy h o) where
  coe t := ⟨n, t⟩

instance {h o} : CoeOut (CTy h o) Ty where
  coe t := ⟨h, o, t⟩
