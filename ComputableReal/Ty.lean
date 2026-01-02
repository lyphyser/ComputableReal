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
import Std.Data.TreeMap
import Std.Data.TreeSet
import Mathlib.Data.Prod.Lex

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type
  isHash : α → Bool
  isOrd : α → Bool
  instHash : (x : α) → isHash x = true → Hashable (toType x)
  instBEq : (x : α) → (isHash x = true ∨ isOrd x = true) → BEq (toType x)
  instOrd : (x : α) → isOrd x = true → Ord (toType x)

export ToType (toType isHash isOrd instHash instBEq instOrd)

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

instance [Ord α] [Ord β] : Ord (α × β) := inferInstanceAs (Ord (Lex (α × β)))

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

  isHash _ := true
  isOrd _ := true

  instHash s _ := by cases s <;> exact inferInstance
  instBEq s _ := by cases s <;> exact inferInstance
  instOrd s _ := by cases s <;> exact inferInstance

inductive XTy (P : Type) [ToType P] : Bool → Bool → Type where
| lift (x : P) : XTy P (isHash x) (isOrd x)
| prod {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P (h1 && h2) (o1 && o2)
| sum {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P (h1 && h2) (o1 && o2)
| vec {h o} (x : XTy P h o) (n : Nat) : XTy P h o
| array {h o} (x : XTy P h o) : XTy P h o
| list {h o} (x : XTy P h o) : XTy P h o
| option {h o} (x : XTy P h o) : XTy P h o
| multiset {h o} (x : XTy P h o) : XTy P false false
| finset {h o} (x : XTy P h o) : XTy P false false
| quot (x : P) (r : toType x → toType x → Prop) : XTy P false false
| quotient (x : P) (s : Setoid (toType x)) : XTy P false false
| squash {h o} (x : XTy P h o) : XTy P true true
| subtype {h o} (x : P) (p : toType x → Prop) : XTy P (isHash x && h) (isOrd x && o)
| hashmap {hv ov} (k : XTy P true ok) (v : XTy P hv ov) : XTy P false false
| dhashmap (k : {k : P // isHash k = true}) (v : toType k.val → XTy P false false) : XTy P false false
| hashset (k : XTy P true ok) : XTy P false false
| treemap {hv ov} (k : XTy P hk true) (v : XTy P hv ov) : XTy P false false
| dtreemap (k : {k : P // isOrd k = true}) (v : toType k.val → XTy P false false) : XTy P false false
| treeset (k : XTy P hk true) : XTy P false false
| f {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P false false
| sigma (x : P) (y : toType x → XTy P false false) : XTy P false false
| pi (x : P) (y : toType x → XTy P false false) : XTy P false false
| w (d : P) (a : toType d → XTy P false false) (b : toType d → XTy P false false) : XTy P false false
| thunk {h o} (x : XTy P h o) : XTy P false false

structure Decoded (h o : Bool) where
  type : Type
  hInst : h = true → Hashable type
  oInst : o = true → Ord type
  bInst : h = true ∨ o = true → BEq type

-- Helper lemmas
lemma or_to_bool_or {a b : Bool} (h : a = true ∨ b = true) : (a || b) = true := by
  cases h <;> simp_all

-- Helpers for decode
def Decoded.noInstances (type : Type) : Decoded false false := {
  type := type
  hInst := fun h => nomatch h
  oInst := fun o => nomatch o
  bInst := fun b => nomatch b
}

def Decoded.liftWrapper {h o} (d : Decoded h o) (F : Type → Type)
    (hF : ∀ {α}, Hashable α → Hashable (F α))
    (oF : ∀ {α}, Ord α → Ord (F α))
    (bF : ∀ {α}, BEq α → BEq (F α)) : Decoded h o := {
  type := F d.type
  hInst := fun eq => hF (d.hInst eq)
  oInst := fun eq => oF (d.oInst eq)
  bInst := fun eq =>
    have : h = true ∨ o = true := by cases eq <;> simp_all
    bF (d.bInst this)
}

def decode {P} [ToType P] {h o} (t : XTy P h o) : Decoded h o :=
  match t with
  | .lift x => {
      type := ToType.toType x
      hInst := fun heq => ToType.instHash x heq
      oInst := fun oeq => ToType.instOrd x oeq
      bInst := fun beq => ToType.instBEq x (by cases beq <;> simp_all)
    }
  | .prod (h1:=h1) (o1:=o1) (h2:=h2) (o2:=o2) x y =>
      let d1 := decode x
      let d2 := decode y
      {
        type := d1.type × d2.type
        hInst := fun heq => by
          have h_and : h1 = true ∧ h2 = true := by simp_all [Bool.and_eq_true]
          letI : Hashable d1.type := d1.hInst h_and.1
          letI : Hashable d2.type := d2.hInst h_and.2
          exact inferInstance
        oInst := fun oeq => by
          have o_and : o1 = true ∧ o2 = true := by simp_all [Bool.and_eq_true]
          letI : Ord d1.type := d1.oInst o_and.1
          letI : Ord d2.type := d2.oInst o_and.2
          exact inferInstance
        bInst := fun beq => by
          have c1 : h1 = true ∨ o1 = true := by
            cases beq <;> simp_all [Bool.and_eq_true]
          have c2 : h2 = true ∨ o2 = true := by
            cases beq <;> simp_all [Bool.and_eq_true]
          letI : BEq d1.type := d1.bInst c1
          letI : BEq d2.type := d2.bInst c2
          exact inferInstance
      }
  | .sum (h1:=h1) (o1:=o1) (h2:=h2) (o2:=o2) x y =>
      let d1 := decode x
      let d2 := decode y
      {
        type := d1.type ⊕ d2.type
        hInst := fun heq => by
          have h_and : h1 = true ∧ h2 = true := by simp_all [Bool.and_eq_true]
          letI : Hashable d1.type := d1.hInst h_and.1
          letI : Hashable d2.type := d2.hInst h_and.2
          exact inferInstance
        oInst := fun oeq => by
          have o_and : o1 = true ∧ o2 = true := by simp_all [Bool.and_eq_true]
          letI : Ord d1.type := d1.oInst o_and.1
          letI : Ord d2.type := d2.oInst o_and.2
          exact inferInstance
        bInst := fun beq => by
          have c1 : h1 = true ∨ o1 = true := by
            cases beq <;> simp_all [Bool.and_eq_true]
          have c2 : h2 = true ∨ o2 = true := by
            cases beq <;> simp_all [Bool.and_eq_true]
          letI : BEq d1.type := d1.bInst c1
          letI : BEq d2.type := d2.bInst c2
          exact inferInstance
      }
  | .vec x n => (decode x).liftWrapper (fun T => Vector T n) (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance)
  | .array x => (decode x).liftWrapper Array (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance)
  | .list x => (decode x).liftWrapper List (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance)
  | .option x => (decode x).liftWrapper Option (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance) (fun {_} i => by letI := i; exact inferInstance)
  | .multiset x => Decoded.noInstances (Multiset (decode x).type)
  | .finset x => Decoded.noInstances (Finset (decode x).type)
  | .quot x r => Decoded.noInstances (Quot r)
  | .quotient x s => Decoded.noInstances (Quotient s)
  | .squash x =>
      let d := decode x
      {
        type := Squash d.type
        hInst := fun _ => inferInstance
        oInst := fun _ => inferInstance
        bInst := fun _ => inferInstance
      }
  | .subtype (h:=h') (o:=o') x p =>
      let d := ToType.toType x
      {
        type := { a : d // p a }
        hInst := fun heq => by
          have h_and : ToType.isHash x = true ∧ h' = true := by simp_all [Bool.and_eq_true]
          letI : Hashable d := ToType.instHash x h_and.1
          exact inferInstance
        oInst := fun oeq => by
          have o_and : ToType.isOrd x = true ∧ o' = true := by simp_all [Bool.and_eq_true]
          letI : Ord d := ToType.instOrd x o_and.1
          exact inferInstance
        bInst := fun beq => by
          have : ToType.isHash x = true ∨ ToType.isOrd x = true := by
            cases beq <;> simp_all [Bool.and_eq_true]
          letI : BEq d := ToType.instBEq x this
          exact inferInstance
      }
  | .hashmap k v =>
      let kd := decode k
      let vd := decode v
      letI : Hashable kd.type := kd.hInst rfl
      letI : BEq kd.type := kd.bInst (Or.inl rfl)
      Decoded.noInstances (Std.HashMap kd.type vd.type)
  | .dhashmap k v =>
      letI : Hashable (ToType.toType k.val) := ToType.instHash k.val k.property
      letI : BEq (ToType.toType k.val) := ToType.instBEq k.val (Or.inl k.property)
      Decoded.noInstances (Std.DHashMap (ToType.toType k.val) (fun a => (decode (v a)).type))
  | .hashset k =>
      let kd := decode k
      letI : Hashable kd.type := kd.hInst rfl
      letI : BEq kd.type := kd.bInst (Or.inl rfl)
      Decoded.noInstances (Std.HashSet kd.type)
  | .treemap k v =>
      let kd := decode k
      let vd := decode v
      letI : Ord kd.type := kd.oInst rfl
      Decoded.noInstances (Std.TreeMap kd.type vd.type)
  | .dtreemap k v =>
      letI : Ord (ToType.toType k.val) := ToType.instOrd k.val k.property
      Decoded.noInstances (Std.DTreeMap (ToType.toType k.val) (fun a => (decode (v a)).type))
  | .treeset k =>
      let kd := decode k
      letI : Ord kd.type := kd.oInst rfl
      Decoded.noInstances (Std.TreeSet kd.type)
  | .f x y => Decoded.noInstances ((decode x).type → (decode y).type)
  | .sigma x y => Decoded.noInstances ((a : ToType.toType x) × (decode (y a)).type)
  | .pi x y => Decoded.noInstances ((a : ToType.toType x) → (decode (y a)).type)
  | .w d a b =>
      Decoded.noInstances (WType (fun (x: ((x : ToType.toType d) × (decode (a x)).type)) => (decode (b x.1)).type))
  | .thunk x => Decoded.noInstances (Thunk (decode x).type)

def XTy.toType {P} [ToType P] {h o} (t : XTy P h o) : Type := (decode t).type

instance instHashXTy {P} [ToType P] {h o} (t : XTy P h o) (eq : h = true) : Hashable (XTy.toType t) :=
  (decode t).hInst eq

instance instOrdXTy {P} [ToType P] {h o} (t : XTy P h o) (eq : o = true) : Ord (XTy.toType t) :=
  (decode t).oInst eq

instance instBEqXTy {P} [ToType P] {h o} (t : XTy P h o) (cond : h = true ∨ o = true) : BEq (XTy.toType t) :=
  (decode t).bInst cond

-- Universe Hierarchy Construction

@[reducible] def NTyStruct : (n : Nat) → (Σ (T : Bool → Bool → Type), ToType (Σ h o, T h o))
| 0 =>
  let T := fun h o => if h && o then STy else Empty
  let inst : ToType (Σ h o, T h o) := {
    toType := fun ⟨h, o, x⟩ => match h, o with
      | true, true => ToType.toType (cast (by simp [T]) x : STy)
      | _, _ => Empty
    isHash := fun x => x.1
    isOrd := fun x => x.2.1
    instHash := fun ⟨h, o, x⟩ eq => by
      simp at eq
      subst eq
      match o with
      | true =>
        show Hashable (ToType.toType (cast (by rfl) x : STy))
        exact ToType.instHash (cast (by rfl) x : STy) rfl
      | false =>
        show Hashable Empty
        exact inferInstance
    instBEq := fun ⟨h, o, x⟩ cond => by
      match h, o with
      | true, true =>
        show BEq (ToType.toType (cast (by rfl) x : STy))
        exact ToType.instBEq (cast (by rfl) x : STy) (Or.inl rfl)
      | true, false =>
        show BEq Empty
        exact inferInstance
      | false, true =>
        show BEq Empty
        exact inferInstance
      | false, false =>
        show BEq Empty
        exact inferInstance
    instOrd := fun ⟨h, o, x⟩ eq => by
      simp at eq
      subst eq
      match h with
      | true =>
        show Ord (ToType.toType (cast (by rfl) x : STy))
        exact ToType.instOrd (cast (by rfl) x : STy) rfl
      | false =>
        show Ord Empty
        exact inferInstance
  }
  ⟨T, inst⟩
| n + 1 =>
  let ⟨prevT, prevInst⟩ := NTyStruct n
  let P := Σ h o, prevT h o
  let T := fun h o => @XTy P prevInst h o
  let inst : ToType (Σ h o, T h o) := {
    toType := fun ⟨h, o, x⟩ => @XTy.toType P prevInst h o x
    isHash := fun x => x.1
    isOrd := fun x => x.2.1
    instHash := fun ⟨h, o, x⟩ eq => @instHashXTy P prevInst h o x eq
    instBEq := fun ⟨h, o, x⟩ cond => by
      have cond' : h = true ∨ o = true := by
        cases h <;> cases o <;> simp_all
      exact @instBEqXTy P prevInst h o x cond'
    instOrd := fun ⟨h, o, x⟩ eq => @instOrdXTy P prevInst h o x eq
  }
  ⟨T, inst⟩

@[reducible] def NTy (n : Nat) (h o : Bool) : Type := (NTyStruct n).1 h o
instance instNTy (n : Nat) : ToType (Σ h o, NTy n h o) := (NTyStruct n).2

lemma instNTy_isHash (n : Nat) (x : Σ h o, NTy n h o) : ToType.isHash (self := instNTy n) x = x.1 := by
  dsimp [instNTy, NTyStruct]
  induction n <;> rfl

lemma instNTy_isOrd (n : Nat) (x : Σ h o, NTy n h o) : ToType.isOrd (self := instNTy n) x = x.2.1 := by
  dsimp [instNTy, NTyStruct]
  induction n <;> rfl

-- Definition of CTy (Code Type) and Ty
def CTy (h o : Bool) := (n : Nat) × NTy n h o

def Ty := Σ (h o : Bool), CTy h o

instance : ToType Ty where
  toType t :=
    let n := t.2.2.1
    let x := t.2.2.2
    letI := instNTy n
    ToType.toType (⟨t.1, t.2.1, x⟩ : Σ h o, NTy n h o)

  isHash t := t.1
  isOrd t := t.2.1

  instHash t h := by
    let n := t.2.2.1
    let x := t.2.2.2
    letI := instNTy n
    let val : Σ h o, NTy n h o := ⟨t.1, t.2.1, x⟩
    have eq : ToType.isHash val = true := by
      rw [instNTy_isHash]
      exact h
    exact ToType.instHash val eq

  instBEq t cond := by
    let n := t.2.2.1
    let x := t.2.2.2
    letI := instNTy n
    let val : Σ h o, NTy n h o := ⟨t.1, t.2.1, x⟩
    have cond' : ToType.isHash val = true ∨ ToType.isOrd val = true := by
      cases cond with
      | inl h => exact Or.inl (by rw [instNTy_isHash]; exact h)
      | inr o => exact Or.inr (by rw [instNTy_isOrd]; exact o)
    exact ToType.instBEq val cond'

  instOrd t o := by
    let n := t.2.2.1
    let x := t.2.2.2
    letI := instNTy n
    let val : Σ h o, NTy n h o := ⟨t.1, t.2.1, x⟩
    have eq : ToType.isOrd val = true := by
      rw [instNTy_isOrd]
      exact o
    exact ToType.instOrd val eq

-- Lift/Coercions

instance {P : Type} [ToType P] : Coe P (Σ h o, XTy P h o) where
  coe x := ⟨isHash x, isOrd x, XTy.lift x⟩

def lift_nty (m : Nat) {n : Nat} {h o} (x : NTy n h o) : NTy (n + m) h o :=
  match m with
  | 0 => x
  | m + 1 =>
    let x' := lift_nty m x
    letI := instNTy (n + m)
    let y : Σ h o, NTy (n+m) h o := ⟨h, o, x'⟩
    have h_eq : ToType.isHash y = h := instNTy_isHash (n + m) y
    have o_eq : ToType.isOrd y = o := instNTy_isOrd (n + m) y
    let res : XTy (Σ h o, NTy (n + m) h o) (ToType.isHash y) (ToType.isOrd y) := XTy.lift y
    cast (by dsimp [NTy, instNTy, NTyStruct]; rw [h_eq, o_eq]) res

instance (n m : Nat) {h o} : Coe (NTy n h o) (NTy (n + m) h o) where
  coe := lift_nty m

instance {n h o} : CoeOut (NTy n h o) (CTy h o) where
  coe t := ⟨n, t⟩

instance {h o} : CoeOut (CTy h o) Ty where
  coe t := ⟨h, o, t⟩
