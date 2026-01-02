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

/-- Type class for codes that can be decoded into a Type -/
class ToType (α : Type) where
  toType : α → Type
  isHash : α → Bool
  isOrd : α → Bool
  instHash : ∀ x, isHash x → Hashable (toType x)
  instBEq : ∀ x, (isHash x || isOrd x) → BEq (toType x)
  instOrd : ∀ x, isOrd x → Ord (toType x)

export ToType (toType isHash isOrd instHash instBEq instOrd)

-- Instances for primitives
instance : Hashable Empty where hash _ := 0
instance : Ord Empty where compare _ _ := .eq
instance : BEq Empty where beq _ _ := true

instance : Hashable (PLift p) where hash _ := 0
instance : Ord (PLift p) where compare _ _ := .eq
instance : BEq (PLift p) where beq _ _ := true

instance : Hashable NONote where hash _ := 0
instance : Ord NONote where compare x y := if x < y then .lt else if x = y then .eq else .gt

instance : Hashable Rat where hash x := mixHash (hash x.num) (hash x.den)

instance : ToType Empty where
  toType _ := Empty
  isHash _ := false
  isOrd _ := false
  instHash _ _ := inferInstance
  instBEq _ _ := inferInstance
  instOrd _ _ := inferInstance

instance [Hashable α] [Hashable β] : Hashable (α ⊕ β) where
  hash
  | .inl a => mixHash 0 (hash a)
  | .inr b => mixHash 1 (hash b)

instance [Ord α] [Ord β] : Ord (α × β) where
  compare x y := match compare x.1 y.1 with
    | .eq => compare x.2 y.2
    | o => o

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

abbrev Squash (α : Type u) := Quot (fun (_ _ : α) => True)

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

  instHash s _ := by cases s <;> try exact inferInstance; exact { hash := fun _ => 0 }
  instBEq s _ := by cases s <;> simp [toType] <;> try exact inferInstance; exact { beq := fun _ _ => true }
  instOrd s _ := by cases s <;> simp [toType] <;> try exact inferInstance; exact { compare := fun _ _ => .eq }

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
| hashset (k : XTy P true ok) : XTy P false false
| treemap {hv ov} (k : XTy P hk true) (v : XTy P hv ov) : XTy P false false
| treeset (k : XTy P hk true) : XTy P false false
| f {h1 o1 h2 o2} (x : XTy P h1 o1) (y : XTy P h2 o2) : XTy P false false
| sigma (x : P) (y : toType x → XTy P false false) : XTy P false false
| pi (x : P) (y : toType x → XTy P false false) : XTy P false false
| w (d : P) (a : toType d → XTy P false false) (b : toType d → XTy P false false) : XTy P false false
| thunk {h o} (x : XTy P h o) : XTy P false false

instance : Hashable (Squash α) where hash _ := 0
instance : BEq (Squash α) where beq _ _ := true
instance : Ord (Squash α) where compare _ _ := .eq

structure Decoded (h o : Bool) where
  type : Type
  hInst : if h then Hashable type else Unit
  oInst : if o then Ord type else Unit
  bInst : if h || o then BEq type else Unit

-- Helper lemmas
lemma cond_implies_left {h1 h2 o1 o2 : Bool} (cond : (h1 && h2) || (o1 && o2)) : h1 || o1 := by
  cases h1 <;> cases h2 <;> cases o1 <;> cases o2 <;> simp_all

lemma cond_implies_right {h1 h2 o1 o2 : Bool} (cond : (h1 && h2) || (o1 && o2)) : h2 || o2 := by
  cases h1 <;> cases h2 <;> cases o1 <;> cases o2 <;> simp_all

lemma cond_implies_subtype {h o : Bool} {isHashX isOrdX : Bool} (cond : isHashX && h || isOrdX && o) : isHashX || isOrdX := by
  cases isHashX <;> cases isOrdX <;> cases h <;> cases o <;> simp_all

def decode {P} [ToType P] {h o} (t : XTy P h o) : Decoded h o :=
  match t with
  | .lift x => {
      type := ToType.toType x
      hInst := if heq : ToType.isHash x then ToType.instHash x heq else ()
      oInst := if oeq : ToType.isOrd x then ToType.instOrd x oeq else ()
      bInst := if beq : ToType.isHash x || ToType.isOrd x then ToType.instBEq x beq else ()
    }
  | .prod (h1:=h1) (o1:=o1) (h2:=h2) (o2:=o2) x y =>
      let d1 := decode x
      let d2 := decode y
      {
        type := d1.type × d2.type
        hInst := if heq : h1 && h2 then
            have h_and : h1 = true ∧ h2 = true := by simp at heq; exact ⟨heq.1, heq.2⟩
            letI : Hashable d1.type := cast (by simp [h_and.1]) d1.hInst
            letI : Hashable d2.type := cast (by simp [h_and.2]) d2.hInst
            instHashableProd
          else ()
        oInst := if oeq : o1 && o2 then
            have o_and : o1 = true ∧ o2 = true := by simp at oeq; exact ⟨oeq.1, oeq.2⟩
            letI : Ord d1.type := cast (by simp [o_and.1]) d1.oInst
            letI : Ord d2.type := cast (by simp [o_and.2]) d2.oInst
            inferInstance
          else ()
        bInst := if beq : (h1 && h2) || (o1 && o2) then
            have c1 : h1 || o1 := cond_implies_left beq
            have c2 : h2 || o2 := cond_implies_right beq
            letI : BEq d1.type := cast (by simp [c1]) d1.bInst
            letI : BEq d2.type := cast (by simp [c2]) d2.bInst
            inferInstance
          else ()
      }
  | .sum (h1:=h1) (o1:=o1) (h2:=h2) (o2:=o2) x y =>
      let d1 := decode x
      let d2 := decode y
      {
        type := d1.type ⊕ d2.type
        hInst := if heq : h1 && h2 then
            have h_and : h1 = true ∧ h2 = true := by simp at heq; exact ⟨heq.1, heq.2⟩
            letI : Hashable d1.type := cast (by simp [h_and.1]) d1.hInst
            letI : Hashable d2.type := cast (by simp [h_and.2]) d2.hInst
            inferInstance
          else ()
        oInst := if oeq : o1 && o2 then
            have o_and : o1 = true ∧ o2 = true := by simp at oeq; exact ⟨oeq.1, oeq.2⟩
            letI : Ord d1.type := cast (by simp [o_and.1]) d1.oInst
            letI : Ord d2.type := cast (by simp [o_and.2]) d2.oInst
            inferInstance
          else ()
        bInst := if beq : (h1 && h2) || (o1 && o2) then
            have c1 : h1 || o1 := cond_implies_left beq
            have c2 : h2 || o2 := cond_implies_right beq
            letI : BEq d1.type := cast (by simp [c1]) d1.bInst
            letI : BEq d2.type := cast (by simp [c2]) d2.bInst
            inferInstance
          else ()
      }
  | .vec x n =>
      let d := decode x
      {
        type := Vector d.type n
        hInst := if heq : h then
            letI : Hashable d.type := cast (by simp [heq]) d.hInst
            inferInstance
          else ()
        oInst := if oeq : o then
            letI : Ord d.type := cast (by simp [oeq]) d.oInst
            inferInstance
          else ()
        bInst := if beq : h || o then
            letI : BEq d.type := cast (by simp [beq]) d.bInst
            inferInstance
          else ()
      }
  | .array x =>
      let d := decode x
      {
        type := Array d.type
        hInst := if heq : h then
            letI : Hashable d.type := cast (by simp [heq]) d.hInst
            instHashableArray
          else ()
        oInst := if oeq : o then
            letI : Ord d.type := cast (by simp [oeq]) d.oInst
            inferInstance
          else ()
        bInst := if beq : h || o then
            letI : BEq d.type := cast (by simp [beq]) d.bInst
            inferInstance
          else ()
      }
  | .list x =>
      let d := decode x
      {
        type := List d.type
        hInst := if heq : h then
            letI : Hashable d.type := cast (by simp [heq]) d.hInst
            instHashableList
          else ()
        oInst := if oeq : o then
            letI : Ord d.type := cast (by simp [oeq]) d.oInst
            inferInstance
          else ()
        bInst := if beq : h || o then
            letI : BEq d.type := cast (by simp [beq]) d.bInst
            inferInstance
          else ()
      }
  | .option x =>
      let d := decode x
      {
        type := Option d.type
        hInst := if heq : h then
            letI : Hashable d.type := cast (by simp [heq]) d.hInst
            instHashableOption
          else ()
        oInst := if oeq : o then
            letI : Ord d.type := cast (by simp [oeq]) d.oInst
            inferInstance
          else ()
        bInst := if beq : h || o then
            letI : BEq d.type := cast (by simp [beq]) d.bInst
            inferInstance
          else ()
      }
  | .multiset x =>
      let d := decode x
      {
        type := Multiset d.type
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .finset x =>
      let d := decode x
      {
        type := Finset d.type
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .quot x r =>
      {
        type := Quot r
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .quotient x s =>
      {
        type := Quotient s
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .squash x =>
      let d := decode x
      {
        type := Squash d.type
        hInst := inferInstance
        oInst := inferInstance
        bInst := inferInstance
      }
  | .subtype (h:=h') (o:=o') x p =>
      let d := ToType.toType x
      {
        type := { a : d // p a }
        hInst := if heq : ToType.isHash x && h' then
            have : ToType.isHash x = true := by simp at heq; exact heq.1
            letI : Hashable d := ToType.instHash x this
            inferInstance
          else ()
        oInst := if oeq : ToType.isOrd x && o' then
            have : ToType.isOrd x = true := by simp at oeq; exact oeq.1
            letI : Ord d := ToType.instOrd x this
            inferInstance
          else ()
        bInst := if beq : (ToType.isHash x && h') || (ToType.isOrd x && o') then
            have : (ToType.isHash x || ToType.isOrd x) = true := cond_implies_subtype beq
            letI : BEq d := ToType.instBEq x this
            inferInstance
          else ()
      }
  | .hashmap k v =>
      let kd := decode k
      let vd := decode v
      letI : Hashable kd.type := cast (by simp) kd.hInst
      letI : BEq kd.type := cast (by simp) kd.bInst
      {
        type := @Std.HashMap kd.type vd.type inferInstance inferInstance
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .hashset k =>
      let kd := decode k
      letI : Hashable kd.type := cast (by simp) kd.hInst
      letI : BEq kd.type := cast (by simp) kd.bInst
      {
        type := @Std.HashSet kd.type inferInstance inferInstance
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .treemap k v =>
      let kd := decode k
      let vd := decode v
      letI : Ord kd.type := cast (by simp) kd.oInst
      {
        type := @Std.TreeMap kd.type vd.type (compare)
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .treeset k =>
      let kd := decode k
      letI : Ord kd.type := cast (by simp) kd.oInst
      {
        type := @Std.TreeSet kd.type (compare)
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .f x y =>
      let dx := decode x
      let dy := decode y
      {
        type := dx.type → dy.type
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .sigma x y =>
      {
        type := (a : ToType.toType x) × (decode (y a)).type
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .pi x y =>
      {
        type := (a : ToType.toType x) → (decode (y a)).type
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .w d a b =>
      {
        type := WType (fun (x: ((x : ToType.toType d) × (decode (a x)).type)) => (decode (b x.1)).type)
        hInst := ()
        oInst := ()
        bInst := ()
      }
  | .thunk x =>
      let d := decode x
      {
        type := Thunk d.type
        hInst := ()
        oInst := ()
        bInst := ()
      }

def XTy.toType {P} [ToType P] {h o} (t : XTy P h o) : Type := (decode t).type

instance {P} [ToType P] {h o} (t : XTy P h o) (eq : h = true) : Hashable (XTy.toType t) :=
  cast (by simp [eq, XTy.toType]) (decode t).hInst

instance {P} [ToType P] {h o} (t : XTy P h o) (eq : o = true) : Ord (XTy.toType t) :=
  cast (by simp [eq, XTy.toType]) (decode t).oInst

instance {P} [ToType P] {h o} (t : XTy P h o) (cond : h || o) : BEq (XTy.toType t) :=
  cast (by simp [cond, XTy.toType]) (decode t).bInst

-- Universe Hierarchy Construction

@[reducible] def NTyStruct : (n : Nat) → (Σ (T : Bool → Bool → Type), ToType (Σ h o, T h o))
| 0 =>
  let T := fun h o => if h && o then STy else Empty
  let inst : ToType (Σ h o, T h o) := {
    toType := fun ⟨h, o, x⟩ => if h_eq : h then if o_eq : o then ToType.toType (cast (by simp [h_eq, o_eq] at x; exact x) : STy) else Empty else Empty
    isHash := fun x => x.1
    isOrd := fun x => x.2.1
    instHash := fun ⟨h, o, x⟩ eq => by
      simp at eq
      simp [eq] at x
      have : h = true := eq
      split at x
      next heq =>
         split at x
         next oeq =>
            have : o = true := oeq
            let s : STy := cast (by simp [heq, oeq]) x
            exact ToType.instHash s rfl
         next => contradiction
      next => contradiction
    instBEq := fun ⟨h, o, x⟩ cond => by
      simp at cond
      dsimp
      split
      next heq =>
        split
        next oeq =>
           let s : STy := cast (by simp [heq, oeq]) x
           exact ToType.instBEq s (by simp)
        next => exact (inferInstance : BEq Empty)
      next => exact (inferInstance : BEq Empty)
    instOrd := fun ⟨h, o, x⟩ eq => by
      simp at eq
      simp [eq] at x
      have : o = true := eq
      split at x
      next heq =>
         split at x
         next oeq =>
            let s : STy := cast (by simp [heq, oeq]) x
            exact ToType.instOrd s rfl
         next => contradiction
      next => contradiction
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
    instHash := fun ⟨h, o, x⟩ eq => by
      simp at eq
      apply (inferInstance : Hashable (XTy.toType x.2.2))
    instBEq := fun ⟨h, o, x⟩ cond => by
      apply (inferInstance : BEq (XTy.toType x.2.2))
    instOrd := fun ⟨h, o, x⟩ eq => by
      simp at eq
      apply (inferInstance : Ord (XTy.toType x.2.2))
  }
  ⟨T, inst⟩

@[reducible] def NTy (n : Nat) (h o : Bool) : Type := (NTyStruct n).1 h o
instance instNTy (n : Nat) : ToType (Σ h o, NTy n h o) := (NTyStruct n).2

lemma instNTy_isHash (n : Nat) (x : Σ h o, NTy n h o) : ToType.isHash (self := instNTy n) x = x.1 := by
  dsimp [instNTy, NTyStruct]
  induction n <;> try rfl
  rfl

lemma instNTy_isOrd (n : Nat) (x : Σ h o, NTy n h o) : ToType.isOrd (self := instNTy n) x = x.2.1 := by
  dsimp [instNTy, NTyStruct]
  induction n <;> try rfl
  rfl

-- Definition of CTy (Code Type) and Ty
def CTy (h o : Bool) := (n : Nat) × NTy n h o

instance {h o} : Coe (NTy n h o) (CTy h o) := ⟨fun t => ⟨n, t⟩⟩

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
    change (ToType.isHash val || ToType.isOrd val) = true at cond
    exact ToType.instBEq val cond

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
    have h_eq : ToType.isHash y = h := by rw [instNTy_isHash]
    have o_eq : ToType.isOrd y = o := by rw [instNTy_isOrd]
    let res : XTy (Σ h o, NTy (n + m) h o) (ToType.isHash y) (ToType.isOrd y) := XTy.lift y
    cast (by dsimp [NTy, instNTy, NTyStruct]; rw [h_eq, o_eq]; rfl) res

instance (n m : Nat) {h o} : Coe (NTy n h o) (NTy (n + m) h o) where
  coe := lift_nty m

instance {n h o} : CoeOut (NTy n h o) (CTy h o) where
  coe t := ⟨n, t⟩

instance {h o} : CoeOut (CTy h o) Ty where
  coe t := ⟨h, o, t⟩
