module

public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Topology.Defs.Filter
public import ComputableReal.Sometone
public import ComputableReal.OrdClosure
import ComputableReal.Set

import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Topology.Order.IntermediateValue

namespace NonemptyInterval
variable {α β γ δ: Type*}

/-
section le
variable [LE α]
--public instance (priority := 99) instMembershipOfLE: Membership α (NonemptyInterval α) :=
--  ⟨fun s a => s.fst ≤ a ∧ a ≤ s.snd⟩
end le
-/

section refl
--variable [LE α] [IsRefl α (· ≤ ·)]
variable [Preorder α]

public lemma fst_mem (x: NonemptyInterval α): x.fst ∈ x := by
  exact ⟨IsRefl.refl _, NonemptyInterval.fst_le_snd x⟩

public lemma snd_mem (x: NonemptyInterval α): x.snd ∈ x := by
  exact ⟨NonemptyInterval.fst_le_snd x, IsRefl.refl _⟩
end refl

section base
variable [Preorder α] [Preorder β] [Preorder γ]
public def map₂' {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys) (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs): NonemptyInterval γ :=
  ⟨⟨f xs.fst ys.fst, f xs.snd ys.snd⟩, by
    have h1 := hfl ys.fst ys.fst_mem xs.fst_mem xs.snd_mem xs.fst_le_snd
    have h2 := hfr xs.snd xs.snd_mem ys.fst_mem ys.snd_mem ys.fst_le_snd
    exact le_trans h1 h2⟩

public lemma toProd_map₂ (f: α → β → γ) (hfl: ∀ y, Monotone (f · y)) (hfr: ∀ x, Monotone (f x)) (x : NonemptyInterval α) (y: NonemptyInterval β):
  (map₂ f hfl hfr x y).toProd =
    ⟨f x.fst y.fst, f x.snd y.snd⟩ :=
  rfl
end base

section lattice
variable [LE α] [LE β] [Lattice γ]
@[inline]
public def map₂mm (f: α → β → γ) (x : NonemptyInterval α) (y: NonemptyInterval β): NonemptyInterval γ :=
  let ⟨⟨xl,xu⟩,_⟩ := x
  let ⟨⟨yl,yu⟩,_⟩ := y
  ⟨⟨(f xl yl ⊓ f xu yl) ⊓ (f xl yu ⊓ f xu yu),
    (f xl yl ⊔ f xu yl) ⊔ (f xl yu ⊔ f xu yu)⟩,
    by
      repeat apply inf_le_of_left_le
      repeat apply le_sup_of_le_left
      rfl⟩

public lemma toProd_map₂mm (f: α → β → γ) (x : NonemptyInterval α) (y: NonemptyInterval β):
  (map₂mm f x y).toProd =
    ⟨(f x.fst y.fst ⊓ f x.snd y.fst) ⊓ (f x.fst y.snd ⊓ f x.snd y.snd),
      (f x.fst y.fst ⊔ f x.snd y.fst) ⊔ (f x.fst y.snd ⊔ f x.snd y.snd)⟩ := by
  unfold map₂mm
  simp

end lattice

section pre_pre_lattice
variable [Preorder α] [Preorder β] [Lattice γ] [Lattice δ]
public def map_injective (f : α ↪o β) : Function.Injective (NonemptyInterval.map f.toOrderHom) := by
  apply Function.Injective.of_comp (f := NonemptyInterval.toProd)
  exact ((Function.Injective.prodMap f.injective f.injective).comp NonemptyInterval.toProd_injective)

public theorem image2_subset_map₂mm {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, SometoneOn (f · y) xs) (hfr: ∀ x ∈ xs, SometoneOn (f x) ys): Set.image2 f xs ys ⊆ map₂mm f xs ys := by
  rw [@Set.image2_subset_iff_right]
  intro y hy
  unfold map₂mm
  simp only [NonemptyInterval.coe_def]
  apply subset_trans (SometoneOn.image_uIcc_subset (hfl y hy))
  rw [Set.uIcc_subset_Icc_iff_mem]
  constructor
  · apply Set.mem_of_mem_of_subset (SometoneOn.mapsTo_uIcc (hfr xs.fst xs.fst_mem) hy)
    rw [Set.uIcc_subset_Icc_iff_mem]
    grind [inf_le_of_left_le, inf_le_of_right_le, le_sup_of_le_left, le_sup_of_le_right]
  · apply Set.mem_of_mem_of_subset (SometoneOn.mapsTo_uIcc (hfr xs.snd xs.snd_mem) hy)
    rw [Set.uIcc_subset_Icc_iff_mem]
    grind [inf_le_of_left_le, inf_le_of_right_le, le_sup_of_le_left, le_sup_of_le_right]

public theorem map₂_eq_map₂' {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y, Monotone (f · y)) (hfr: ∀ x, Monotone (f x)): map₂ f hfl hfr xs ys = map₂' (λ y _ ↦ (hfl y).monotoneOn xs) (λ x _ ↦ (hfr x).monotoneOn ys) := by
  unfold map₂ map₂'
  simp

public theorem map₂'_eq_map₂mm {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): map₂' hfl hfr = map₂mm f xs ys := by
  unfold map₂' map₂mm
  have hl := hfr _ xs.fst_mem ys.fst_mem ys.snd_mem ys.fst_le_snd
  have hr := hfr _ xs.snd_mem ys.fst_mem ys.snd_mem ys.fst_le_snd
  have hd := hfl _ ys.fst_mem xs.fst_mem xs.snd_mem xs.fst_le_snd
  have hu := hfl _ ys.snd_mem xs.fst_mem xs.snd_mem xs.fst_le_snd
  simp only [mk.injEq, Prod.mk.injEq]
  clear hfl hfr
  grind [inf_eq_left, inf_eq_right, sup_eq_left, sup_eq_right]

public theorem image2_subset_map₂' {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): Set.image2 f xs ys ⊆ map₂' hfl hfr := by
  rw [map₂'_eq_map₂mm hfl hfr]
  exact image2_subset_map₂mm (λ x hx ↦ SometoneOn.of_MonotoneOn (hfl x hx)) (λ x hx ↦ SometoneOn.of_MonotoneOn (hfr x hx))

public theorem map₂mm_map_left {xs : NonemptyInterval α} {ys: NonemptyInterval β} (f: γ → β → δ) (g: α →o γ): (xs.map g).map₂mm f ys = xs.map₂mm (λ x ↦ f (g x)) ys := by
  unfold map₂mm map
  simp

public theorem map₂mm_map_right {xs : NonemptyInterval α} {ys: NonemptyInterval β} (f: α → γ → δ) (g: β →o γ): xs.map₂mm f (ys.map g) = xs.map₂mm (λ x y ↦ f x (g y)) ys := by
  unfold map₂mm map
  simp
end pre_pre_lattice

section linear
variable {δ: Type*} [Preorder α] [Preorder β] [LinearOrder γ] [Lattice δ]
public theorem map_map₂mm {xs : NonemptyInterval α} {ys: NonemptyInterval β} (f: α → β → γ) (g: γ →o δ): (xs.map₂mm f ys).map g = xs.map₂mm (λ x y ↦ g (f x y)) ys := by
  unfold map₂mm map
  simp

lemma split_min {a b: γ} {p: γ → Prop} (h: p a) (hb: p b): p (a ⊓ b) := by
  rw [min_def]
  split_ifs
  all_goals assumption

lemma split_max {a b: γ} {p: γ → Prop} (h: p a) (hb: p b): p (a ⊔ b) := by
  rw [max_def]
  split_ifs
  all_goals assumption

public theorem map₂mm_subset_ordClosure_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β}: (map₂mm f xs ys: Set γ) ⊆ Set.ordClosure (Set.image2 f xs ys) := by
  unfold map₂mm
  simp only [coe_def]
  apply Set.Icc_subset
  all_goals
    apply Set.mem_ordClosure_of_mem
    repeat'
      first
      | apply split_min
      | apply split_max
    all_goals
      simp only [Set.mem_image2, Set.mem_Icc]
      apply Exists.intro
      constructor
      pick_goal 2
      · apply Exists.intro
        constructor
        pick_goal 2
        · exact Eq.refl _
        · simp only [le_refl, fst_le_snd, and_self]
      · simp only [le_refl, fst_le_snd, and_self]

public theorem map₂mm_eq_ordClosure_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, SometoneOn (f · y) xs) (hfr: ∀ x ∈ xs, SometoneOn (f x) ys): (map₂mm f xs ys: Set γ) = Set.ordClosure (Set.image2 f xs ys) := by
  apply Set.eq_of_subset_of_subset
  · exact map₂mm_subset_ordClosure_image2
  · apply Set.ordClosure_subset_ordConnected
    · apply image2_subset_map₂mm hfl hfr
    · rw [coe_def]
      exact Set.ordConnected_Icc

public theorem map₂'_subset_ordClosure_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): (map₂' hfl hfr: Set γ) ⊆ Set.ordClosure (Set.image2 f xs ys) := by
  rw [map₂'_eq_map₂mm hfl hfr]
  exact map₂mm_subset_ordClosure_image2 (α := α) (β := β) (γ := γ)

public theorem map₂'_eq_ordClosure_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): (map₂' hfl hfr: Set γ) = Set.ordClosure (Set.image2 f xs ys) := by
  apply Set.eq_of_subset_of_subset
  · exact map₂'_subset_ordClosure_image2 hfl hfr
  · apply Set.ordClosure_subset_ordConnected
    · exact image2_subset_map₂' hfl hfr
    · rw [coe_def]
      exact Set.ordConnected_Icc
end linear

section add
variable [Preorder α]
/-
variable [Add α] [Preorder α] [AddLeftMono α] [AddRightMono α] in
instance (priority := low): Add (NonemptyInterval α) where
  add s t := by
    exact map₂ (· + ·) (λ x ↦ (add_left_mono: Monotone (· + x))) (λ x ↦(add_right_mono: Monotone (x + ·))) s t
-/

variable [Add α] [AddLeftMono α] [AddRightMono α] in
lemma add_eq_map₂ {s t: NonemptyInterval α}: s + t = s.map₂ (· + ·) (λ x ↦ (add_left_mono: Monotone (· + x))) (λ x ↦(add_right_mono: Monotone (x + ·))) t :=
  rfl

variable [AddZeroClass α] [AddLeftMono α] [AddRightMono α] in
instance (priority := low): AddZeroClass (NonemptyInterval α) where
  add_zero s := by
    apply toProd_injective
    simp [add_eq_map₂, toProd_map₂]
  zero_add s := by
    apply toProd_injective
    simp [add_eq_map₂, toProd_map₂]

variable [AddSemigroup α] [AddLeftMono α] [AddRightMono α] in
instance: AddSemigroup (NonemptyInterval α) where
  add_assoc s t u := by
    apply toProd_injective
    simp only [add_eq_map₂, toProd_map₂]
    simp [add_assoc]

variable [AddCommMagma α] [AddLeftMono α] [AddRightMono α] in
instance: AddCommMagma (NonemptyInterval α) where
  add_comm s t := by
    apply toProd_injective
    simp only [add_eq_map₂, toProd_map₂]
    simp [add_comm t.toProd.1, add_comm t.toProd.2]

variable [h: AddMonoid α]  [AddLeftMono α] [AddRightMono α] in
instance: AddMonoid (NonemptyInterval α) where
  nsmul n s := ⟨⟨h.nsmul n s.fst, h.nsmul n s.snd⟩, by
    simp only [nsmul_eq_smul]
    apply nsmul_le_nsmul_right
    exact s.fst_le_snd
  ⟩
  nsmul_zero s := by
    apply toProd_injective
    simp
  nsmul_succ n s := by
    apply toProd_injective
    ext <;> simp [succ_nsmul]

variable [AddCommSemigroup α] [AddLeftMono α] [AddRightMono α] in
instance: AddCommSemigroup (NonemptyInterval α) where

variable [AddCommMonoid α] [AddLeftMono α] [AddRightMono α] in
instance: AddCommMonoid (NonemptyInterval α) where
end add

section sub
variable [Preorder α]

variable [AddCommSemigroup α] [Sub α] [OrderedSub α] [AddLeftMono α] in
lemma toProd_sub {s t: NonemptyInterval α}: (s - t).toProd = ⟨s.fst - t.snd, s.snd - t.fst⟩ :=
  rfl

variable [AddCommSemigroup α] [SubNegMonoid α] [OrderedSub α] [AddLeftMono α] in
instance: Neg (NonemptyInterval α) where
  neg s := ⟨⟨-s.snd, -s.fst⟩, by
    simp only [neg_eq_zero_sub]
    apply tsub_le_tsub_left (α := α)
    exact s.fst_le_snd
  ⟩

variable [AddCommSemigroup α] [SubNegMonoid α] [OrderedSub α] [AddLeftMono α] in
lemma toProd_neg {s: NonemptyInterval α}: (-s).toProd = ⟨-s.snd, -s.fst⟩ :=
  rfl

variable [AddCommSemigroup α] [SubtractionMonoid α] [OrderedSub α] [AddLeftMono α] in
instance: InvolutiveNeg (NonemptyInterval α) where
  neg_neg s := by
    apply toProd_injective
    simp [toProd_neg]

variable [AddCommGroup α] [OrderedSub α] [AddLeftMono α] [AddRightMono α] in
instance: SubNegMonoid (NonemptyInterval α) where
  zsmul := zsmulRec (AddMonoid.nsmul)
  zsmul_zero' s := by
    apply toProd_injective
    unfold zsmulRec AddMonoid.nsmul instAddMonoid_computableReal
    simp
  zsmul_succ' n s := by
    apply toProd_injective
    unfold zsmulRec AddMonoid.nsmul instAddMonoid_computableReal
    ext <;> simp [succ_nsmul]
  zsmul_neg' n s := by
    apply toProd_injective
    unfold zsmulRec AddMonoid.nsmul instAddMonoid_computableReal
    ext <;> simp [succ_nsmul]
  sub_eq_add_neg s t := by
    apply toProd_injective
    simp only [add_eq_map₂, toProd_map₂, toProd_sub, toProd_neg]
    simp [sub_eq_add_neg]
end sub

section sub_partial
variable [PartialOrder α]

variable [AddCommGroup α] [OrderedSub α] [AddLeftMono α] [AddRightMono α] in
instance: SubtractionCommMonoid (NonemptyInterval α) where
  neg_add_rev s t := by
    apply toProd_injective
    simp [add_eq_map₂, toProd_map₂, toProd_neg]

  neg_eq_of_add s t := by
    intro h
    apply toProd_injective
    apply_fun toProd at h
    simp [add_eq_map₂, toProd_map₂, toProd_neg] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have he := Eq.trans h1 h2.symm
    have hs := s.fst_le_snd
    have ht := t.fst_le_snd
    have hl {a b c d: α} (h: c + d ≤ a + b) (h1: a ≤ c) (h2: b ≤ d): a = c := by
      rcases lt_or_eq_of_le h1 with hac | hac
      · grind
      · grind

    replace hs: s.toProd.1 = s.toProd.2 := hl (le_of_eq he.symm) hs ht
    replace ht: t.toProd.1 = t.toProd.2 := by grind
    ext
    · rw [neg_eq_iff_add_eq_zero]
      simp [← hs]
      exact h1
    · rw [neg_eq_iff_add_eq_zero]
      simp [← ht]
      exact h1

end sub_partial

section mul
variable [LE α] [LE β] [Lattice γ] [HMul α β γ] in
instance (priority := low): HMul (NonemptyInterval α) (NonemptyInterval β) (NonemptyInterval γ) where
  hMul := map₂mm (HMul.hMul · ·)

section lattice
variable [Lattice α]

variable [Mul α] in
instance (priority := low): Mul (NonemptyInterval α) where
  mul := map₂mm (· * ·)

variable [Mul α] in
lemma mul_eq_map₂mm {s t: NonemptyInterval α}: (s * t) = s.map₂mm (· * ·) t :=
  rfl
end lattice

--variable {s t: NonemptyInterval α}

--variable [CommMonoid α]

variable [Preorder α] [One α] in
instance: One (NonemptyInterval α) where
  one := ⟨⟨1, 1⟩, le_refl 1⟩

variable [MulOneClass α] [Lattice α] in
instance: MulOneClass (NonemptyInterval α) where
  one_mul s := by
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp [inf_of_le_left s.fst_le_snd, sup_of_le_right s.fst_le_snd]
  mul_one s := by
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp [inf_of_le_left s.fst_le_snd, sup_of_le_right s.fst_le_snd]

variable [MulZeroClass α] [Lattice α] in
instance: MulZeroClass (NonemptyInterval α) where
  zero_mul s := by
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp
  mul_zero s := by
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp

variable [NonUnitalSemiring α] [LinearOrder α] [AddRightMono α] [AddRightReflectLE α] [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α] in
instance: SemigroupWithZero (NonemptyInterval α) where
  mul_assoc s t u := by
    /-
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp
    let s1 := s.toProd.1
    have: s.toProd.1 = s1 := rfl
    simp only [this]
    let s2 := s.toProd.2
    have: s.toProd.2 = s2 := rfl
    simp only [this]
    let t1 := t.toProd.1
    have: t.toProd.1 = t1 := rfl
    simp only [this]
    let t2 := t.toProd.2
    have: t.toProd.2 = t2 := rfl
    simp only [this]
    let u1 := u.toProd.1
    have: u.toProd.1 = u1 := rfl
    simp only [this]
    let u2 := u.toProd.2
    have: u.toProd.2 = u2 := rfl
    simp only [this]
    simp only [← inf_assoc, ← sup_assoc]
    constructor
    · grind (splits := 100) (instances := 3000) (gen := 16)
    · sorry
    -/

    simp only [mul_eq_map₂mm]
    apply NonemptyInterval.coeHom.injective
    have hfr := λ {s: Set α} {t: Set α} x (_: x ∈ s) ↦ (mul_left_sometone x).sometoneOn t
    have hfl := λ {s: Set α} {t: Set α} y (_: y ∈ t) ↦ (mul_right_sometone y).sometoneOn s

    simp only [NonemptyInterval.coe_coeHom, ← NonemptyInterval.coe_def,
      NonemptyInterval.map₂mm_eq_ordClosure_image2 hfl hfr,
      Set.ordClosure_image2_ordClosure_left_eq hfr,
      Set.ordClosure_image2_ordClosure_right_eq hfl]
    congr 1
    apply Set.image2_assoc
    exact mul_assoc

variable [CommMagma α] [Lattice α] in
instance: CommMagma (NonemptyInterval α) where
  mul_comm s t := by
    apply toProd_injective
    simp only [mul_eq_map₂mm, toProd_map₂mm]
    simp only [mul_comm t.toProd.1, mul_comm t.toProd.2]
    grind

variable [Semiring α] [LinearOrder α] [AddRightMono α] [AddRightReflectLE α] [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α] [AddLeftMono α] in
instance: MonoidWithZero (NonemptyInterval α) where

variable [NonUnitalCommSemiring α] [LinearOrder α] [AddRightMono α] [AddRightReflectLE α] [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α] in
instance: CommSemigroup (NonemptyInterval α) where

variable [CommSemiring α] [LinearOrder α] [AddRightMono α] [AddRightReflectLE α] [ExistsAddOfLE α] [PosMulMono α] [MulPosMono α] in
instance: CommMonoidWithZero (NonemptyInterval α) where

variable [CommRing α] [LinearOrder α] [IsOrderedAddMonoid α] in
instance: HasDistribNeg (NonemptyInterval α) where
  neg_mul x y := by
    apply toProd_injective
    simp only [toProd_neg, mul_eq_map₂mm, toProd_map₂mm]
    ext
    · simp
      grind
    · simp
      grind

  mul_neg x y := by
    apply toProd_injective
    simp only [toProd_neg, mul_eq_map₂mm, toProd_map₂mm]
    ext
    · simp [min_neg_neg]
      grind
    · simp [max_neg_neg]
      grind

end mul

section algebra
variable [Preorder α] [Add α] [AddLeftMono α] [AddRightMono α]

public theorem add_eq_map₂'_add (xs: NonemptyInterval α) (ys: NonemptyInterval α):
  let hfr := λ y (_: y ∈ ys) ↦ (add_left_mono (a := y)).monotoneOn xs
  let hfl := λ x (_: x ∈ xs) ↦ (add_right_mono (a := x)).monotoneOn ys
  ((xs + ys): NonemptyInterval α) = map₂' hfr hfl := by
  unfold map₂'
  dsimp
  rw [← Add.add_eq_hAdd]
  unfold Add.add instAddNonemptyInterval
  simp only [Prod.add_def]

end algebra

section cclo
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
variable [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] [DenselyOrdered β]
variable [LinearOrder γ] [TopologicalSpace γ] [OrderClosedTopology γ]

public theorem Icc_subset_image {f: α → γ} {xs : NonemptyInterval α} (hf: ContinuousOn f xs) (hx₀: x₀ ∈ xs) (hx₁: x₁ ∈ xs): Set.Icc (f x₀) (f x₁) ⊆ f '' xs := by
  have hs: Set.uIcc x₀ x₁ ⊆ xs :=
    Set.OrdConnected.uIcc_subset Set.ordConnected_Icc hx₀ hx₁
  exact subset_trans Set.Icc_subset_uIcc
    (subset_trans (intermediate_value_uIcc (ContinuousOn.mono hf hs))
      (Set.image_mono hs))

public theorem Icc_subset_image2 (f: α → β → γ) {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, ContinuousOn (f · y) xs) (hfr: ∀ x ∈ xs, ContinuousOn (f x) ys) (hx₀: x₀ ∈ xs) (hx₁: x₁ ∈ xs) (hy₀: y₀ ∈ ys) (hy₁: y₁ ∈ ys): Set.Icc (f x₀ y₀) (f x₁ y₁) ⊆ Set.image2 f xs ys := by
  rw [Set.subset_def]
  intro z hz
  rw [Set.mem_Icc] at hz
  obtain ⟨hzl, hzu⟩ := hz
  rcases le_or_gt z (f x₀ y₁) with h | h
  · have hz: z ∈ Set.Icc (f x₀ y₀) (f x₀ y₁) :=
      Set.mem_Icc.mpr ⟨hzl, h⟩
    use x₀, hx₀
    have := Set.mem_of_mem_of_subset hz (Icc_subset_image (hfr x₀ hx₀) hy₀ hy₁)
    rw [Set.mem_image] at this
    exact this
  · have hz: z ∈ Set.Icc (f x₀ y₁) (f x₁ y₁) :=
      Set.mem_Icc.mpr ⟨le_of_lt h, hzu⟩
    have := Set.mem_of_mem_of_subset hz (Icc_subset_image (hfl y₁ hy₁) hx₀ hx₁)
    rw [Set.mem_image] at this
    obtain ⟨x, hx, hze⟩ := this
    use x, hx, y₁, hy₁

public theorem map₂mm_subset_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, ContinuousOn (f · y) xs) (hfr: ∀ x ∈ xs, ContinuousOn (f x) ys): (map₂mm f xs ys: Set γ) ⊆ Set.image2 f xs ys := by
  unfold map₂mm
  rw [Set.subset_def]
  intro z hz
  simp only [NonemptyInterval.coe_def] at hz
  simp at hz
  obtain ⟨hzl, hzu⟩ := hz
  replace hzl: ∃ x₀ ∈ xs, ∃ y₀ ∈ ys, f x₀ y₀ ≤ z := by
    rcases hzl with (_ | _) | (_ | _)
    all_goals
      use ?_, ?_, ?_, ?_
      all_goals simp [NonemptyInterval.mem_def, NonemptyInterval.fst_le_snd]
  replace hzu: ∃ x₁ ∈ xs, ∃ y₁ ∈ ys, z ≤ f x₁ y₁ := by
    rcases hzu with (_ | _) | (_ | _)
    all_goals
      use ?_, ?_, ?_, ?_
      all_goals simp [NonemptyInterval.mem_def, NonemptyInterval.fst_le_snd]
  obtain ⟨x₀, hx₀, y₀, hy₀, h₀⟩ := hzl
  obtain ⟨x₁, hx₁, y₁, hy₁, h₁⟩ := hzu
  have :=  Icc_subset_image2 f hfl hfr hx₀ hx₁ hy₀ hy₁
  apply this
  rw [Set.mem_Icc]
  exact ⟨h₀, h₁⟩

public theorem map₂mm_eq_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, ContinuousOn (f · y) xs) (hfal: ∀ y ∈ ys, SometoneOn (f · y) xs) (hfr: ∀ x ∈ xs, ContinuousOn (f x) ys) (hfar: ∀ x ∈ xs, SometoneOn (f x) ys): (map₂mm f xs ys: Set γ) = Set.image2 f xs ys := by
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · exact map₂mm_subset_image2 hfl hfr
  · exact image2_subset_map₂mm hfal hfar

public theorem map₂'_subset_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfcl: ∀ y ∈ ys, ContinuousOn (f · y) xs) (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfcr: ∀ x ∈ xs, ContinuousOn (f x) ys) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): (map₂' hfl hfr: Set γ) ⊆ Set.image2 f xs ys := by
  rw [map₂'_eq_map₂mm hfl hfr]
  exact map₂mm_subset_image2 hfcl hfcr

public theorem map₂'_eq_image2 {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfcl: ∀ y ∈ ys, ContinuousOn (f · y) xs) (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfcr: ∀ x ∈ xs, ContinuousOn (f x) ys) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): (map₂' hfl hfr: Set γ) = Set.image2 f xs ys := by
  apply Set.Subset.antisymm_iff.mpr
  constructor
  · exact map₂'_subset_image2 hfcl hfl hfcr hfr
  · exact image2_subset_map₂' hfl hfr
end cclo

/-
theorem left_distrib (x y z : NonemptyInterval α) : x * (y + z) ⊆ x * y + x * z := by
  unfold HMul.hMul instHMul Mul.mul instMul mul mul' QInterval.mul_pair
  dsimp
  unfold HAdd.hAdd instHAdd Add.add instAdd add mk
  dsimp
  apply NonemptyInterval.coeHom.injective
  have hfr := λ {s: Set ℚ} {t: Set ℚ} x (_: x ∈ s) ↦ (mul_left_sometone x).sometoneOn t
  have hfl := λ {s: Set ℚ} {t: Set ℚ} y (_: y ∈ t) ↦ (mul_right_sometone y).sometoneOn s
  have har := λ {s: Set ℚ} {t: Set ℚ} x (_: x ∈ s) ↦ SometoneOn.of_MonotoneOn ((add_left_mono (a := x)).monotoneOn t)
  have hal := λ {s: Set ℚ} {t: Set ℚ} y (_: y ∈ t) ↦ SometoneOn.of_MonotoneOn ((add_right_mono (a := y)).monotoneOn s)
  simp only [NonemptyInterval.coe_coeHom, ← NonemptyInterval.coe_def,
    NonemptyInterval.add_eq_map₂'_add,
    NonemptyInterval.map₂'_eq_ordClosure_image2,
    NonemptyInterval.map₂mm_eq_ordClosure_image2 hfl hfr,
    Set.ordClosure_image2_ordClosure_left_eq hfr,
    Set.ordClosure_image2_ordClosure_left_eq hal,
    Set.ordClosure_image2_ordClosure_right_eq har]
  apply Set.eq_of_subset_of_subset
  · apply Set.ordClosure.mono
    apply Set.image2_distrib_subset_left
    apply mul_add
  · -- 1 * x1 + (-1) * x2
    -- [0, 1]
    -- => [-1, 1]
    -- not distrib!!
    -- (1 + (-1)) * [0, 1]
    --
    sorry

theorem right_distrib (x y z : ComputableℝSeq) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, left_distrib, mul_comm, mul_comm z y]

-/

end NonemptyInterval
