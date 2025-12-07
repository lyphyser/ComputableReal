module

public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Topology.Defs.Filter
public import ComputableReal.Sometone
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
end lattice

section pre_pre_lattice
variable [Preorder α] [Preorder β] [Lattice γ] [Lattice δ]

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

public def map₂' {f: α → β → γ} {xs : NonemptyInterval α} {ys: NonemptyInterval β} (hfl: ∀ y ∈ ys, MonotoneOn (f · y) xs) (hfr: ∀ x ∈ xs, MonotoneOn (f x) ys): NonemptyInterval γ :=
  ⟨⟨f xs.fst ys.fst, f xs.snd ys.snd⟩, by
    have h1 := hfl ys.fst ys.fst_mem xs.fst_mem xs.snd_mem xs.fst_le_snd
    have h2 := hfr xs.snd xs.snd_mem ys.fst_mem ys.snd_mem ys.fst_le_snd
    exact le_trans h1 h2⟩

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
end linear

section
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
end
end NonemptyInterval
