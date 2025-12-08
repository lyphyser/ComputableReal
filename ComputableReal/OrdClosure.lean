module
public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.UpperLower.Closure
public import ComputableReal.Sometone

namespace Set
variable {α: Type*}

open Interval

variable (s: Set α) {a b: α} (t: Set α)

section pre
variable [Preorder α]
public def ordClosure: Set α →o Set α where
  toFun (s: Set α) := (upperClosure s: Set α) ∩ (lowerClosure s: Set α)
  monotone' {s t: Set α} (h: s ⊆ t) := by
    apply inter_subset_inter
    · rw [UpperSet.coe_subset_coe]
      apply upperClosure_anti
      simp only [le_eq_subset]
      exact h
    · rw [LowerSet.coe_subset_coe]
      apply lowerClosure_mono
      simp only [le_eq_subset]
      exact h

public lemma ordClosure_eq_upperClosure_inter_lowerClosure: ordClosure s = (upperClosure s: Set α) ∩ (lowerClosure s: Set α) := by
  unfold ordClosure
  rfl

public lemma subset_ordClosure_self: s ⊆ ordClosure s := by
  rw [ordClosure_eq_upperClosure_inter_lowerClosure]
  exact subset_inter (subset_upperClosure) (subset_lowerClosure)

public lemma mem_ordClosure_of_mem {x: α} (hx: x ∈  s): x ∈ ordClosure s :=
  mem_of_mem_of_subset hx (subset_ordClosure_self s)

public lemma subset_ordClosure (h: s ⊆ t): s ⊆ ordClosure t :=
  subset_trans h (subset_ordClosure_self t)

public instance ordConnected_ordClosure: Set.OrdConnected (ordClosure s) := by
  rw [ordClosure_eq_upperClosure_inter_lowerClosure]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

variable {s} {t} in
public lemma ordClosure_subset_ordConnected (hst: s ⊆ t) (ht: Set.OrdConnected t): ordClosure s ⊆ t := by
  unfold ordClosure
  simp only [subset_def]
  rintro x ⟨hxu, hxl⟩
  simp only [SetLike.mem_coe, mem_upperClosure] at hxu
  simp only [SetLike.mem_coe, mem_lowerClosure] at hxl
  obtain ⟨u, ⟨hus, hux⟩⟩ := hxu
  obtain ⟨l, ⟨hls, hxl⟩⟩ := hxl
  have hlt := mem_of_mem_of_subset hls hst
  have hut := mem_of_mem_of_subset hus hst
  have := ht.out hut hlt
  simp only [subset_def, mem_Icc] at this
  exact this x ⟨hux, hxl⟩

public lemma ordClosure_eq_sInter_ordConnected: ordClosure s = ⋂₀ {t: Set α | t.OrdConnected ∧ s ⊆ t} := by
  apply Set.eq_of_subset_of_subset
  · apply subset_sInter
    rintro t ⟨ht, hst⟩
    exact ordClosure_subset_ordConnected hst ht
  · apply sInter_subset_of_mem
    simp only [mem_setOf_eq]
    constructor
    · exact ordConnected_ordClosure s
    · exact subset_ordClosure_self s

@[simp, grind =]
public lemma ordClosure_ordClosure: ordClosure (ordClosure s) = ordClosure s := by
  apply eq_of_subset_of_subset
  · apply ordClosure_subset_ordConnected
    · rfl
    · apply ordConnected_ordClosure
  · apply subset_ordClosure_self

public lemma mem_ordClosure {x: α}: x ∈ ordClosure s ↔ (∃ a ∈ s, a ≤ x) ∧ (∃ b ∈ s, x ≤ b) := by
  simp [ordClosure_eq_upperClosure_inter_lowerClosure]

public lemma ordClosure_eq_setOf: ordClosure s = {x | (∃ a ∈ s, a ≤ x) ∧ (∃ b ∈ s, x ≤ b)} := by
  ext x
  simp only [mem_setOf_eq]
  exact mem_ordClosure s

public lemma ordClosure_eq_iUnion_Icc: ordClosure s = ⋃ a ∈ s, ⋃ b ∈ s, Icc a b := by
  ext x
  simp only [mem_ordClosure, mem_iUnion, mem_Icc, exists_prop]
  grind

public lemma Icc_subset_ordClosure (ha: a ∈ s) (hb: b ∈ s): Icc a b ⊆ ordClosure s := by
  rw [ordClosure_eq_iUnion_Icc]
  apply subset_iUnion₂_of_subset a ha
  apply subset_iUnion₂_of_subset b hb
  apply subset_refl

public lemma ordClosure_eq_iff: ordClosure s = ordClosure t ↔ s ⊆ ordClosure t ∧ t ⊆ ordClosure s   := by
  constructor
  · intro h
    constructor
    · rw [← h]
      apply subset_ordClosure_self
    · rw [h]
      apply subset_ordClosure_self
  · rintro ⟨hst, hts⟩
    apply eq_of_subset_of_subset
    · apply ordClosure.mono at hst
      simpa using hst
    · apply ordClosure.mono at hts
      simpa using hts

public lemma union_ordClosure_subset: ordClosure s ∪ ordClosure t ⊆ ordClosure (s ∪ t) := by
  apply ordClosure.mono.le_map_sup

public lemma iUnion_ordClosure_subset {ι: Sort*} {f: ι → Set α}: ⋃ i: ι, ordClosure (f i) ⊆ ordClosure (⋃ i, f i) := by
  apply ordClosure.mono.le_map_iSup

public lemma sUnion_ordClosure_subset (S: Set (Set α)): ⋃ s ∈ S, ordClosure s ⊆ ordClosure (⋃₀ S) := by
  apply ordClosure.mono.le_map_sSup

public lemma inter_ordClosure_subset: ordClosure (s ∩ t) ⊆ (ordClosure s) ∩ (ordClosure t) := by
  apply ordClosure.mono.map_inf_le

public lemma iInter_ordClosure_subset {ι: Sort*} {f: ι → Set α}: ordClosure (⋂ i, f i) ⊆ ⋂ i: ι, ordClosure (f i) := by
  apply ordClosure.mono.map_iInf_le

public lemma sInter_ordClosure_subset (S: Set (Set α)): ordClosure (⋂₀ S) ⊆ ⋂ s ∈ S, ordClosure s := by
  apply ordClosure.mono.map_sInf_le

variable {β: Type*} [Preorder β]

public lemma image_ordClosure_subset_ordClosure_image {f: α → β} (hf: SometoneOn f (ordClosure s)): f '' ordClosure s ⊆ ordClosure (f '' s) := by
  simp only [ordClosure_eq_iUnion_Icc]
  simp only [image_iUnion, mem_image, iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, iUnion_subset_iff]
  intro a ha b hb
  have hab := Icc_subset_ordClosure s ha hb
  have := (hf.mono hab).image_Icc_union_Icc_subset
  apply subset_trans this _
  apply union_subset
  · apply subset_iUnion₂_of_subset a ha
    apply subset_iUnion₂_of_subset b hb
    apply subset_refl
  · apply subset_iUnion₂_of_subset b hb
    apply subset_iUnion₂_of_subset a ha
    apply subset_refl

@[simp, grind =]
public lemma ordClosure_image_ordClosure_eq {f: α → β} (hf: SometoneOn f (ordClosure s)): ordClosure (f '' ordClosure s) = ordClosure (f '' s) := by
  rw [ordClosure_eq_iff]
  constructor
  · apply image_ordClosure_subset_ordClosure_image s hf
  · apply subset_ordClosure
    apply image_mono
    exact subset_ordClosure_self s

variable {γ: Type*} [Preorder γ]

omit [Preorder α] in
variable {s} in
public lemma image2_ordClosure_subset_ordClosure_image2_left {f: α → β → γ} {t: Set β} (hf: ∀ x ∈ s, SometoneOn (f x) (ordClosure t)): Set.image2 f s (ordClosure t) ⊆ ordClosure (Set.image2 f s t) := by
  simp only [← Set.iUnion_image_left]
  apply subset_trans _ (iUnion_ordClosure_subset)
  simp only [iUnion_subset_iff]
  intro x hx
  apply subset_trans _ (subset_iUnion _ x)
  apply subset_trans _ (iUnion_ordClosure_subset)
  apply subset_trans _ (subset_iUnion _ hx)
  exact image_ordClosure_subset_ordClosure_image t (hf x hx)

omit [Preorder α] in
variable {s} in
@[simp, grind =]
public lemma ordClosure_image2_ordClosure_left_eq {f: α → β → γ} {t: Set β} (hf: ∀ x ∈ s, SometoneOn (f x) (ordClosure t)): ordClosure (Set.image2 f s (ordClosure t)) = ordClosure (Set.image2 f s t) := by
  rw [ordClosure_eq_iff]
  constructor
  · apply image2_ordClosure_subset_ordClosure_image2_left hf
  · apply subset_ordClosure
    apply image2_subset_left
    exact subset_ordClosure_self t

omit [Preorder β] in
variable {s} in
public lemma image2_ordClosure_subset_ordClosure_image2_right {f: α → β → γ} {t: Set β} (hf: ∀ y ∈ t, SometoneOn (f · y) (ordClosure s)): Set.image2 f (ordClosure s) t ⊆ ordClosure (Set.image2 f s t) := by
  simp only [← Set.iUnion_image_right]
  apply subset_trans _ (iUnion_ordClosure_subset)
  simp only [iUnion_subset_iff]
  intro y hy
  apply subset_trans _ (subset_iUnion _ y)
  apply subset_trans _ (iUnion_ordClosure_subset)
  apply subset_trans _ (subset_iUnion _ hy)
  exact image_ordClosure_subset_ordClosure_image s (hf y hy)

omit [Preorder β] in
variable {s} in
@[simp, grind =]
public lemma ordClosure_image2_ordClosure_right_eq {f: α → β → γ} {t: Set β} (hf: ∀ y ∈ t, SometoneOn (f · y) (ordClosure s)): ordClosure (Set.image2 f (ordClosure s) t) = ordClosure (Set.image2 f s t) := by
  rw [ordClosure_eq_iff]
  constructor
  · apply image2_ordClosure_subset_ordClosure_image2_right hf
  · apply subset_ordClosure
    apply image2_subset_right
    exact subset_ordClosure_self s

end pre

section linear
variable [LinearOrder α]
variable (s: Set α) in
public lemma uIcc_subset_ordClosure (ha: a ∈ s) (hb: b ∈ s): uIcc a b ⊆ ordClosure s := by
  replace ha := mem_of_mem_of_subset ha (subset_ordClosure_self s)
  replace hb := mem_of_mem_of_subset hb (subset_ordClosure_self s)
  exact (ordConnected_ordClosure s).uIcc_subset ha hb
end linear
