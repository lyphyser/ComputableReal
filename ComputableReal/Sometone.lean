module

public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Order.Interval.Set.UnorderedInterval

import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Set.Function
import Mathlib.Order.Interval.Set.Image

open Set
open Interval
open OrderDual

variable {α β: Type*} [LE α] [LE β] in
@[expose] public def SometoneOn (f : α → β) (s : Set α) := ∀ ⦃a⦄ (_ : a ∈ s) ⦃b⦄ (_ : b ∈ s) ⦃c⦄ (_ : c ∈ s), a ≤ b → b ≤ c → (f a ≤ f b ∧ f b ≤ f c) ∨ (f c ≤ f b ∧ f b ≤ f a)

namespace SometoneOn

variable {α β : Type*} {f : α → β} {s: Set α}

section base
variable [LE α] [LE β]

@[simp]
public theorem dual_left : SometoneOn (f ∘ ofDual) s ↔ SometoneOn f s := by
  unfold SometoneOn
  have htm: ∀a, toDual a ∈ s ↔ a ∈ s := by
    intro a
    exact MapsTo.mem_iff (fun ⦃x⦄ a => a) fun ⦃x⦄ a => a
  simp only [Function.comp_apply, OrderDual.forall, ofDual_toDual, toDual_le_toDual, htm]
  grind

@[simp]
public theorem dual_right : SometoneOn (toDual ∘ f: α → βᵒᵈ) s ↔ SometoneOn f s := by
  unfold SometoneOn
  simp only [Function.comp_apply, toDual_le_toDual]
  grind
end base

section preorder
variable [Preorder α] [Preorder β]
public lemma of_MonotoneOn (h: MonotoneOn f s): SometoneOn f s := by
  intro a ha b hb c hc hab hbc
  left
  exact ⟨h ha hb hab, h hb hc hbc⟩

public lemma of_AntitoneOn (h: AntitoneOn f s): SometoneOn f s := by
  intro a ha b hb c hc hab hbc
  right
  exact ⟨h hb hc hbc, h ha hb hab⟩

variable {a b : α}
public lemma mapsTo_Icc_union_Icc (h: SometoneOn f (Icc a b)): MapsTo f (Icc a b) ((Icc (f a) (f b)) ∪ (Icc (f b) (f a))) := by
  rw [MapsTo.eq_1]
  intro x hx
  obtain ⟨hax, hxb⟩ := mem_Icc.mp hx
  have ha: a ∈ Icc a b := by grind
  have hb: b ∈ Icc a b := by grind
  specialize h ha hx hb hax hxb
  simp only [mem_union, mem_Icc]
  exact h

public lemma image_Icc_union_Icc_subset (h : SometoneOn f (Icc a b)) : f '' Icc a b ⊆ (Icc (f a) (f b)) ∪ (Icc (f b) (f a)) :=
  h.mapsTo_Icc_union_Icc.image_subset
end preorder

section lattice
variable [Preorder α] [Lattice β] {a b : α} {s: Set α}

public lemma mapsTo_uIcc (h: SometoneOn f (Icc a b)): MapsTo f (Icc a b) [[f a, f b]] := by
  have := mapsTo_Icc_union_Icc h
  apply MapsTo.mono_right this
  apply union_subset
  · exact Icc_subset_uIcc
  · exact Icc_subset_uIcc'

public lemma image_uIcc_subset (h : SometoneOn f (Icc a b)) : f '' Icc a b ⊆ [[f a, f b]] :=
  h.mapsTo_uIcc.image_subset
end lattice

section linear
variable [Preorder α] [Std.IsLinearPreorder α] [Preorder β]

public def monotoneOn (h: SometoneOn f s) {a: α} (ha: a ∈ s) {b: α} (hb: b ∈ s) (hab: a ≤ b) (hfab: f a < f b): MonotoneOn f s := by
  intro x hx y hy hxy
  have hxab := (h hx ha hb · hab)
  have haxy := (h ha hx hy · hxy)
  have haby := h ha hb hy hab
  have hxyb := h hx hy hb hxy
  clear h
  have hxa: x ≤ a ∨ a ≤ x := Std.IsLinearPreorder.le_total x a
  have hyb: y ≤ b ∨ b ≤ y := Std.IsLinearPreorder.le_total y b
  grind

public def antitoneOn (h: SometoneOn f s) {a: α} (ha: a ∈ s) {b: α} (hb: b ∈ s) (hab: a ≤ b) (hfab: f b < f a): AntitoneOn f s := by
  rw [← monotoneOn_toDual_comp_iff]
  rw [← dual_right] at h
  have: ∀ a b, toDual (f a) < toDual (f b) ↔ f b < f a := by
    simp
  simp_rw [← this] at hfab
  exact monotoneOn h ha hb hab hfab

public def monotoneOn_or_antitoneOn (h: SometoneOn f s): MonotoneOn f s ∨ AntitoneOn f s := by
  by_cases he: ∃ a ∈ s, ∃ b ∈ s, a ≤ b ∧ (f a < f b ∨ f b < f a)
  · obtain ⟨a, ha, b, hb, hab, hfab⟩ := he
    rcases hfab with hfab | hfab
    · left
      exact h.monotoneOn ha hb hab hfab
    · right
      exact h.antitoneOn ha hb hab hfab
  · simp only [not_exists, not_and, not_or] at he
    left
    intro x hx y hy hxy
    specialize he x hx y hy hxy
    simp only [lt_iff_le_not_ge, not_and, not_not] at he
    specialize h hx hy hy hxy (le_refl y)
    rcases h with ⟨hfxy, _⟩ | ⟨_, hfyx⟩
    · exact hfxy
    · exact he.right hfyx

public def iff_MonotoneOn_or_antitoneOn: SometoneOn f s ↔ MonotoneOn f s ∨ AntitoneOn f s := by
  constructor
  · exact monotoneOn_or_antitoneOn
  · intro h
    rcases h with h | h
    · exact of_MonotoneOn h
    · exact of_AntitoneOn h
end linear
end SometoneOn

variable {α β: Type*} [Preorder α] [Preorder β] in
@[expose] public def Sometone (f : α → β) := ∀ ⦃a b c⦄, a ≤ b → b ≤ c → (f a ≤ f b ∧ f b ≤ f c) ∨ (f c ≤ f b ∧ f b ≤ f a)

namespace Sometone
variable {α β : Type*} {f : α → β}

section base
variable [Preorder α] [Preorder β]

public lemma iff_sometoneOn_univ : Sometone f ↔ SometoneOn f univ := by
  simp [Sometone, SometoneOn]

public lemma sometoneOn (h : Sometone f) (s : Set α) : SometoneOn f s := by
  intro a _ b _ c _ hab hbc
  specialize h hab hbc
  exact h

@[simp]
public theorem dual_left : Sometone (f ∘ ofDual) ↔ Sometone f := by
  simp_rw [iff_sometoneOn_univ, SometoneOn.dual_left]

@[simp]
public theorem dual_right : Sometone (toDual ∘ f : α → βᵒᵈ) ↔ Sometone f := by
  simp_rw [iff_sometoneOn_univ, SometoneOn.dual_right]

public lemma of_Monotone (h : Monotone f) : Sometone f := by
  rw [iff_sometoneOn_univ]
  exact SometoneOn.of_MonotoneOn (h.monotoneOn _)

public lemma of_Antitone (h : Antitone f) : Sometone f := by
  rw [iff_sometoneOn_univ]
  exact SometoneOn.of_AntitoneOn (h.antitoneOn _)

variable {a b : α}

public lemma mapsTo_Icc_union_Icc (h : Sometone f) : MapsTo f (Icc a b) ((Icc (f a) (f b)) ∪ (Icc (f b) (f a))) :=
  (h.sometoneOn (Icc a b)).mapsTo_Icc_union_Icc

public lemma image_Icc_union_Icc_subset (h : Sometone f) : f '' Icc a b ⊆ (Icc (f a) (f b) ∪ Icc (f b) (f a)) :=
  (h.sometoneOn (Icc a b)).image_Icc_union_Icc_subset
end base

section lattice
variable [Preorder α] [Lattice β] {a b : α}

public lemma mapsTo_uIcc (h : Sometone f) : MapsTo f (Icc a b) [[f a, f b]] := by
  exact (h.sometoneOn (Icc a b)).mapsTo_uIcc

public lemma image_uIcc_subset (h : Sometone f) : f '' Icc a b ⊆ [[f a, f b]] := by
  exact (h.sometoneOn (Icc a b)).image_uIcc_subset
end lattice

section linear
variable [LinearOrder α] [Preorder β]

public def monotone (h : Sometone f) (hab : a ≤ b) (hfab : f a < f b) : Monotone f := by
  rw [← monotoneOn_univ]
  exact (iff_sometoneOn_univ.mp h).monotoneOn (mem_univ a) (mem_univ b) hab hfab

public def antitone (h : Sometone f) (hab : a ≤ b) (hfab : f b < f a) : Antitone f := by
  rw [← antitoneOn_univ]
  exact (iff_sometoneOn_univ.mp h).antitoneOn (mem_univ a) (mem_univ b) hab hfab

public def monotone_or_antitone (h : Sometone f) : Monotone f ∨ Antitone f := by
  rw [← monotoneOn_univ, ← antitoneOn_univ]
  exact (iff_sometoneOn_univ.mp h).monotoneOn_or_antitoneOn

public def iff_Monotone_or_antitone : Sometone f ↔ Monotone f ∨ Antitone f := by
  rw [iff_sometoneOn_univ, ← monotoneOn_univ, ← antitoneOn_univ]
  exact SometoneOn.iff_MonotoneOn_or_antitoneOn
end linear
end Sometone

section mul
variable {α: Type*} [Semiring α] [LinearOrder α] [PosMulMono α] [AddRightMono α] [AddRightReflectLE α] [ExistsAddOfLE α]
public def mul_left_sometone [PosMulMono α] (x: α): Sometone (x * ·) := by
  if h: 0 ≤ x then
    apply Sometone.of_Monotone
    apply monotone_iff_forall_lt.mpr
    intro y z hyz
    exact mul_le_mul_of_nonneg_left (le_of_lt hyz) h
  else
    apply Sometone.of_Antitone
    apply antitone_iff_forall_lt.mpr
    intro y z hyz
    exact mul_le_mul_of_nonpos_left (le_of_lt hyz) (le_of_lt (not_le.mp h))

public def mul_right_sometone [MulPosMono α] (x: α): Sometone (· * x) := by
  if h: 0 ≤ x then
    apply Sometone.of_Monotone
    apply monotone_iff_forall_lt.mpr
    intro y z hyz
    exact mul_le_mul_of_nonneg_right (le_of_lt hyz) h
  else
    apply Sometone.of_Antitone
    apply antitone_iff_forall_lt.mpr
    intro y z hyz
    exact mul_le_mul_of_nonpos_right (le_of_lt hyz) (le_of_lt (not_le.mp h))
end mul
