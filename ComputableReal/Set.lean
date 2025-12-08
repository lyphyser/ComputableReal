module
public import Mathlib.Order.Interval.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.UpperLower.Closure

namespace Set
variable {α: Type*}

open Interval

section lattice
variable [Lattice α] {a b a₁ b₁ a₂ b₂: α}

public lemma uIcc_subset_Icc_iff_mem :
    [[a₁, b₁]] ⊆ Icc a₂ b₂ ↔ a₁ ∈ Icc a₂ b₂ ∧ b₁ ∈ Icc a₂ b₂ :=
  Iff.intro (fun h => ⟨h left_mem_uIcc, h right_mem_uIcc⟩) fun h =>
    uIcc_subset_Icc h.1 h.2
end lattice
end Set
