import Mathlib.Data.Set.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.Ultra.Completion

import ComputableReal.SetInfStream

open Filter

/-!
  # CauchyStream & Coercions
-/

universe u v w

section

class SetLikeSurjective (α β : Type*) [SetLike α β] : Prop where
  surj : Function.Surjective fun a : α => (a : Set β)

class CauchyFilterCountablyGenerated (β : Type*) [UniformSpace β] : Prop where
  isCountablyGenerated : ∀ f : CauchyFilter β, f.1.IsCountablyGenerated

variable (τ : Type u) (T : τ → Type v) (β : Type u) [UniformSpace β]
variable (α : Type w) [SetLike α β] [SetLikeSurjective α β] [CauchyFilterCountablyGenerated β]
variable [Inhabited τ] [Inhabited (T default)]

/--
  `CauchyStream` is the bundled subtype of streams that generate Cauchy filters.
-/
def CauchyStream :=
  { s : InfStream τ T α // Cauchy s.toFilter }

local instance : UniformSpace { f : Filter β // Cauchy f } :=
  (inferInstance : UniformSpace (CauchyFilter β))

/--
  Coercion: a `CauchyStream` can be used where a `CauchyFilter` is expected.
-/
instance : CoeTC (CauchyStream τ T β α) (CauchyFilter β) where
  coe s := ⟨s.1.toFilter, s.2⟩

/-!
  ### Transporting instances from `CauchyFilter`
-/

instance : UniformSpace (CauchyStream τ T β α) :=
  UniformSpace.comap (fun s => (s : CauchyFilter β)) inferInstance

private def isUniformInducing_coe :
    IsUniformInducing (fun s : CauchyStream τ T β α => (s : CauchyFilter β)) :=
  (isUniformInducing_iff_uniformSpace).mpr rfl

instance [IsUltraUniformity (CauchyFilter β)] : IsUltraUniformity (CauchyStream τ T β α) := by
  letI : IsUltraUniformity { f : Filter β // Cauchy f } :=
    (inferInstance : IsUltraUniformity (CauchyFilter β))
  have h_inducing :
      IsUniformInducing (fun s : CauchyStream τ T β α => (s : CauchyFilter β)) :=
    isUniformInducing_coe τ T β α
  exact h_inducing.isUltraUniformity

theorem exists_stream_of_cauchy (f : CauchyFilter β) :
    ∃ s : InfStream τ T α, s.toFilter = f.1 := by
  classical
  haveI := CauchyFilterCountablyGenerated.isCountablyGenerated (β:=β) f
  obtain ⟨x, hxanti, hxmem⟩ := f.1.exists_antitone_seq
  choose a ha using (fun n => (SetLikeSurjective.surj (α:=α) (β:=β)) (x n))
  let s : InfStream τ T α := InfStream.ofFn a
  refine ⟨s, ?_⟩
  apply Filter.ext
  intro U
  have hxInf :
      (⨅ n, 𝓟 (x n)).HasAntitoneBasis x :=
    Filter.HasAntitoneBasis.iInf_principal hxanti
  have hxInf_mem :
      U ∈ ⨅ n, 𝓟 (x n) ↔ ∃ i, x i ⊆ U := by
    simpa using (hxInf.1.mem_iff : U ∈ ⨅ n, 𝓟 (x n) ↔ ∃ i, True ∧ x i ⊆ U)
  have hxmem' : U ∈ f.1 ↔ ∃ i, x i ⊆ U := by
    simpa using (hxmem : U ∈ f.1 ↔ ∃ i, x i ⊆ U)
  have hfilter : s.toFilter = ⨅ n, 𝓟 (x n) := by
    ext V
    simp [s, InfStream.toFilter, InfStream.seq_ofFn, ha]
  simpa [hfilter] using (hxInf_mem.trans hxmem'.symm)

noncomputable def choiceStream (f : CauchyFilter β) : CauchyStream τ T β α :=
  ⟨Classical.choose (exists_stream_of_cauchy (τ:=τ) (T:=T) (β:=β) (α:=α) f),
    by
      simpa [Classical.choose_spec (exists_stream_of_cauchy (τ:=τ) (T:=T) (β:=β) (α:=α) f)]
        using f.2⟩

theorem choiceStream_coe (f : CauchyFilter β) :
    (choiceStream (τ:=τ) (T:=T) (β:=β) (α:=α) f : CauchyFilter β) = f := by
  apply Subtype.ext
  simp [choiceStream,
    Classical.choose_spec (exists_stream_of_cauchy (τ:=τ) (T:=T) (β:=β) (α:=α) f)]

theorem leftInverse_coe :
    Function.LeftInverse (fun s : CauchyStream τ T β α => (s : CauchyFilter β))
      (choiceStream (τ:=τ) (T:=T) (β:=β) (α:=α)) :=
  choiceStream_coe (τ:=τ) (T:=T) (β:=β) (α:=α)

instance : CompleteSpace (CauchyStream τ T β α) := by
  have h_inducing :
      IsUniformInducing (fun s : CauchyStream τ T β α => (s : CauchyFilter β)) :=
    isUniformInducing_coe τ T β α
  have hsurj :
      Function.Surjective (fun s : CauchyStream τ T β α => (s : CauchyFilter β)) :=
    (Function.LeftInverse.surjective (leftInverse_coe (τ:=τ) (T:=T) (β:=β) (α:=α)))
  have h_complete :
      CompleteSpace (CauchyFilter β) :=
    (inferInstance : CompleteSpace (CauchyFilter β))
  exact
    (IsUniformInducing.completeSpace_congr h_inducing hsurj).mpr h_complete

end
