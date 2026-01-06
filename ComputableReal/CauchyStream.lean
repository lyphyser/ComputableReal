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

variable (τ : Type u) (T : τ → Type v) (β : Type u) [UniformSpace β] (α : Type w) [SetLike α β]

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

axiom choiceStream (f : CauchyFilter β) : CauchyStream τ T β α

axiom choiceStream_coe (f : CauchyFilter β) :
  (choiceStream (τ:=τ) (T:=T) (β:=β) (α:=α) f : CauchyFilter β) = f

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
