import Mathlib.Data.Set.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Filter.Basic
import ComputableReal.InfStream

open Filter

/-!
  # InfStream filter interface
-/

universe u v w

namespace InfStream

variable {β : Type u} {α : Type w} [SetLike α β] {τ : Type u} {T : τ → Type v}

/--
  Generates a Filter from the stream.
  (Valid when α has a SetLike instance interpreted as sets of β)
-/
def toFilter (s : InfStream τ T α) : Filter β :=
  ⨅ n, 𝓟 (s.seq n : Set β)

end InfStream
