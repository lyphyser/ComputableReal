/-!
  # InfStream (Generic State Machine)
-/

universe u v w

structure InfStream (τ : Type u) (T : τ → Type v) (α : Type w) where
  stateTy : τ
  init : T stateTy
  step : Nat → T stateTy → T stateTy × α

namespace InfStream

variable {τ : Type u} {T : τ → Type v} {α : Type w}

def compute_step (s : InfStream τ T α) (st : T s.stateTy) (k n : Nat) :
    T s.stateTy × α :=
  let res := s.step k st
  match n with
  | 0 => res
  | n + 1 => compute_step s res.1 (k + 1) n

def step_n (s : InfStream τ T α) (n : Nat) : T s.stateTy × α :=
  s.compute_step s.init 0 n

def seq (s : InfStream τ T α) (n : Nat) : α :=
  (s.step_n n).2

/--
  Witnesses the state and value at step `n`.
-/
structure InfStreamAt (s : InfStream τ T α) (n : Nat) where
  state : T s.stateTy
  val : α
  is_step : s.step_n n = (state, val)

def run (s : InfStream τ T α) (n : Nat) : InfStreamAt s n :=
  let res := s.step_n n
  ⟨res.1, res.2, rfl⟩

def ofFn [Inhabited τ] [Inhabited (T default)] (f : Nat → α) : InfStream τ T α :=
  { stateTy := default
    init := default
    step := fun n _ => (default, f n) }

end InfStream
