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

def ofFn [Inhabited τ] [Inhabited (T default)] (f : Nat → α) : InfStream τ T α := by
  classical
  exact
    { stateTy := (default : τ)
      init := (default : T (default : τ))
      step := fun n _ => ((default : T (default : τ)), f n) }

theorem compute_step_ofFn [Inhabited τ] [Inhabited (T default)] (f : Nat → α) (k n : Nat) :
    (ofFn (τ:=τ) (T:=T) f).compute_step (ofFn (τ:=τ) (T:=T) f).init k n =
      ((ofFn (τ:=τ) (T:=T) f).init, f (k + n)) := by
  induction n generalizing k with
  | zero =>
      simp [compute_step, ofFn]
  | succ n ih =>
      simp [compute_step, ofFn]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (ih (k:=k + 1))

@[simp] theorem seq_ofFn [Inhabited τ] [Inhabited (T default)] (f : Nat → α) (n : Nat) :
    (ofFn (τ:=τ) (T:=T) f).seq n = f n := by
  simp [seq, step_n, compute_step_ofFn, Nat.add_comm]

end InfStream
