import CommitGolf.Parameters
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf

/-- Instructions after leaf `k` and before the next leaf.
The back-edge is skipped only on the final tile. -/
def tailCount (k : Nat) : Nat :=
  if (k + 1) % 128 = 0 then
    if k + 1 = LENGTH then 5 else 6
  else if (k + 1) % 32 = 0 then 3
  else if (k + 1) % 16 = 0 then 1
  else 0

/-- Control instructions strictly before leaf `k`. -/
def controlPrefix (k : Nat) : Nat :=
  19 * (k / 128) + (k % 128) / 16 + 2 * ((k % 128) / 32) - (if k = LENGTH then 1 else 0)

def leafSteps (k n : Nat) : Nat := 12 * n + (controlPrefix (k + n) - controlPrefix k)
def leafCycles (k n : Nat) : Nat := 40 * n + (controlPrefix (k + n) - controlPrefix k)

/-- Program counter of leaf `k`. The image holds one tile and jumps back. -/
def leafPC (k : Nat) : Nat :=
  4123 + 12 * (k % 128) + (k % 128) / 16 + 2 * ((k % 128) / 32)

private theorem local_step (t : Nat) (ht : t < 127) :
    (t + 1) / 16 + 2 * ((t + 1) / 32) =
      t / 16 + 2 * (t / 32) +
        (if (t + 1) % 32 = 0 then 3 else if (t + 1) % 16 = 0 then 1 else 0) := by
  have closed : ∀ u : Fin 127,
      (u.val + 1) / 16 + 2 * ((u.val + 1) / 32) =
        u.val / 16 + 2 * (u.val / 32) +
          (if (u.val + 1) % 32 = 0 then 3 else if (u.val + 1) % 16 = 0 then 1 else 0) := by
    decide
  exact closed ⟨t, ht⟩

private theorem prefix_step (k : Nat) (hk : k < LENGTH) :
    controlPrefix (k + 1) = controlPrefix k + tailCount k := by
  have hk' : k < 16777216 := by simpa [LENGTH, LOG_LENGTH] using hk
  by_cases boundary : k % 128 = 127
  · simp only [controlPrefix, tailCount, boundary,
      show (k + 1) % 128 = 0 by omega,
      show (k + 1) / 128 = k / 128 + 1 by omega,
      ite_eq_right (show k ≠ LENGTH by omega)]
    by_cases last : k + 1 = LENGTH <;> simp [last] <;> (try split_ifs) <;> omega
  · have lt : k % 128 < 127 := by omega
    have mod1 : (k + 1) % 128 = k % 128 + 1 := by omega
    have div0 : (k + 1) / 128 = k / 128 := by omega
    have notK : k ≠ LENGTH := by omega
    have notLast : k + 1 ≠ LENGTH := by
      intro eq
      have hk0 : k = 16777215 := by simpa [LENGTH, LOG_LENGTH] using eq
      have : (16777215 : Nat) % 128 = 127 := by decide
      exact boundary (hk0 ▸ this)
    have nz : k % 128 + 1 ≠ 0 := by omega
    have mod32 : (k + 1) % 32 = (k % 128 + 1) % 32 := by omega
    have mod16 : (k + 1) % 16 = (k % 128 + 1) % 16 := by omega
    have tailEq : tailCount k =
        if (k % 128 + 1) % 32 = 0 then 3
        else if (k % 128 + 1) % 16 = 0 then 1 else 0 := by
      rw [tailCount, mod1, ite_eq_right nz, mod32, mod16]
    have lhs : controlPrefix (k + 1) =
        19 * (k / 128) + (k % 128 + 1) / 16 + 2 * ((k % 128 + 1) / 32) := by
      rw [controlPrefix, div0, mod1, ite_eq_right notLast, Nat.sub_zero]
    have rhs : controlPrefix k =
        19 * (k / 128) + k % 128 / 16 + 2 * (k % 128 / 32) := by
      rw [controlPrefix, ite_eq_right notK, Nat.sub_zero]
    have step := local_step (k % 128) lt
    rw [lhs, rhs, tailEq, Nat.add_assoc, step]
    omega

private theorem prefix_le (k n : Nat) (room : k + n ≤ LENGTH) :
    controlPrefix k ≤ controlPrefix (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, prefix_step _ (by omega)]
    exact (ih (by omega)).trans (Nat.le_add_right _ _)

def controls (k n : Nat) : Nat := controlPrefix (k + n) - controlPrefix k

theorem controls_succ (k n : Nat) (room : k + (n + 1) ≤ LENGTH) :
    controls k (n + 1) = tailCount k + controls (k + 1) n := by
  have inc := prefix_step k (by omega)
  have hi := prefix_le (k + 1) n (by omega)
  unfold controls
  rw [show k + (n + 1) = (k + 1) + n by omega]
  omega

theorem leaf_pc_slot (k : Nat) : leafPC k + 12 ≤ 5672 := by
  have : k % 128 ≤ 127 := by
    have := Nat.mod_lt k (show 0 < 128 by decide)
    omega
  unfold leafPC
  omega

theorem leaf_totals :
    leafSteps 0 LENGTH = 203816959 ∧ leafCycles 0 LENGTH = 673579007 := by
  decide

end CommitGolfCandidate.Chained.BinaryMachine
