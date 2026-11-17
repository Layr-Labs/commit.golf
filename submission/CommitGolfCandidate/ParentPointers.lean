import CommitGolfCandidate.CommitLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem commit_leaves_final_invariant (state : MachineState) (remaining : Nat)
    (invariant : CommitLeavesInvariant state remaining) (finished : MachineState)
    (reachable : finished ∈ support (commitLeaves state remaining)) :
    CommitLeavesInvariant finished 0 := by
  induction remaining generalizing state with
  | zero =>
    simp only [commitLeaves, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact invariant
  | succ remaining ih =>
    simp only [commitLeaves, mem_support_bind_iff] at reachable
    obtain ⟨next, reached, rest⟩ := reachable
    exact ih next (commit_leaves_next_invariant state next remaining invariant reached) rest

theorem parent_pointer_decrement (base : Word) (step remaining : Nat) :
    (base + BitVec.ofNat 64 (step * (remaining + 1))) - BitVec.ofNat 64 step =
      base + BitVec.ofNat 64 (step * remaining) := by
  have eq : step * (remaining + 1) = step * remaining + step := by simp [Nat.mul_add]
  rw [eq, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem parent_pointer_shift (node shift : Nat) :
    (BitVec.ofNat 64 node <<< shift) = BitVec.ofNat 64 (2^shift * node) := by
  have power : BitVec.twoPow 64 shift = BitVec.ofNat 64 (2^shift) := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [BitVec.shiftLeft_eq_mul_twoPow, power, ← BitVec.ofNat_mul, Nat.mul_comm]

theorem parent_pointer_done_iff (base : Word) (remaining : Nat)
    (bounded : remaining < 2^24) :
    base + BitVec.ofNat 64 (32 * remaining) = base ↔ remaining = 0 := by
  constructor
  · intro equal
    have offset : BitVec.ofNat 64 (32 * remaining) = 0 := by
      have sub := congrArg (fun word : Word => word - base) equal
      rw [BitVec.add_comm base _, BitVec.add_sub_cancel] at sub
      simpa using sub
    have natEqual := congrArg BitVec.toNat offset
    change (32 * remaining) % 18446744073709551616 = 0 at natEqual
    omega
  · intro empty
    subst remaining
    simp

end CommitGolfCandidate
