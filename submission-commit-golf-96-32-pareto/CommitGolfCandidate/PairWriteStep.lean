import CommitGolfCandidate.PairLocations
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4000
set_option maxHeartbeats 250000
attribute [local irreducible] headState Nat.iterate overrideState openingCopyState submission
theorem writeMemory (s : MachineState) :
    (overrideState s).mem = (openingCopyState (headState s)).mem := by unfold overrideState latchState; rfl

theorem headMemory (s : MachineState) : (headState s).mem = s.mem := by unfold headState blockPrefix headOps; rfl

theorem belowWord (s : MachineState) {n i : Nat} (f : Frame s (n+1)) (bi : i < 2^24)
    (loaded : s.getMem (BitVec.ofNat 64 (indexBase+8*n)) = BitVec.ofNat 64 i)
    (addr : Word) (below : addr.toNat < outBase) :
    (overrideState s).getMem addr = s.getMem addr := by
  rw [show (overrideState s).getMem addr = (openingCopyState (headState s)).getMem addr from congrFun (writeMemory s) addr]
  rw [opening_copy_memory_outside]
  · exact congrFun (headMemory s) addr
  · intro j equal
    rw [(locations s f bi loaded).2, ← BitVec.ofNat_add] at equal
    have hh := congrArg BitVec.toNat equal
    have bound := j.isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by dsimp [outBase] at *; omega)] at hh
    omega

theorem oneSlot (s : MachineState) {n i : Nat} (f : Frame s (n+1)) (bi : i < 2^24)
    (loaded : s.getMem (BitVec.ofNat 64 (indexBase+8*n)) = BitVec.ofNat 64 i)
    (p : Nat) (bp : p < 128) :
    readBuffer (overrideState s) (outBase+32*p) 32 =
      if i/131072 = p then readBuffer s (childAddress (i/65536)) 32 else
        readBuffer s (outBase+32*p) 32 := by
  have loc := locations s f bi loaded
  have bounds : childAddress (i/65536) % 8 = 0 ∧ childAddress (i/65536) + 32 ≤ outBase := childBounds ⟨i/65536,by omega⟩
  rw [read_buffer_memory_congr _ _ (writeMemory s)]
  split
  next yes =>
    rw [← yes]
    rw [opening_copy_digest _ (childAddress (i/65536)) _ loc.1 loc.2 bounds.1
      (by dsimp [outBase]; omega) (by dsimp [outBase] at bounds; omega)
      (by dsimp [outBase]; omega) (Or.inl (by omega)),read_buffer_memory_congr _ _ (headMemory s)]
  next no =>
    rw [opening_copy_preserves_digest _ _ _ loc.2 (by dsimp [outBase]; omega)
      (by dsimp [outBase]; omega) (by dsimp [outBase]; omega)
      (by dsimp [outBase]; omega),read_buffer_memory_congr _ _ (headMemory s)]

end CommitGolfCandidate.PairCap
