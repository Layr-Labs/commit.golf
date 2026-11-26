import CommitGolfCandidate.TruncBTailResult
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 5000
set_option maxHeartbeats 20000
attribute [local irreducible] bucketState tested copied compared lowerHash readBuffer storedAt Runs
theorem freshSafe (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) (h : HashedFrame o input n s) :
    safeSteps storeOps (tested s) := by
  have t := testInfo s h.pc (rowBucket input n) h.index
  have a := compareAccess o input n s h
  apply safeStore (tested s)
  · rw [t.1]
    exact (show ∀ v : Fin 256, accessValid (BitVec.ofNat 64 (flag v.val)) 1 by decide) (rowBucket input n)
  · exact fun j=>a.1 j.val j.isLt
  · intro j;rw [Nat.zero_add];exact a.2 j.val j.isLt

theorem recordFlag (o : Oracle) (input : CheckInput) (n : Nat) (s : MachineState) (h : HashedFrame o input n s) :
    (bucketState s).getReg .x7=0 ↔ s.getByte (BitVec.ofNat 64 (flag (rowBucket input n).val))=0 := by
  have info := bucketInfo s h.pc (rowBucket input n) h.index
  rw [info.2.2.2.1];exact flagZeroIff _

end CommitGolfCandidate.Trunc.Batch
