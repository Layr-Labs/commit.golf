import CommitGolfCandidate.TruncBLatch
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 5100
set_option maxHeartbeats 90000
theorem flagSpan (p : Nat) (hp : p<128) (u : Fin 256) :
    flag u.val<2^64 ∧ Separate (flag u.val) 1 (sourceRow p) 64 ∧ Separate (flag u.val) 1 (outSlot p) 32 := by
  have bu:=u.isLt;simp only [Separate,flag,sourceRow,outSlot];omega
theorem cellSpan (p : Nat) (hp : p<128) (u : Fin 256) (future : p<u.val/2) :
    cell u.val+32≤2^64 ∧ Separate (cell u.val) 32 (sourceRow p) 64 ∧ Separate (cell u.val) 32 (outSlot p) 32 := by
  have bu:=u.isLt;simp only [Separate,cell,heapOffset,sourceRow,outSlot];omega
theorem gapSpan (p : Nat) (hp : p<128) (v : Fin 128) (future : p<v.val) :
    sourceRow v.val+64+32≤2^64 ∧ Separate (sourceRow v.val+64) 32 (sourceRow p) 64 ∧ Separate (sourceRow v.val+64) 32 (outSlot p) 32 := by
  have bv:=v.isLt;simp only [Separate,sourceRow,outSlot];omega
theorem proofSpan (p : Nat) (hp : p<128) (v : Fin 128) :
    inSlot v.val+32≤2^64 ∧ Separate (inSlot v.val) 32 (sourceRow p) 64 ∧ Separate (inSlot v.val) 32 (outSlot p) 32 := by
  have bv:=v.isLt;simp only [Separate,sourceRow,inSlot,outSlot];omega
theorem priorSpan (p : Nat) (hp : p<128) (v : Fin 128) (before : v.val<p) :
    outSlot v.val+32≤2^64 ∧ Separate (outSlot v.val) 32 (sourceRow p) 64 ∧ Separate (outSlot v.val) 32 (outSlot p) 32 := by
  have bv:=v.isLt;simp only [Separate,sourceRow,outSlot];omega
theorem rootSpan (p : Nat) (hp : p<128) :
    Separate 4294971392 32 (sourceRow p) 64 ∧ Separate 4294971392 32 (outSlot p) 32 := by
  simp only [Separate,sourceRow,outSlot];omega
end CommitGolfCandidate.Trunc.Batch
