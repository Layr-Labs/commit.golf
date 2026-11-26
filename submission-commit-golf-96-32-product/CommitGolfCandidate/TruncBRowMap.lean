import CommitGolfCandidate.TruncBReadFrame
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 90000
attribute [local irreducible] readBuffer copyAt storedAt nextEdge storeState

theorem copiedMap (s : MachineState) (pc : s.pc=5120) (u v : Fin 256) (idx : s.getReg .x20=BitVec.ofNat 64 u.val)
    (hs : s.getReg .x21=256) :
    storedAt (copied s) v = if v=u then some (readBuffer s 256 32) else storedAt s v := by
  have info := testInfo s pc u idx
  have eqMem (a b : MachineState) (e : a.mem=b.mem) : storedAt a v=storedAt b v := by
    have bb : a.getByte (BitVec.ofNat 64 (flag v.val)) = b.getByte (BitVec.ofNat 64 (flag v.val)) := by
      simp only [MachineState.getByte,MachineState.getMem,e]
    simp only [storedAt,bb,read_buffer_memory_congr a b e]
  change storedAt (nextEdge (storeState (tested s))) v=_
  rw [eqMem _ _ (nextMem _),writeMap (tested s) u v info.1 info.2.1 (info.2.2.1.trans hs),
    read_buffer_memory_congr _ _ info.2.2.2,eqMem _ _ info.2.2.2]

end CommitGolfCandidate.Trunc.Batch
