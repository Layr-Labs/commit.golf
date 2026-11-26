import CommitGolfCandidate.TruncBProgress
import CommitGolfCandidate.TruncBFill
import CommitGolfCandidate.TruncMask
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 10000
set_option maxHeartbeats 140000

private theorem halfStep (s : MachineState) (a : Nat) (ptr : s.getReg .x24=BitVec.ofNat 64 a)
    (al : a%8=0) (bd : a+32≤MEMORY_BYTES) (pc : s.pc=loc 1017) :
    Trunc.Runs (Trunc.submission.image .check) s ((s.setHalfword (BitVec.ofNat 64 (a+30)) 0).setPC (loc 1018)) 1 1 := by
  have address : s.getReg .x24+signExtend12 30=BitVec.ofNat 64 (a+30) := by
    rw [ptr];exact (BitVec.ofNat_add a 30).symm
  have ok : accessValid (BitVec.ofNat 64 (a+30)) 2 := by
    unfold MEMORY_BYTES at bd
    simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a+30<2^64),MEMORY_BYTES];omega
  apply one 1017 _ _ (.SH .x24 .x0 30) (by decide) pc (by rfl) _ rfl
  simp only [ordinaryStep,execInstrBr,memoryArgumentsValid,memAccess,address,ok,ite_true,pc]
  rfl

private theorem maskCode (m : MachineState) (a : Nat) (pc : m.pc=5532) (ptr : m.getReg .x24=BitVec.ofNat 64 a)
    (al : a%8=0) (bd : a+32≤MEMORY_BYTES) :
    Trunc.Runs (Trunc.submission.image .check) m ((m.setHalfword (BitVec.ofNat 64 (a+30)) 0).setPC 5568) 3 3 := by
  have mv:=jumpAt (Trunc.submission.image .check) m 359 1017 2632 (by decide) pc (by rfl) (by decide)
  have sh:=halfStep (m.setPC (loc 1017)) a ptr al bd rfl
  let u:=((m.setPC (loc 1017)).setHalfword (BitVec.ofNat 64 (a+30)) 0).setPC (loc 1018)
  have go:=jumpAt (Trunc.submission.image .check) u 1018 368 2094552 (by decide) rfl (by rfl) (by decide)
  exact chain (chain mv sh) go

private theorem maskedHashed (t : MachineState) (a : Nat) (d : Digest) (ptr : t.getReg .x24=BitVec.ofNat 64 a)
    (al : a%8=0) (bd : a+32≤MEMORY_BYTES) :
    (hashed t d).setHalfword (BitVec.ofNat 64 (a+30)) 0=hashed t (padLow d) := by
  unfold hashed;rw [ptr]
  exact clearedReply _ a d al (by unfold MEMORY_BYTES at bd;omega)

attribute [local irreducible] hashed in
theorem pairMaskTail (o : Oracle) (t : MachineState) (d : Digest) (pc : (hashed t d).pc=5532)
    (a : Nat) (ptr : t.getReg .x24=BitVec.ofNat 64 a) (al : a%8=0) (bd : a+32≤MEMORY_BYTES) :
    Runs o (hashed t d) ((hashed t (padLow d)).setPC 5568) 3 0 := by
  have addr : (hashed t d).getReg .x24=BitVec.ofNat 64 a := by
    unfold hashed;rw [writeBits_register];exact ptr
  have code:=maskCode (hashed t d) a pc addr al bd
  rw [maskedHashed t a d ptr al bd] at code
  exact pureBlockRuns (fun fuel=>code fuel false)
end CommitGolfCandidate.Trunc.Batch
