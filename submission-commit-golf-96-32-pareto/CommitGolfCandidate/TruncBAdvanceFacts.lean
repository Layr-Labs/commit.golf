import CommitGolfCandidate.TruncBSpans
import CommitGolfCandidate.TruncBBranches
import CommitGolfCandidate.TruncBAccess
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8000
set_option maxHeartbeats 200000

theorem sameStoredAt (s t : MachineState) (u : Fin 256)
    (b : byteAt t (flag u.val)=byteAt s (flag u.val)) (d : digestAt t (cell u.val)=digestAt s (cell u.val)) :
    storedAt t u=storedAt s u := by
  unfold storedAt;unfold byteAt at b;unfold digestAt at d;rw [b,d]
theorem oldCellAfter {s t : MachineState} (p : Nat) (small : p<128) (quiet : AreaQuiet s t p)
    (u : Fin 256) (above : p<u.val/2) : storedAt t u=storedAt s u := by
  obtain ⟨fb,fc,fd⟩ := flagSpan p small u
  obtain ⟨cb,cc,cd⟩ := cellSpan p small u above
  exact sameStoredAt s t u (quiet (flag u.val) fb fc fd) (areaDigest quiet cb cc cd)

def pairStride (r : Reg) : Word :=
  (match r with | .x19 | .x24 => 32 | .x22 => 2 | .x23 => 96 | .x27 => signExtend12 4095 | _ => 0)

theorem advanceRegs (s : MachineState) (r : Reg) (h : r∈pairRegs) :
    (pairNextState s).getReg r = s.getReg r +
      pairStride r := by
  simp only [pairRegs,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> simp [pairStride,pairNextState,pairNextOps,execInstrBr,MachineState.setReg,MachineState.getReg,MachineState.setPC,signExtend12]
end CommitGolfCandidate.Trunc.Batch
