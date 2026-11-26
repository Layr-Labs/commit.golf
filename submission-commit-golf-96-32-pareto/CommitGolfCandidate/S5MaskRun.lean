import CommitGolfCandidate.S5MaskCore
import CommitGolfCandidate.S5ChainCommon
import CommitGolfCandidate.S5MaskStep
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000

theorem mask_regs (s : MachineState) : Keeps s (maskOut s) := by
  intro r a b c d
  change (maskAnd s).getReg r=s.getReg r
  simp only [maskAnd,maskLoad,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ d.symm]

theorem mask_run (o : Oracle) (d : Height) (lane : Lane) (cut : chained d) (s : MachineState) (dst : Nat)
    (pc : s.pc=pcAt (maskPC d lane)) (dest : s.getReg .x12=BitVec.ofNat 64 dst)
    (fit : dst+32≤MEMORY_BYTES) (al : dst%8=0) : Runs .commit true o s (maskOut s) 3 3 0 := by
  obtain ⟨small,lhu,and_,sw⟩:=mask_sites d cut lane
  exact mask_core_run o s _ dst pc dest fit al (decoded_site (by omega) lhu) (decoded_site (by omega) and_) (decoded_site small sw)
end CommitGolfCandidate.S5Machine
