import CommitGolfCandidate.S5CheckMaskFrame
namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Arithmetic in words 217–220, expressed without substituting a particular checker state. -/
private theorem mask_register (s : MachineState) :
    (preparedMask s).getReg .x7 = (1#64 <<< ((s.getReg .x31+signExtend12 3872).toNat%64))+signExtend12 4095 := rfl

theorem setup_mask (s : MachineState) (h : Height) (pc : s.pc=pcAt 217) (w : s.getReg .x31=BitVec.ofNat 64 (wireWidth h)) :
    pathReady s maskSetup ∧ (preparedMask s).pc=pcAt 221 ∧ (preparedMask s).mem=s.mem ∧ (preparedMask s).getReg .x12=s.getReg .x12 ∧
    (preparedMask s).getReg .x7=heldMask h := by
  obtain ⟨ready,next,mem,ptr⟩:=mask_frame s pc
  exact ⟨ready,next,mem,ptr,(mask_register s).trans ((congrArg (fun v : Word=>(1#64 <<< ((v+signExtend12 3872).toNat%64))+signExtend12 4095) w).trans (calc_mask h))⟩
end CommitGolfCandidate.S5Machine.Check
