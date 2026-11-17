import CommitGolfCandidate.CapCheckLowerRecord

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem cap_check_lower_record_steps_bound (state : MachineState) :
    capCheckLowerRecordSteps state ≤ 646 := by
  have path := cap_check_path_loop_steps_bound (state.getMem (state.getReg .x24)) 16
  unfold capCheckLowerRecordSteps
  omega

theorem cap_check_lower_record_cycles_bound (state : MachineState) :
    capCheckPathLoopSteps (state.getMem (state.getReg .x24)) 16+321 ≤ 821 := by
  have path := cap_check_path_loop_steps_bound (state.getMem (state.getReg .x24)) 16
  omega

end CommitGolfCandidate
