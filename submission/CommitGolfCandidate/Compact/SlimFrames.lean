import CommitGolfCandidate.Compact.FastOpeningFrames
import CommitGolfCandidate.Compact.SlimPath
/-! Register and PC frames for path steps, counter iteration, and the checked final adjustment. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem path_counter_frame (s : MachineState) (c d pc : Word) :
    ((openingPathState (s.setReg .x28 c)).setReg .x28 d).setPC pc =
      ((openingPathState s).setReg .x28 d).setPC pc := by
  have prepared (s : MachineState) : openingPathPreparedState s =
      ([.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7] : List Instr).foldl execInstrBr s := rfl
  simp [openingPathState,openingLatchState,openingPathAdvancedState,
    opening_copy_expansion,prepared,execInstrBr,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,
    MachineState.setMem,MachineState.getMem,BitVec.add_assoc,signExtend12]
  funext reg
  cases reg <;> rfl

theorem path_counter_iterate (n : Nat) (s : MachineState) :
    (openingPathState^[n] s).getReg .x28=s.getReg .x28-BitVec.ofNat 64 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',(opening_path_registers _).2.2.1,ih,
      BitVec.sub_sub,BitVec.ofNat_add]
    rfl

theorem state_set_own_register (s : MachineState) (r : Reg) :
    s.setReg r (s.getReg r)=s := by
  cases s
  cases r <;> simp [MachineState.setReg,MachineState.getReg] <;>
    funext reg <;> cases reg <;> rfl

theorem counter_write_frame (s : MachineState) (a b pc next : Word) :
    (((s.setReg .x28 a).setPC pc).setReg .x28 b).setPC next=
      (s.setReg .x28 b).setPC next := by
  cases s
  simp [MachineState.setReg,MachineState.setPC]
  funext reg
  cases reg <;> rfl

theorem counter_cleanup_step (s : MachineState) (c : Word)
    (h : s.getReg .x28=c-24) :
    ordinaryStep ((s.setReg .x28 c).setPC 5496) (.base (.ADDI .x28 .x28 4072))=
      some (s.setPC 5500) := by
  change some (((((s.setReg .x28 c).setPC 5496).setReg .x28
    (c+signExtend12 4072))).setPC 5500)=_
  have sub : c+signExtend12 4072=c-24 := by simp [signExtend12,BitVec.sub_eq_add_neg]
  rw [sub,←h,counter_write_frame,state_set_own_register]

end CommitGolfCandidate.Compact
