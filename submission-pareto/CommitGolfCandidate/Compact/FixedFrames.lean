import CommitGolfCandidate.Compact.FixedPath
import CommitGolfCandidate.Compact.SlimFrames
/-! Fixed-output and counter frames relate the new physical path to the reference. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def fixedFrame (s : MachineState) (base counter pc : Word) : MachineState :=
  ((s.setReg .x25 base).setReg .x28 counter).setPC pc

theorem fixed_frame_virtual (s : MachineState) (base counter pc offset : Word)
    (cursor : s.getReg .x25=base+offset) :
    (fixedFrame s base counter pc).setReg .x25
      ((fixedFrame s base counter pc).getReg .x25+offset)=
      (s.setReg .x28 counter).setPC pc := by
  have clean : (fixedFrame s base counter pc).setReg .x25 (base+offset)=
      ((s.setReg .x25 (base+offset)).setReg .x28 counter).setPC pc := by
    cases s
    simp [fixedFrame,MachineState.setReg,MachineState.setPC]
    funext reg
    cases reg <;> rfl
  have output : (fixedFrame s base counter pc).getReg .x25=base := by
    simp [fixedFrame,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  rw [output,clean,←cursor,state_set_own_register]

theorem fixed_frame_rewrite (s : MachineState) (base counter pc next : Word) :
    ((((s.setReg .x28 counter).setPC pc).setReg .x25 base).setPC next)=
      fixedFrame s base counter next := by
  cases s
  simp [fixedFrame,MachineState.setReg,MachineState.setPC]
  funext reg
  cases reg <;> rfl

/-- A physical fixed-cursor step returns the same reference state and memory. -/
theorem fixed_path_refine (s : MachineState) (level : Nat) (bound : level<24)
    (base counter pc : Word) (cursor : s.getReg .x25=base+BitVec.ofNat 64 (32*level)) :
    fixedPathPrefix (fixedFrame s base counter pc) level 12=
      fixedFrame (openingPathState s) base counter (pc+48) := by
  rw [fixed_path_same _ level bound,fixed_frame_virtual _ _ _ _ _ cursor,slim_path_same]
  rw [path_frame_erasure]
  simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x28≠.x0)]
  rw [path_counter_frame]
  change ((((openingPathState s).setReg .x28 counter).setPC _).setReg .x25 _).setPC _=_
  have output : (fixedFrame s base counter pc).getReg .x25=base := by
    simp [fixedFrame,MachineState.getReg,MachineState.setReg,MachineState.setPC]
  have physicalPC : (fixedFrame s base counter pc).pc=pc := rfl
  rw [output,physicalPC,fixed_frame_rewrite]
end CommitGolfCandidate.Compact
