import CommitGolfCandidate.S5WriterCode
namespace CommitGolfCandidate.S5Machine.Writer
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def storePrefix : PathCode := [(32,.SD .x19 .x23 0),(33,.ADDI .x19 .x19 8),(34,.ADDI .x24 .x24 4032)]
def atTest (s : MachineState) := pathEnd s storePrefix
def afterTest (s : MachineState) := execInstrBr s (.BEQ .x24 .x0 16)
def shiftTail : Bool → PathCode
  | true=>[(39,.ADDI .x23 .x0 0),(40,.JAL .x0 2097076)]
  | false=>[(36,.SUB .x30 .x31 .x24),(37,.SRL .x23 .x28 .x30),(38,.JAL .x0 2097084)]

theorem prefix_ready (s : MachineState) (pc : s.pc=pcAt 32) (valid : accessValid (s.getReg .x19) 8=true) :
    pathReady s storePrefix ∧ (atTest s).pc=pcAt 35 := by
  change accessValid (s.regs .x19) 8=true at valid
  simp +decide [storePrefix,atTest,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg,MachineState.setReg,MachineState.setPC,MachineState.setMem,pcAt,pc,signExtend12,valid]

theorem prefix_ptr (s : MachineState) : (atTest s).getReg .x19=s.getReg .x19+8 := rfl
theorem prefix_count (s : MachineState) : (atTest s).getReg .x24=s.getReg .x24+signExtend12 4032 := rfl
theorem prefix_word (s : MachineState) : (atTest s).getReg .x28=s.getReg .x28 := rfl
theorem prefix_width (s : MachineState) : (atTest s).getReg .x31=s.getReg .x31 := rfl
theorem prefix_mem (s : MachineState) : (atTest s).mem=(s.setMem (s.getReg .x19) (s.getReg .x23)).mem := by
  change (s.setMem (s.getReg .x19+0#64) _).mem=_;rw [BitVec.add_zero]

theorem tested (s : MachineState) (pc : s.pc=pcAt 35) (b : Bool) (fit : (s.getReg .x24==0)=b) :
    afterTest s=s.setPC (pcAt (if b then 39 else 36)) := by
  change (if s.getReg .x24==0 then _ else _)=_
  rw [fit,pc];cases b <;> rfl

def tailEnd (b : Bool) (s : MachineState) := pathEnd s (shiftTail b)
theorem tail_state (b : Bool) (s : MachineState) (pc : s.pc=pcAt (if b then 39 else 36)) :
    pathReady s (shiftTail b) ∧
    (tailEnd b s).pc=pcAt 21 ∧ (tailEnd b s).getReg .x19=s.getReg .x19 ∧ (tailEnd b s).getReg .x24=s.getReg .x24 ∧
    (tailEnd b s).getReg .x23=(if b then 0 else s.getReg .x28 >>> ((s.getReg .x31-s.getReg .x24).toNat%64)) ∧
    (tailEnd b s).mem=s.mem := by
  cases b <;> simp +decide [shiftTail,tailEnd,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg,MachineState.setReg,MachineState.setPC,pcAt,pc,signExtend12,signExtend21]
end CommitGolfCandidate.S5Machine.Writer
