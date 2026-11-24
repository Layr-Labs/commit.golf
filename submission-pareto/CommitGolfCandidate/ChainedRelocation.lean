import CommitGolfCandidate.ChainedOpeningControllerCode

/-! PC translation for the position-independent ordinary instructions of the chained controller. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def relocatedState (delta : Word) (s : MachineState) : MachineState := s.setPC (s.pc+delta)

@[simp] theorem relocated_pc (delta : Word) (s : MachineState) : (relocatedState delta s).pc=s.pc+delta := rfl
@[simp] theorem relocated_reg (delta : Word) (s : MachineState) (reg : Reg) :
    (relocatedState delta s).getReg reg=s.getReg reg := by cases reg <;> rfl
@[simp] theorem relocated_mem (delta : Word) (s : MachineState) (address : Word) :
    (relocatedState delta s).getMem address=s.getMem address := rfl
@[simp] theorem relocated_byte (delta : Word) (s : MachineState) (address : Word) :
    (relocatedState delta s).getByte address=s.getByte address := rfl
@[simp] theorem relocated_set_reg (delta : Word) (s : MachineState) (reg : Reg) (value : Word) :
    relocatedState delta (s.setReg reg value)=(relocatedState delta s).setReg reg value := by cases reg <;> rfl
@[simp] theorem relocated_set_mem (delta : Word) (s : MachineState) (address value : Word) :
    relocatedState delta (s.setMem address value)=(relocatedState delta s).setMem address value := rfl
@[simp] theorem relocated_set_byte (delta : Word) (s : MachineState) (address : Word) (value : Byte) :
    relocatedState delta (s.setByte address value)=(relocatedState delta s).setByte address value := rfl
@[simp] theorem relocated_set_pc (delta : Word) (s : MachineState) (pc : Word) :
    relocatedState delta (s.setPC pc)=(relocatedState delta s).setPC (pc+delta) := rfl

def relativeInstruction : Instr → Bool
  | .ADD .. | .ADDI .. | .ANDI .. | .LUI .. | .SUB .. | .OR .. | .SLL .. | .SLLI .. | .SRLI ..
  | .LD .. | .LBU .. | .SB .. | .BEQ .. | .BNE .. | .BGEU .. | .BLTU .. | .ECALL => true
  | .JAL reg _ => reg==.x0
  | _ => false

private theorem relocation_add_left_comm (a b c : Word) : a+(b+c)=b+(a+c) := by ac_rfl

theorem ordinary_step_relocated (delta : Word) (s : MachineState) (instruction : Instr)
    (relative : relativeInstruction instruction=true) :
    ordinaryStep (relocatedState delta s) (.base instruction)=
      (ordinaryStep s (.base instruction)).map (relocatedState delta) := by
  cases instruction <;> simp only [relativeInstruction,Bool.false_eq_true] at relative
  all_goals try contradiction
  case JAL rd offset =>
    have zero : rd=.x0 := by cases rd <;> simp_all
    subst rd
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,relocatedState,
      MachineState.setReg,MachineState.setPC,BitVec.add_assoc,relocation_add_left_comm,BitVec.add_comm]
  all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,relocated_reg,Option.map_none,
    execInstrBr,relocated_mem,relocated_byte,relocated_pc,Option.map_some,relocated_set_pc,
    relocated_set_reg,relocated_set_byte]
  all_goals (repeat split) <;>
    simp_all only [Bool.false_eq_true,ite_true,ite_false,Option.map_none,Option.map_some,relocated_set_pc,relocated_set_reg,
      relocated_set_byte,relocated_set_mem,relocated_reg,relocated_mem,relocated_byte,relocated_pc,
      BitVec.add_assoc,relocation_add_left_comm,BitVec.add_comm]

private theorem opening_controller_all_relative : openingControllerOps.all relativeInstruction=true := by
  decide +kernel

theorem opening_controller_relative (i : Fin 2248) :
    relativeInstruction (openingControllerOps.getD i.val .EBREAK)=true := by
  have inside : i.val<openingControllerOps.length := by
    rw [opening_controller_ops_length]
    exact i.isLt
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some]
  exact List.all_eq_true.mp opening_controller_all_relative _ (List.getElem_mem inside)

end CommitGolfCandidate.Chained.Native
