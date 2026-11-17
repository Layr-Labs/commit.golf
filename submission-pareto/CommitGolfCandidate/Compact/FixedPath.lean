import CommitGolfCandidate.Compact.SlimPath
/-! A path step with a fixed output base and immediate store offsets. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000

def fixedPathInstructions (level : Nat) : List Instr :=
  [.XORI .x7 .x20 1,.SLLI .x7 .x7 5,.ADD .x23 .x9 .x7,
   .LD .x6 .x23 0,.SD .x25 .x6 (BitVec.ofNat 12 (32*level)),
   .LD .x6 .x23 8,.SD .x25 .x6 (BitVec.ofNat 12 (32*level+8)),
   .LD .x6 .x23 16,.SD .x25 .x6 (BitVec.ofNat 12 (32*level+16)),
   .LD .x6 .x23 24,.SD .x25 .x6 (BitVec.ofNat 12 (32*level+24)),
   .SRLI .x20 .x20 1]

def fixedPathPrefix (s : MachineState) (level count : Nat) : MachineState :=
  ((fixedPathInstructions level).take count).foldl execInstrBr s

private theorem reg_mem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

@[simp] private theorem pc_set (s : MachineState) (p : Word) : (s.setPC p).pc=p := rfl
@[simp] private theorem pc_overwrite (s : MachineState) (a b : Word) :
    (s.setPC a).setPC b=s.setPC b := rfl
@[simp] private theorem cursor_mem (s : MachineState) (c a v : Word) :
    (s.setReg .x25 c).setMem a v=(s.setMem a v).setReg .x25 c := rfl
@[simp] private theorem cursor_pc (s : MachineState) (c p : Word) :
    (s.setReg .x25 c).setPC p=(s.setPC p).setReg .x25 c := rfl
@[simp] private theorem cursor_overwrite (s : MachineState) (a b : Word) :
    (s.setReg .x25 a).setReg .x25 b=s.setReg .x25 b := by
  cases s
  simp [MachineState.setReg]
  funext r
  cases r <;> rfl
@[simp] private theorem cursor_write (s : MachineState) (r : Reg) (c v : Word) (different : r≠.x25) :
    (s.setReg .x25 c).setReg r v=(s.setReg r v).setReg .x25 c := by
  cases r <;> simp_all [MachineState.setReg]
  all_goals funext reg; cases reg <;> rfl

private theorem fixed_immediate (level word : Nat) (bound : level<24) (inside : word<4) :
    signExtend12 (BitVec.ofNat 12 (32*level+8*word))=
      BitVec.ofNat 64 (32*level)+BitVec.ofNat 64 (8*word) := by
  interval_cases level <;> interval_cases word <;> rfl

/-- Immediate stores write exactly where the reference's moving cursor writes. -/
theorem fixed_path_same (s : MachineState) (level : Nat) (bound : level<24) :
    fixedPathPrefix s level 12=
      (((slimPathPrefix (s.setReg .x25 (s.getReg .x25+BitVec.ofNat 64 (32*level))) 13).setReg .x25 (s.getReg .x25)).setPC (s.pc+48)) := by
  have o0 := fixed_immediate level 0 bound (by decide)
  have o1 := fixed_immediate level 1 bound (by decide)
  have o2 := fixed_immediate level 2 bound (by decide)
  have o3 := fixed_immediate level 3 bound (by decide)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at o0 o1 o2 o3
  simp only [fixedPathPrefix,fixedPathInstructions,slimPathPrefix,slimPathInstructions,
    List.take,List.foldl,execInstrBr]
  simp only [o0,o1,o2,o3]
  simp [signExtend12,MachineState.getReg_setPC,reg_mem,
    MachineState.getReg_setReg_ne,MachineState.getReg_setReg_eq,BitVec.add_assoc]
  all_goals
    cases s
    simp [MachineState.setReg,MachineState.getReg,MachineState.setPC,
      MachineState.setMem,MachineState.getMem,BitVec.add_assoc]
    all_goals first | rfl | (funext reg; cases reg <;> rfl)
end CommitGolfCandidate.Compact
