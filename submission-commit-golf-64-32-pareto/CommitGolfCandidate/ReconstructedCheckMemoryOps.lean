import CommitGolfCandidate.ReconstructedCheckBranch

namespace CommitGolfCandidate.Reconstruction.CheckMemoryOps
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding.Machine CheckRecorded CommitBlocks
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

def word (pc : Nat) (ins : Instruction) := decide (pc<796) && CheckDecode.same (CheckStraight.actualAt pc) ins

theorem parsed {n : Nat} {ins : Instruction} (ok : word n ins=true) (s : MachineState) (pc : s.pc=addr n) : fetch image s=some ins := by
  simp only [word,Bool.and_eq_true] at ok
  obtain ⟨inside,h⟩:=ok
  exact CheckStraight.present n _ (of_decide_eq_true inside) (CheckDecode.same_sound h) s pc

theorem loadB (o : Oracle) (s : MachineState) (n : Nat) (rd rs : Reg) (a : Word)
    (op : word n (.base (.LBU rd rs 0))=true) (pc : s.pc=addr n) (reg : s.getReg rs=a) (valid : accessValid a 1=true) :
    Segment o 1 s ((s.setReg rd ((s.getByte a).zeroExtend 64)).setPC (addr (n+1))) [] := by
  apply plain _ _ _ _ (parsed op s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,reg,show signExtend12 0=0#64 by decide,BitVec.add_zero,valid,
    ite_true,execInstrBr,pc,addr_next]

theorem loadU32 (o : Oracle) (s : MachineState) (n : Nat) (rd rs : Reg) (a : Word)
    (op : word n (.base (.LWU rd rs 0))=true) (pc : s.pc=addr n) (reg : s.getReg rs=a) (valid : accessValid a 4=true) :
    Segment o 1 s ((s.setReg rd ((s.getWord32 a).zeroExtend 64)).setPC (addr (n+1))) [] := by
  apply plain _ _ _ _ (parsed op s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,reg,show signExtend12 0=0#64 by decide,BitVec.add_zero,valid,
    ite_true,execInstrBr,pc,addr_next]

theorem storeB (o : Oracle) (s : MachineState) (n : Nat) (rs rt : Reg) (a : Word) (x : BitVec 8)
    (op : word n (.base (.SB rs rt 0))=true) (pc : s.pc=addr n) (reg : s.getReg rs=a) (value : (s.getReg rt).truncate 8=x)
    (valid : accessValid a 1=true) : Segment o 1 s ((s.setByte a x).setPC (addr (n+1))) [] := by
  apply plain _ _ _ _ (parsed op s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,reg,show signExtend12 0=0#64 by decide,BitVec.add_zero,valid,
    ite_true,execInstrBr,pc,addr_next,value]

theorem store32 (o : Oracle) (s : MachineState) (n : Nat) (rs rt : Reg) (a : Word) (x : BitVec 32)
    (op : word n (.base (.SW rs rt 0))=true) (pc : s.pc=addr n) (reg : s.getReg rs=a) (value : (s.getReg rt).truncate 32=x)
    (valid : accessValid a 4=true) : Segment o 1 s ((s.setWord32 a x).setPC (addr (n+1))) [] := by
  apply plain _ _ _ _ (parsed op s pc)
  simp only [ordinaryStep,memoryArgumentsValid,memAccess,reg,show signExtend12 0=0#64 by decide,BitVec.add_zero,valid,
    ite_true,execInstrBr,pc,addr_next,value]

end CommitGolfCandidate.Reconstruction.CheckMemoryOps
