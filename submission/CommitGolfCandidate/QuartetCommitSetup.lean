import CommitGolfCandidate.QuartetCommitQStep
import CommitGolfCandidate.TwoPermutationPackedParents
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
attribute [local irreducible] execute image writeBits

def prePrefix (s : MachineState) (i : Nat) := (setupOps.take i).foldl execInstrBr s
theorem pre_run (s : MachineState) (pc : s.pc=wordPC 0) (fuel : Nat) :
    execute image (15+fuel) s true = (do
      let e ← execute image fuel (prePrefix s 15) true; return e.charge 15 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := prePrefix s)
  intro i hi
  refine ⟨.base ((setupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (prePrefix s i).pc=wordPC (0+i) := by
      interval_cases i <;> simp only [prePrefix,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_setup (prePrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def postPrefix (s : MachineState) (i : Nat) := ((setupOps.drop 16).take i).foldl execInstrBr s
theorem post_run (s : MachineState) (pc : s.pc=wordPC 16) (fuel : Nat) :
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (postPrefix s 6) true; return e.charge 6 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := postPrefix s)
  intro i hi
  refine ⟨.base (((setupOps.drop 16)[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (postPrefix s i).pc=wordPC (16+i) := by
      interval_cases i <;> simp only [postPrefix,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_setup (postPrefix s i) ⟨16+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def qStartPrefix (s : MachineState) (i : Nat) := (quadSetupOps.take i).foldl execInstrBr s
theorem qStart_run (s : MachineState) (pc : s.pc=wordPC 45224) (fuel : Nat) :
    execute image (3+fuel) s true = (do
      let e ← execute image fuel (qStartPrefix s 3) true; return e.charge 3 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := qStartPrefix s)
  intro i hi
  refine ⟨.base ((quadSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (qStartPrefix s i).pc=wordPC (45224+i) := by
      interval_cases i <;> simp only [qStartPrefix,quadSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_quadSetup (qStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

def upStartPrefix (s : MachineState) (i : Nat) := (upperSetupOps.take i).foldl execInstrBr s
theorem upStart_run (s : MachineState) (pc : s.pc=wordPC 46765) (fuel : Nat) :
    execute image (6+fuel) s true = (do
      let e ← execute image fuel (upStartPrefix s 6) true; return e.charge 6 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := upStartPrefix s)
  intro i hi
  refine ⟨.base ((upperSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (upStartPrefix s i).pc=wordPC (46765+i) := by
      interval_cases i <;> simp only [upStartPrefix,upperSetupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    have cell := fetch_upperSetup (upStartPrefix s i) ⟨0+i,by omega⟩ (by simpa only [Nat.zero_add,Nat.add_assoc] using here)
    interval_cases i <;> exact cell
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure SeedRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 15
  selector : s.getReg .x5=2
  target : s.getReg .x10=BitVec.ofNat 64 (8*qSalt 0)
  size : s.getReg .x11=24
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  salt : s.getReg .x22=wordAddress (qSalt 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  bigStride : s.getReg .x23=4096
  bias : s.getReg .x7=2048

private def seedChunk (block : Nat) (s : MachineState) := ((setupOps.drop (5*block)).take 5).foldl execInstrBr s

private structure Seed1 (s : MachineState) : Prop where
  pc : s.pc=wordPC 5
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)

private theorem seedBlock1 (s : MachineState) (h : CommitEntry s) : Seed1 (seedChunk 0 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x10=4096 from h.message,
    show s.regs .x11=4294971392 from h.commitment,
    show s.regs .x12=4294971424 from h.heap]
  all_goals rfl

private structure Seed2 (s : MachineState) : Prop where
  pc : s.pc=wordPC 10
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  message : s.getReg .x18=4096
  stride : s.getReg .x19=536870912
  quartet : s.getReg .x21=wordAddress (qSource 0)
  salt : s.getReg .x22=wordAddress (qSalt 0)
  sentinel : s.getReg .x24=wordAddress (qSource 4194304)
  bigStride : s.getReg .x23=4096
  temp : s.getReg .x7=4096

private theorem seedBlock2 (s : MachineState) (h : Seed1 s) : Seed2 (seedChunk 1 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet]
  all_goals rfl

private theorem seedBlock3 (s : MachineState) (h : Seed2 s) : SeedRegs (seedChunk 2 s) := by
  constructor <;> dsimp [seedChunk,setupOps,List.drop,List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [h.pc,show s.regs .x8=4294971392 from h.output,
    show s.regs .x9=4294971424 from h.heap,
    show s.regs .x18=4096 from h.message,
    show s.regs .x19=536870912 from h.stride,
    show s.regs .x21=wordAddress (qSource 0) from h.quartet,
    show s.regs .x22=wordAddress (qSalt 0) from h.salt,
    show s.regs .x24=wordAddress (qSource 4194304) from h.sentinel,
    show s.regs .x23=4096 from h.bigStride,
    show s.regs .x7=4096 from h.temp]
  all_goals rfl

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegs (prePrefix s 15) :=
  seedBlock3 _ (seedBlock2 _ (seedBlock1 s entry))

structure StartLeafRegs (s : MachineState) : Prop where
  pc : s.pc=wordPC 22
  source : s.getReg .x10=4096
  cursor : s.getReg .x20=wordAddress (qSource 0)+2048
  salt : s.getReg .x22=wordAddress (qSalt 0)+2048
  bigStride : s.getReg .x23=4096
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  sentinel : s.getReg .x25=wordAddress (qSource 4194304)+2048
  quartet : s.getReg .x21=wordAddress (qSource 0)
  stop : s.getReg .x24=wordAddress (qSource 4194304)
  output : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  stride : s.getReg .x19=536870912

end TwoPermutationPrototype.QuartetCommit
