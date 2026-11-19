import CommitGolfCandidate.QuadCommitQuad3Run
import CommitGolfCandidate.QuadCommitSetup

namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
attribute [local irreducible] image leafCode quadCode quad2Code quad3Code parentCode decodeInstruction execute writeBits

def quadSetupOps : List Instr :=
  [.LUI .x10 65537,.ADDI .x10 .x10 4024,.ADD .x10 .x9 .x10,
   .LUI .x12 507908,.ADDI .x12 .x12 0,.ADD .x12 .x9 .x12,
   .LUI .x21 94208,.ADDI .x21 .x21 0,.ADD .x21 .x12 .x21]
def quad2SetupOps : List Instr :=
  [.LUI .x10 507908,.ADDI .x10 .x10 4024,.ADD .x10 .x9 .x10,
   .LUI .x12 8193,.ADDI .x12 .x12 0,.ADD .x12 .x9 .x12,
   .LUI .x21 23552,.ADDI .x21 .x21 0,.ADD .x21 .x12 .x21]
def quad3SetupOps : List Instr :=
  [.LUI .x10 8193,.ADDI .x10 .x10 4024,.ADD .x10 .x9 .x10,
   .LUI .x12 2048,.ADDI .x12 .x12 0,.ADD .x12 .x9 .x12,
   .LUI .x21 4096,.ADDI .x21 .x21 0,.ADD .x21 .x9 .x21]
def parentSetupOps : List Instr :=
  [.ADDI .x11 .x0 64,.ADDI .x13 .x0 0,.LUI .x10 4096,.ADDI .x10 .x10 4032,.ADD .x10 .x9 .x10,
   .LUI .x12 2048,.ADDI .x12 .x12 4064,.ADD .x12 .x9 .x12,.ADDI .x21 .x9 0]
def quadSetup (s : MachineState) (i : Nat) := (quadSetupOps.take i).foldl execInstrBr s
def quad2Setup (s : MachineState) (i : Nat) := (quad2SetupOps.take i).foldl execInstrBr s
def quad3Setup (s : MachineState) (i : Nat) := (quad3SetupOps.take i).foldl execInstrBr s
def parentSetup (s : MachineState) (i : Nat) := (parentSetupOps.take i).foldl execInstrBr s

def quadSetupHead := leafLatchPrefix++leafLatchWords
def quad2SetupHead := quadPrefix++quadCode++quadLatchWords
def quad3SetupHead := quad2Prefix++quad2Code++quadLatchWords
def parentSetupHead := quad3Prefix++quad3Code++quadLatchWords

theorem quad_setup_head_length : quadSetupHead.length=45203 := by
  rw [quadSetupHead,List.length_append,leaf_latch_prefix_length];rfl

theorem quad2_setup_head_length : quad2SetupHead.length=94366 := by
  rw [quad2SetupHead,List.length_append,List.length_append,quad_prefix_length,quad_code_length];rfl

theorem quad3_setup_head_length : quad3SetupHead.length=143529 := by
  rw [quad3SetupHead,List.length_append,List.length_append,quad2_prefix_length,quad2_code_length];rfl

theorem parent_setup_head_length : parentSetupHead.length=192692 := by
  rw [parentSetupHead,List.length_append,List.length_append,quad3_prefix_length,quad3_code_length];rfl

private theorem quad_setup_decoded (i : Fin 9) :
    (quadSetupWords[i.val]?).bind decodeInstruction=some (.base ((quadSetupOps[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_quad_setup (i : Fin 9) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (184908+4*i.val)) :
    fetch image s=some (.base ((quadSetupOps[i.val]?).getD .EBREAK)) := by
  apply fetch_code_index s (45203+i.val) (by have := i.isLt;omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at quadSetupHead quadSetupWords
    (quadCode++quadLatchWords++quad2SetupWords++quad2Code++quadLatchWords++quad3SetupWords++quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image quadSetupHead leafLatchPrefix;simp only [List.append_assoc]) i.val i.isLt
  rw [quad_setup_head_length] at atIndex
  rw [atIndex];exact quad_setup_decoded i

theorem execute_quad_setup (s : MachineState) (pc : s.pc=184908) (fuel : Nat) :
    execute image (9+fuel) s true =
      (do let out ← execute image fuel (quadSetup s 9) true
          return out.charge 9 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := quadSetup s)
  intro i inside
  refine ⟨.base ((quadSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (quadSetup s i).pc=BitVec.ofNat 64 (184908+4*i) := by
      interval_cases i <;> simp only [quadSetup,quadSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    exact fetch_quad_setup ⟨i,inside⟩ _ here
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem quad2_setup_decoded (i : Fin 9) :
    (quad2SetupWords[i.val]?).bind decodeInstruction=some (.base ((quad2SetupOps[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_quad2_setup (i : Fin 9) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (381560+4*i.val)) :
    fetch image s=some (.base ((quad2SetupOps[i.val]?).getD .EBREAK)) := by
  apply fetch_code_index s (94366+i.val) (by have := i.isLt;omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at quad2SetupHead quad2SetupWords
    (quad2Code++quadLatchWords++quad3SetupWords++quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image quad2SetupHead quadPrefix;simp only [List.append_assoc]) i.val i.isLt
  rw [quad2_setup_head_length] at atIndex
  rw [atIndex];exact quad2_setup_decoded i

theorem execute_quad2_setup (s : MachineState) (pc : s.pc=381560) (fuel : Nat) :
    execute image (9+fuel) s true =
      (do let out ← execute image fuel (quad2Setup s 9) true
          return out.charge 9 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := quad2Setup s)
  intro i inside
  refine ⟨.base ((quad2SetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (quad2Setup s i).pc=BitVec.ofNat 64 (381560+4*i) := by
      interval_cases i <;> simp only [quad2Setup,quad2SetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    exact fetch_quad2_setup ⟨i,inside⟩ _ here
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem quad3_setup_decoded (i : Fin 9) :
    (quad3SetupWords[i.val]?).bind decodeInstruction=some (.base ((quad3SetupOps[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_quad3_setup (i : Fin 9) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (578212+4*i.val)) :
    fetch image s=some (.base ((quad3SetupOps[i.val]?).getD .EBREAK)) := by
  apply fetch_code_index s (143529+i.val) (by have := i.isLt;omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at quad3SetupHead quad3SetupWords
    (quad3Code++quadLatchWords++parentSetupWords++parentCode++parentLatchWords++rootWords)
    (by unfold image quad3SetupHead quad2Prefix quadPrefix;simp only [List.append_assoc]) i.val i.isLt
  rw [quad3_setup_head_length] at atIndex
  rw [atIndex];exact quad3_setup_decoded i

theorem execute_quad3_setup (s : MachineState) (pc : s.pc=578212) (fuel : Nat) :
    execute image (9+fuel) s true =
      (do let out ← execute image fuel (quad3Setup s 9) true
          return out.charge 9 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := quad3Setup s)
  intro i inside
  refine ⟨.base ((quad3SetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (quad3Setup s i).pc=BitVec.ofNat 64 (578212+4*i) := by
      interval_cases i <;> simp only [quad3Setup,quad3SetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    exact fetch_quad3_setup ⟨i,inside⟩ _ here
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem parent_setup_decoded (i : Fin 9) :
    (parentSetupWords[i.val]?).bind decodeInstruction=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  revert i;decide +kernel

theorem fetch_parent_setup (i : Fin 9) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (774864+4*i.val)) :
    fetch image s=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  apply fetch_code_index s (192692+i.val) (by have := i.isLt;omega) (by rw [pc];congr 1 <;> omega)
  have atIndex := code_segment_at parentSetupHead parentSetupWords
    (parentCode++parentLatchWords++rootWords)
    (by unfold image parentSetupHead quad3Prefix quad2Prefix quadPrefix;simp only [List.append_assoc]) i.val i.isLt
  rw [parent_setup_head_length] at atIndex
  rw [atIndex];exact parent_setup_decoded i

theorem execute_parent_setup (s : MachineState) (pc : s.pc=774864) (fuel : Nat) :
    execute image (9+fuel) s true =
      (do let out ← execute image fuel (parentSetup s 9) true
          return out.charge 9 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := parentSetup s)
  intro i inside
  refine ⟨.base ((parentSetupOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have here : (parentSetup s i).pc=BitVec.ofNat 64 (774864+4*i) := by
      interval_cases i <;> simp only [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    exact fetch_parent_setup ⟨i,inside⟩ _ here
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem quad_setup_regs (s : MachineState) (heap : s.getReg .x9=4294971424)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (kind : s.getReg .x13=1) :
    Quads.Regs (quadSetup s 9) 0 ∧ (quadSetup s 9).getReg .x21=wordAddress (quadSlotWord (2^22)) := by
  refine ⟨⟨?_,?_,selector,size,kind⟩,?_⟩
  all_goals dsimp [quadSetup,quadSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
    MachineState.setReg,MachineState.getReg]
  all_goals simp only [show s.regs .x9=4294971424 from heap]
  all_goals rfl

theorem quad_setup_pc (s : MachineState) (pc : s.pc=184908) : (quadSetup s 9).pc=quadPC 0 0 := by
  change s.pc+4+4+4+4+4+4+4+4+4=_;rw [pc];rfl

theorem quad2_setup_regs (s : MachineState) (heap : s.getReg .x9=4294971424)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (kind : s.getReg .x13=1) :
    Quad2s.Regs (quad2Setup s 9) 0 ∧ (quad2Setup s 9).getReg .x21=wordAddress (quad3SlotWord (2^20)) := by
  refine ⟨⟨?_,?_,selector,size,kind⟩,?_⟩
  all_goals dsimp [quad2Setup,quad2SetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
    MachineState.setReg,MachineState.getReg]
  all_goals simp only [show s.regs .x9=4294971424 from heap]
  all_goals rfl

theorem quad2_setup_pc (s : MachineState) (pc : s.pc=381560) : (quad2Setup s 9).pc=quad2PC 0 0 := by
  change s.pc+4+4+4+4+4+4+4+4+4=_;rw [pc];rfl

theorem quad3_setup_regs (s : MachineState) (heap : s.getReg .x9=4294971424)
    (selector : s.getReg .x5=0) (size : s.getReg .x11=200) (kind : s.getReg .x13=1) :
    Quad3s.Regs (quad3Setup s 9) 0 ∧ (quad3Setup s 9).getReg .x21=wordAddress (heapWord (2^19)) := by
  refine ⟨⟨?_,?_,selector,size,kind⟩,?_⟩
  all_goals dsimp [quad3Setup,quad3SetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
    MachineState.setReg,MachineState.getReg]
  all_goals simp only [show s.regs .x9=4294971424 from heap]
  all_goals rfl

theorem quad3_setup_pc (s : MachineState) (pc : s.pc=578212) : (quad3Setup s 9).pc=quad3PC 0 0 := by
  change s.pc+4+4+4+4+4+4+4+4+4=_;rw [pc];rfl

theorem parent_setup_regs (s : MachineState) (heap : s.getReg .x9=4294971424)
    (selector : s.getReg .x5=0) :
    ParentRegs (parentSetup s 9) (2^18-1) ∧ (parentSetup s 9).getReg .x21=(parentSetup s 9).getReg .x9 := by
  refine ⟨⟨?_,?_,selector,rfl,rfl,heap⟩,?_⟩
  · dsimp [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
      MachineState.setReg,MachineState.getReg]
    simp only [show s.regs .x9=4294971424 from heap]
    rfl
  · dsimp [parentSetup,parentSetupOps,List.take,List.foldl,execInstrBr,MachineState.setPC,
      MachineState.setReg,MachineState.getReg]
    simp only [show s.regs .x9=4294971424 from heap]
    rfl
  · change s.getReg .x9+signExtend12 0=s.getReg .x9
    rw [show signExtend12 0=0#64 by rfl]
    exact BitVec.add_zero _

theorem parent_setup_pc (s : MachineState) (pc : s.pc=774864) : (parentSetup s 9).pc=774900 := by
  change s.pc+4+4+4+4+4+4+4+4+4=_;rw [pc];rfl

end TwoPermutationPrototype.Quad.Commit
