import CommitGolfCandidate.QuadCheckerSteps
import CommitGolfCandidate.QuadCopy
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest

/-! The actual appended quad block, retaining the baseline PCs. Prefix writes
72 zero bytes and the opened digest; the loop consumes exactly three rotated siblings. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
@[local simp] private theorem quad_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem quad_set_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

/-- Initial 22 words of the appended block, including the known-child copy. -/
def quadPrefixCode : List Instr :=
  [.ADDI .x10 .x24 256,
   .SD .x10 .x0 0,.SD .x10 .x0 8,.SD .x10 .x0 16,.SD .x10 .x0 24,
   .SD .x10 .x0 32,.SD .x10 .x0 40,.SD .x10 .x0 48,.SD .x10 .x0 56,.SD .x10 .x0 64,
   .ANDI .x29 .x6 3,.SLLI .x29 .x29 5,.ADD .x28 .x10 .x29,
   .LD .x31 .x23 0,.SD .x28 .x31 72,.LD .x31 .x23 8,.SD .x28 .x31 80,
   .LD .x31 .x23 16,.SD .x28 .x31 88,.LD .x31 .x23 24,.SD .x28 .x31 96,
   .ADDI .x30 .x0 3]

def quadPrefix (s : MachineState) (n : Nat) : MachineState :=
  (quadPrefixCode.take n).foldl execInstrBr s

theorem quad_entry_hop (s : MachineState) (pc : s.pc=4336) :
    GroupHop s (s.setPC 5564) 1 := by
  intro fuel
  have fetched := fetch_at s 60 (.JAL .x0 1228) (by decide) pc rfl
  have step : ordinaryStep s (.base (.JAL .x0 1228))=some (s.setPC 5564) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,signExtend21]
    rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem quad_prefix_hop (s : MachineState) (slot : Fin 4)
    (pc : s.pc=5564) (pair : s.getReg .x24=12544) (digest : s.getReg .x23=12288)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) :
    GroupHop s (quadPrefix s 22) 22 := by
  intro fuel
  apply execute_unit_steps (states := quadPrefix s)
  intro i bounded
  refine ⟨.base (quadPrefixCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (367+i) _ (by omega)
    · interval_cases i <;> simp [quadPrefix,quadPrefixCode,execInstrBr,pc]
    · interval_cases i <;> rfl
  · fin_cases slot <;> interval_cases i <;>
      simp [ordinaryStep,memoryArgumentsValid,memAccess,quadPrefix,quadPrefixCode,
        execInstrBr,signExtend12,pair,digest,opened,accessValid,rangeValid,MEMORY_BYTES]
  · interval_cases i <;> rfl

theorem quad_prefix_register (s : MachineState) (r : Reg)
    (a : r≠.x10) (b : r≠.x28) (c : r≠.x29) (d : r≠.x30) (e : r≠.x31) :
    (quadPrefix s 22).getReg r=s.getReg r := by
  simp [quadPrefix,quadPrefixCode,execInstrBr,Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e]

theorem quad_prefix_post (s : MachineState) (slot : Fin 4)
    (pc : s.pc=5564) (pair : s.getReg .x24=12544)
    (opened : s.getReg .x6 &&& (3#64)=BitVec.ofNat 64 slot.val) :
    let t := quadPrefix s 22
    t.pc=5652 ∧ t.getReg .x10=12800 ∧
    t.getReg .x28=BitVec.ofNat 64 (12800+32*slot.val) ∧
    t.getReg .x29=BitVec.ofNat 64 (32*slot.val) ∧ t.getReg .x30=3 := by
  fin_cases slot <;> simp [quadPrefix,quadPrefixCode,execInstrBr,signExtend12,pc,pair,opened]

/-- Halfword codec at the body of the three-iteration rotation loop. -/
def quadSiblingCode : ByteCopy.CopyCode where
  image := packedImage
  start := 392
  count := 16
  source := .x21
  dest := .x28
  destOffset := 72
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := by
    intro j bounded s pc
    apply cap_image_fetch _ _ (392+2*j) _ (by omega) pc
    interval_cases j <;> rfl
  store := by
    intro j bounded s pc
    apply cap_image_fetch _ _ (392+2*j+1) _ (by omega) pc
    interval_cases j <;> rfl

end TwoPermutationPrototype.Quad.Checker
