import CommitGolfCandidate.ChainedPrefixSuffix
import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves

/-! The cached opener's root return and empty branch reach word 1435 without changing memory. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype
open TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem
@[local simp] private theorem dispatch_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem dispatch_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def cachedRootOps : List Instr :=
  [.ANDI .x7 .x6 1,.BNE .x7 .x0 20,.SRLI .x6 .x6 1,.BNE .x6 .x0 8164,
   .SUB .x11 .x21 .x20,.ADDI .x5 .x0 1,.ADDI .x10 .x0 0,.JAL .x0 3076]

def cachedRootPrefix (s : MachineState) (count : Nat) : MachineState :=
  (cachedRootOps.take count).foldl execInstrBr s

theorem cached_root_execution (s : MachineState) (pc : s.pc=0x1a3c) (root : s.getReg .x6=1#64) :
    RunsOpeningBlock s (cachedRootPrefix s 8) 8 := by
  intro fuel coins
  apply execute_unit_steps (states := cachedRootPrefix s)
  intro i inside
  refine ⟨.base (cachedRootOps.getD i .EBREAK),?_,?_,?_⟩
  · apply packed_fetch_raw _ (([655,656,661,662,663,664,665,666] : List Nat).getD i 0) _
      (by interval_cases i <;> decide)
    · interval_cases i <;>
        simp [cachedRootPrefix,cachedRootOps,execInstrBr,pc,root,signExtend12,signExtend13,signExtend21]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cached_root_frame (s : MachineState) (pc : s.pc=0x1a3c) (root : s.getReg .x6=1#64) :
    (cachedRootPrefix s 8).pc=9836 ∧ (cachedRootPrefix s 8).mem=s.mem ∧
    (cachedRootPrefix s 8).getReg .x16=s.getReg .x16 ∧
    (cachedRootPrefix s 8).getReg .x20=s.getReg .x20 := by
  simp [cachedRootPrefix,cachedRootOps,execInstrBr,pc,root,signExtend12,signExtend13,signExtend21]
  rfl

def cachedEmptyOps : List Instr :=
  [.ADDI .x20 .x15 0,.ADDI .x21 .x15 0,.BEQ .x16 .x0 2644,
   .SUB .x11 .x21 .x20,.ADDI .x5 .x0 1,.ADDI .x10 .x0 0,.JAL .x0 3076]

def cachedEmptyPrefix (s : MachineState) (count : Nat) : MachineState :=
  (cachedEmptyOps.take count).foldl execInstrBr s

theorem cached_empty_execution (s : MachineState) (pc : s.pc=4096) (empty : s.getReg .x16=0#64) :
    RunsOpeningBlock s (cachedEmptyPrefix s 7) 7 := by
  intro fuel coins
  apply execute_unit_steps (states := cachedEmptyPrefix s)
  intro i inside
  refine ⟨.base (cachedEmptyOps.getD i .EBREAK),?_,?_,?_⟩
  · apply packed_fetch_raw _ (([0,1,2,663,664,665,666] : List Nat).getD i 0) _
      (by interval_cases i <;> decide)
    · interval_cases i <;>
        simp [cachedEmptyPrefix,cachedEmptyOps,execInstrBr,pc,empty,signExtend12,signExtend13,signExtend21]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cached_empty_frame (s : MachineState) (pc : s.pc=4096) (empty : s.getReg .x16=0#64) :
    (cachedEmptyPrefix s 7).pc=9836 ∧ (cachedEmptyPrefix s 7).mem=s.mem ∧
    (cachedEmptyPrefix s 7).getReg .x16=0#64 ∧
    (cachedEmptyPrefix s 7).getReg .x20=s.getReg .x15 := by
  simp [cachedEmptyPrefix,cachedEmptyOps,execInstrBr,pc,empty,signExtend12,signExtend13,signExtend21]
  rfl

end CommitGolfCandidate.Chained.Native
