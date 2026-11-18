import CommitGolfCandidate.TwoPermutationPackedPostorderDecode
import CommitGolfCandidate.TwoPermutationPackedPostorderExecution
import CommitGolfCandidate.TwoPermutationPackedPostorderMeaning
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (getReg_setReg getReg_setMem)
attribute [local simp] getReg_setReg getReg_setMem
set_option maxRecDepth 8192

private theorem saved : ∀ j : Fin 9, Opening.Postorder.reg j.val ∉ ([.x20,.x21,.x25,.x26,.x27] : List Reg) := by decide

theorem pass_register (s : MachineState) (r : Reg) (keep : r ∈ ([.x20,.x21,.x25,.x26,.x27] : List Reg)) :
    (Opening.Postorder.eval s 1 8 0).getReg r = s.getReg r :=
  Opening.Postorder.eval_register _ _ _ _ _ (by intro j lo hi eq; exact saved ⟨j,by omega⟩ (eq ▸ keep))

def unrollEnter (s : MachineState) : MachineState :=
  (s.setReg .x6 (s.getReg .x26 + 2047)).setPC (Opening.Postorder.pcOf 674)

theorem entry_run (s : MachineState) (pc : s.pc = 0x1984) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) s coins =
      (do let r ← execute openingImage fuel (unrollEnter s) coins
          return r.charge 2 0) := by
  let mid := s.setPC (Opening.Postorder.pcOf 673)
  have f1 := packed_fetch_raw s 609 (.JAL .x0 256) (by decide) pc rfl
  have h1 : ordinaryStep s (.base (.JAL .x0 256)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, mid, pc, Opening.Postorder.pcOf, MachineState.setReg]
  have f2 := packed_fetch_raw mid 673 (.ADDI .x6 .x26 2047) (by decide) rfl rfl
  have h2 : ordinaryStep mid (.base (.ADDI .x6 .x26 2047)) = some (unrollEnter s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, mid,
      unrollEnter, Opening.Postorder.pcOf, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  rw [show 2+fuel = fuel+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 h1,
    execute_ordinary_step _ _ _ _ _ _ f2 h2]
  simp [Execution.charge, instructionCycles, Nat.add_assoc, ← Nat.add_assoc]

theorem return_run (s : MachineState) (pc : s.pc = Opening.Postorder.pcOf 1440) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) s coins =
      (do let r ← execute openingImage fuel (s.setPC 0x19b0) coins
          return r.charge 1 0) := by
  have f := packed_fetch_raw s 1440 (.JAL .x0 2093872) (by decide) pc rfl
  have h : ordinaryStep s (.base (.JAL .x0 2093872)) = some (s.setPC 0x19b0) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc, Opening.Postorder.pcOf, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f h]
  rfl

end TwoPermutationPrototype.PackedOpening
