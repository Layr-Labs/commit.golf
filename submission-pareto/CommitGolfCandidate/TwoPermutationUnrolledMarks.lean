import CommitGolfCandidate.TwoPermutationPostorderDecode
import CommitGolfCandidate.TwoPermutationPostorderExecution
import CommitGolfCandidate.TwoPermutationPostorderMeaning
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
attribute [local simp] getReg_setReg getReg_setMem
set_option maxRecDepth 8192

private theorem saved : ∀ j : Fin 9, Postorder.reg j.val ∉ ([.x20,.x21,.x9,.x26,.x27] : List Reg) := by decide

theorem pass_register (s : MachineState) (r : Reg) (keep : r ∈ ([.x20,.x21,.x9,.x26,.x27] : List Reg)) :
    (Postorder.eval s 1 8 0).getReg r = s.getReg r :=
  Postorder.eval_register _ _ _ _ _ (by intro j lo hi eq; exact saved ⟨j,by omega⟩ (eq ▸ keep))

def unrollEnter (s : MachineState) : MachineState :=
  (s.setReg .x6 (s.getReg .x26 + 2047)).setPC (Postorder.pcOf 280)

theorem entry_run (s : MachineState) (pc : s.pc = 0x13b4) (fuel : Nat) (coins : Bool) :
    execute openingImage (2+fuel) s coins =
      (do let r ← execute openingImage fuel (unrollEnter s) coins
          return r.charge 2 0) := by
  let mid := s.setPC (Postorder.pcOf 279)
  have f1 := opening_fetch s 237 (.JAL .x0 168) (by decide) pc rfl
  have h1 : ordinaryStep s (.base (.JAL .x0 168)) = some mid := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, mid, pc, Postorder.pcOf, MachineState.setReg]
  have f2 := opening_fetch mid 279 (.ADDI .x6 .x26 2047) (by decide) rfl rfl
  have h2 : ordinaryStep mid (.base (.ADDI .x6 .x26 2047)) = some (unrollEnter s) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, mid,
      unrollEnter, Postorder.pcOf, MachineState.setReg, MachineState.setPC, MachineState.getReg]
  rw [show 2+fuel = fuel+1+1 by omega, execute_ordinary_step _ _ _ _ _ _ f1 h1,
    execute_ordinary_step _ _ _ _ _ _ f2 h2]
  simp [Execution.charge, instructionCycles, Nat.add_assoc, ← Nat.add_assoc]

theorem return_run (s : MachineState) (pc : s.pc = Postorder.pcOf 1046) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) s coins =
      (do let r ← execute openingImage fuel (s.setPC 0x13e0) coins
          return r.charge 1 0) := by
  have f := opening_fetch s 1046 (.JAL .x0 2093960) (by decide) pc rfl
  have h : ordinaryStep s (.base (.JAL .x0 2093960)) = some (s.setPC 0x13e0) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21, pc, Postorder.pcOf, MachineState.setReg]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ f h]
  rfl

end TwoPermutationPrototype.Opening
