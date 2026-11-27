import CommitGolfCandidate.TwoPermutationPackedOpeningFields
import CommitGolfCandidate.TwoPermutationOpeningCapImage

namespace TwoPermutationPrototype.PackedOpening
set_option maxRecDepth 4096
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

def exitPrefix (state : MachineState) (count : Nat) : MachineState :=
  (Opening.exitInstructions.take count).foldl execInstrBr state

/-- Word 663 computes the wide proof length before the wire-format dispatcher at 664. -/
theorem execute_exit (s : MachineState) (pc : s.pc=0x1a5c) (fuel : Nat) (coins : Bool) :
    execute openingImage (1+fuel) s coins =
      (do let out ← execute openingImage fuel (exitPrefix s 1) coins;return out.charge 1 0) := by
  have op := packed_fetch_base s 663 (.SUB .x11 .x21 .x20) (by decide) pc (by rfl)
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ (exitPrefix s 1) _ _ op (by rfl)]
  rfl

theorem exit_register (state : MachineState) :
    (exitPrefix state 1).getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  simp [exitPrefix, Opening.exitInstructions, execInstrBr]

theorem exit_memory (state : MachineState) : (exitPrefix state 1).mem = state.mem := rfl

end TwoPermutationPrototype.PackedOpening
