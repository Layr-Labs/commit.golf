import CommitGolfCandidate.CapCheckConstants
import CommitGolfCandidate.CapWordCopy
import CommitGolfCandidate.CapMarkImage

/-! Six real ordinary instructions turn the reconstructed lower-path index
into a cap leaf, compute its mark/root addresses, and load the occupancy word.
The subsequent branch and duplicate comparison are separate macros. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckGroupStartInstructions : List Instr :=
  [.ADD .x20 .x20 .x19, .SLLI .x7 .x20 3, .ADD .x30 .x9 .x7,
   .SLLI .x7 .x20 5, .ADD .x23 .x18 .x7, .LD .x6 .x30 0]

def capCheckGroupStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckGroupStartInstructions.take count).foldl execInstrBr state

theorem cap_check_group_start_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) :
    (capCheckGroupStartPrefix state count).pc =
      state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capCheckGroupStartPrefix, capCheckGroupStartInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_group_start_memory (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) :
    (capCheckGroupStartPrefix state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_check_group_start_execute (state : MachineState)
    (pc : state.pc = 4420)
    (markValid : accessValid
      ((capCheckGroupStartPrefix state 5).getReg .x30) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (6 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckGroupStartPrefix state 6) allowCoins
          return result.charge 6 0) := by
  apply execute_unit_steps (states := capCheckGroupStartPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckGroupStartInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (81 + i) _ (by omega)
    · rw [cap_check_group_start_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · interval_cases i
    all_goals simp only [capCheckGroupStartInstructions, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    all_goals try rfl
    simp only [ordinaryStep, memoryArgumentsValid, memAccess]
    change (if accessValid ((capCheckGroupStartPrefix state 5).getReg .x30 +
      (0#64)) 8 = true then
      some (execInstrBr (capCheckGroupStartPrefix state 5) (.LD .x6 .x30 0))
      else none) = _
    rw [BitVec.add_zero, markValid]
    rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
