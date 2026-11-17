import CommitGolfCandidate.CapDigestCopy
import CommitGolfCandidate.CapParentPrepare
import CommitGolfCandidate.CapNavigationImage

/-! The two real address instructions before a DFS boundary copy. They compute
the same bounded root slot in opening and checking, with different root-base
registers. Neither instruction touches memory or the proof cursor x25. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capBoundaryRootRegister (checking : Bool) : Reg := if checking then .x18 else .x9
def capBoundaryEntry (checking : Bool) : Word := if checking then 4644 else 4452
def capBoundaryInstructions (checking : Bool) : List Instr :=
  [.SLLI .x7 .x20 5, .ADD .x23 (capBoundaryRootRegister checking) .x7]
def capBoundaryPrefix (checking : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((capBoundaryInstructions checking).take count).foldl execInstrBr state

theorem cap_boundary_prefix_succ (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count < 2) :
    capBoundaryPrefix checking state (count + 1) =
      execInstrBr (capBoundaryPrefix checking state count)
        (((capBoundaryInstructions checking)[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_boundary_prefix_memory (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2) : (capBoundaryPrefix checking state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_boundary_prefix_pc (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2) :
    (capBoundaryPrefix checking state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp only [capBoundaryPrefix, capBoundaryInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  · rfl
  · rfl

theorem cap_boundary_prefix_register (checking : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 2) (reg : Reg) (outside : reg ≠ .x7 ∧ reg ≠ .x23) :
    (capBoundaryPrefix checking state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capBoundaryPrefix, capBoundaryInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

theorem cap_boundary_address (checking : Bool) (state : MachineState) (node rootBase : Nat)
    (base : state.getReg (capBoundaryRootRegister checking) = BitVec.ofNat 64 rootBase)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capBoundaryPrefix checking state 2).getReg .x23 =
      BitVec.ofNat 64 (rootBase + 32 * node) := by
  cases checking <;>
    simp only [capBoundaryRootRegister, Bool.false_eq_true, ↓reduceIte] at base <;>
    simp (disch := decide) only [capBoundaryPrefix, capBoundaryInstructions,
      capBoundaryRootRegister, Bool.false_eq_true, ↓reduceIte, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, base, index,
      show (5 : BitVec 6).toNat = 5 by decide]
  all_goals
    rw [BitVec.shiftLeft_eq_mul_twoPow,
      show BitVec.twoPow 64 5 = BitVec.ofNat 64 32 by decide,
      ← BitVec.ofNat_mul]
    change BitVec.ofNat 64 rootBase + BitVec.ofNat 64 (node * 32) =
      BitVec.ofNat 64 (rootBase + 32 * node)
    rw [← BitVec.ofNat_add, Nat.mul_comm node 32]

theorem cap_check_boundary_address (state : MachineState) (node : Nat)
    (base : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) :
    (capBoundaryPrefix true state 2).getReg .x23 = capRootAddress node := by
  exact cap_boundary_address true state node 12288 base index

theorem cap_boundary_prepare_execute (checking : Bool) (state : MachineState)
    (pc : state.pc = capBoundaryEntry checking) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage checking) (2 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage checking) fuel
            (capBoundaryPrefix checking state 2) allowCoins
          return result.charge 2 0) := by
  apply execute_unit_steps (states := capBoundaryPrefix checking state)
  intro i bounded
  refine ⟨.base (((capBoundaryInstructions checking)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · cases checking
    · apply cap_image_fetch _ _ (89 + i) _ (by omega)
      · rw [cap_boundary_prefix_pc false state i (by omega), pc]
        interval_cases i <;> rfl
      · interval_cases i <;> rfl
    · apply cap_image_fetch _ _ (137 + i) _ (by omega)
      · rw [cap_boundary_prefix_pc true state i (by omega), pc]
        interval_cases i <;> rfl
      · interval_cases i <;> rfl
  · rw [cap_boundary_prefix_succ checking state i bounded]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
