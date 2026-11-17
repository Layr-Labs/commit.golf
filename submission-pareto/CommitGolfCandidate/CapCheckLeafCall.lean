import CommitGolfCandidate.S3CheckLeafRun

/-! The actual cap-checker caller is word 39, after the eight salt-copy words
and the proof-cursor advance. Its JAL writes link 4256 and enters the stage-3
leaf at word 257 (pc 5124). The caller and subroutine are both charged here. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckLeafCallState (state : MachineState) : MachineState :=
  (state.setReg .x1 4256).setPC 5124

theorem cap_check_leaf_call_fetched (state : MachineState) (pc : state.pc = 4252) :
    fetch ((capExperimental 24).image .check) state =
      some (.base (.JAL .x1 872)) := by
  apply cap_image_fetch _ state 39 _ (by decide) pc
  rfl

theorem cap_check_leaf_call_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1) :
    (capCheckLeafCallState state).getReg reg = state.getReg reg := by
  simp only [capCheckLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

/-- One real call plus the complete leaf: 91 instructions, 105 cycles, 2 calls. -/
theorem cap_check_leaf_call_execute (state : MachineState) (pc : state.pc = 4252)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (91 + fuel) state allowCoins =
      (do let finished ← capCheckLeaf (capCheckLeafCallState state)
          let result ← execute ((capExperimental 24).image .check) fuel
            (finished.setPC 4256) allowCoins
          return result.charge 105 2) := by
  have stepped : ordinaryStep state (.base (.JAL .x1 872)) =
      some (capCheckLeafCallState state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, ↓reduceIte,
      execInstrBr, pc, capCheckLeafCallState]
    rfl
  have nextSource : ∀ word < 32,
      accessValid ((capCheckLeafCallState state).getReg .x8 +
        BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa only [cap_check_leaf_call_register state .x8 (by decide)] using sourceValid
  have link : (capCheckLeafCallState state).getReg .x1 = 4256 := by
    simp only [capCheckLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  rw [show 91 + fuel = (90 + fuel) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ (cap_check_leaf_call_fetched state pc) stepped,
    cap_check_leaf_execute (capCheckLeafCallState state) rfl link nextSource]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
