import CommitGolfCandidate.CapCheckExit

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

def capCheckProofEndState (state : MachineState) : MachineState :=
  execInstrBr state (.BNE .x25 .x22 72)

theorem cap_check_proof_end_execute (state : MachineState) (pc : state.pc=4736)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (1+fuel) state allowCoins =
      (do let result ← execute (capWalkImage true) fuel (capCheckProofEndState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (capWalkImage true) state=some (.base (.BNE .x25 .x22 72)) := by
    apply cap_image_fetch _ state 160 _ (by decide) pc
    rfl
  have step : ordinaryStep state (.base (.BNE .x25 .x22 72))=
      some (capCheckProofEndState state) := rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
  rfl

theorem cap_check_proof_end_pc (state : MachineState) (pc : state.pc=4736) :
    (capCheckProofEndState state).pc=
      if state.getReg .x25=state.getReg .x22 then 4740 else 4808 := by
  simp only [capCheckProofEndState,execInstrBr,MachineState.setPC,pc]
  by_cases equal : state.getReg .x25=state.getReg .x22
  · simp only [equal,bne_self_eq_false,↓reduceIte]
    rfl
  · have different := bne_iff_ne.mpr equal
    simp only [different,equal,↓reduceIte]
    rfl

theorem cap_check_proof_end_memory (state : MachineState) :
    (capCheckProofEndState state).mem=state.mem := by
  simp only [capCheckProofEndState,execInstrBr]
  split <;> rfl

theorem cap_check_proof_end_register (state : MachineState) (reg : Reg) :
    (capCheckProofEndState state).getReg reg=state.getReg reg := by
  simp only [capCheckProofEndState,execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_check_proof_end_reject (state : MachineState) (pc : state.pc=4736)
    (trailing : state.getReg .x25 ≠ state.getReg .x22)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (4+fuel) state allowCoins =
      pure ⟨.failure,capCheckExitState (capCheckProofEndState state) false,4,0⟩ := by
  have endPC := cap_check_proof_end_pc state pc
  rw [if_neg trailing] at endPC
  rw [show 4+fuel=1+(3+fuel) by omega,cap_check_proof_end_execute state pc,
    cap_check_exit _ false endPC]
  simp only [pure_bind,Execution.charge]
  rfl

end CommitGolfCandidate
