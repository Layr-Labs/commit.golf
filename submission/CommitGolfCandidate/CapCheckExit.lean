import CommitGolfCandidate.CapUnknownFrame

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckExitState (state : MachineState) (success : Bool) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 (if success then 0 else 1)).setPC
    (if success then 4804 else 4816)

theorem cap_check_exit (state : MachineState) (success : Bool)
    (pc : state.pc = if success then 4796 else 4808) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (3 + fuel) state allowCoins =
      pure ⟨if success then .success else .failure,
        capCheckExitState state success, 3, 0⟩ := by
  let next := (state.setReg .x5 1).setPC (if success then 4800 else 4812)
  have first : fetch (capWalkImage true) state =
      some (.base (.ADDI .x5 .x0 1)) := by
    cases success
    · apply cap_image_fetch _ state 178 _ (by decide) pc
      rfl
    · apply cap_image_fetch _ state 175 _ (by decide) pc
      rfl
  have second : fetch (capWalkImage true) next =
      some (.base (.ADDI .x10 .x0 (if success then 0 else 1))) := by
    cases success
    · apply cap_image_fetch _ next 179 _ (by decide) rfl
      rfl
    · apply cap_image_fetch _ next 176 _ (by decide) rfl
      rfl
  have last : fetch (capWalkImage true) (capCheckExitState state success) =
      some (.base .ECALL) := by
    cases success
    · apply cap_image_fetch _ _ 180 _ (by decide) rfl
      rfl
    · apply cap_image_fetch _ _ 177 _ (by decide) rfl
      rfl
  have stepFirst : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some next := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, pc, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have stepSecond : ordinaryStep next (.base (.ADDI .x10 .x0 (if success then 0 else 1))) =
      some (capCheckExitState state success) := by
    cases success <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr,
      signExtend12, next, capCheckExitState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC]
  rw [Nat.add_comm 3 fuel]
  simp only [execute, first, stepFirst, second, stepSecond, last, instructionCycles,
    bind_assoc, pure_bind]
  cases success <;> simp [capCheckExitState, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, Execution.charge]

theorem cap_unknown_check_short_reject (state : MachineState) (node cursor limit : Nat)
    (pc : state.pc = capKnownVisit true)
    (marks : state.getReg .x9 = 28672)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (positive : 0 < node) (bounded : node < 512)
    (marked : Nat → Bool) (ready : CapMarksReady state 256 0 marked)
    (absent : marked node = false)
    (proof : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (noWrap : cursor + 32 < 2^64) (limitBound : limit < 2^64)
    (short : limit < cursor + 32) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (9 + fuel) state allowCoins =
      pure ⟨.failure, capCheckExitState (capUnknownCheckGuard state) false, 9, 0⟩ := by
  have guarded := cap_unknown_check_guard_pc state node cursor limit pc marks index
    positive bounded marked ready absent proof proofEnd noWrap limitBound
  have notEnough : ¬ cursor + 32 ≤ limit := by omega
  simp only [if_neg notEnough] at guarded
  rw [show 9 + fuel = 6 + (3 + fuel) by omega,
    cap_unknown_check_guard_execute state node pc marks index positive bounded marked ready absent,
    cap_check_exit _ false guarded]
  simp only [pure_bind, Execution.charge]
  rfl

theorem cap_unknown_check_short_memory (state : MachineState) :
    (capCheckExitState (capUnknownCheckGuard state) false).mem = state.mem :=
  cap_unknown_check_guard_memory state

end CommitGolfCandidate
