import CommitGolfCandidate.CapFlow
import CommitGolfCandidate.CapBoundaryPrepare

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capBoundaryGuardAdded (state : MachineState) : MachineState :=
  execInstrBr state (.ADDI .x6 .x25 32)
def capBoundaryGuardState (state : MachineState) : MachineState :=
  capFlowState (.below .x22 .x6 168) (capBoundaryGuardAdded state)

theorem cap_boundary_guard_added_pc (state : MachineState) :
    (capBoundaryGuardAdded state).pc = state.pc + 4 := rfl

theorem cap_boundary_guard_added_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capBoundaryGuardAdded state).getReg reg = state.getReg reg := by
  simp only [capBoundaryGuardAdded, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_boundary_guard_added_limit (state : MachineState) (cursor : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor) :
    (capBoundaryGuardAdded state).getReg .x6 = BitVec.ofNat 64 (cursor + 32) := by
  simp (disch := decide) only [capBoundaryGuardAdded, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq, pointer,
    show signExtend12 (32 : BitVec 12) = (32 : Word) by decide]
  exact (BitVec.ofNat_add cursor 32).symm

theorem cap_boundary_guard_memory (state : MachineState) :
    (capBoundaryGuardState state).mem = state.mem := by
  rw [capBoundaryGuardState, cap_flow_memory]
  rfl

theorem cap_boundary_guard_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6) :
    (capBoundaryGuardState state).getReg reg = state.getReg reg := by
  rw [capBoundaryGuardState, cap_flow_register]
  exact cap_boundary_guard_added_register state reg outside

theorem cap_boundary_guard_pc (state : MachineState) (cursor limit : Nat)
    (pc : state.pc = 4636)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (proofEnd : state.getReg .x22 = BitVec.ofNat 64 limit)
    (noWrap : cursor + 32 < 2^64) (limitBound : limit < 2^64) :
    (capBoundaryGuardState state).pc =
      if cursor + 32 ≤ limit then capBoundaryEntry true else 4808 := by
  have comparison :
      (capBoundaryGuardAdded state).getReg .x22 <
        (capBoundaryGuardAdded state).getReg .x6 ↔ limit < cursor + 32 := by
    rw [cap_boundary_guard_added_register state .x22 (by decide), proofEnd,
      cap_boundary_guard_added_limit state cursor pointer, BitVec.lt_def]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt noWrap,
      Nat.mod_eq_of_lt limitBound]
  rw [capBoundaryGuardState, cap_flow_below_pc]
  simp only [comparison]
  rw [cap_boundary_guard_added_pc, pc]
  by_cases enough : cursor + 32 ≤ limit
  · have notShort : ¬ limit < cursor + 32 := by omega
    simp only [if_neg notShort, if_pos enough]
    rfl
  · have short : limit < cursor + 32 := by omega
    simp only [if_pos short, if_neg enough]
    rfl

private theorem charge_pair (result : Execution) :
    (result.charge 1 0).charge 1 0 = result.charge 2 0 := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc]

theorem cap_boundary_guard_execute (state : MachineState)
    (pc : state.pc = 4636) (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (2 + fuel) state allowCoins =
      (do let result ← execute (capWalkImage true) fuel
            (capBoundaryGuardState state) allowCoins
          return result.charge 2 0) := by
  have add : fetch (capWalkImage true) state = some (.base (.ADDI .x6 .x25 32)) := by
    apply cap_image_fetch _ state 135 _ (by decide) pc
    rfl
  have guard : fetch (capWalkImage true) (capBoundaryGuardAdded state) =
      some (.base (capFlowInstruction (.below .x22 .x6 168))) := by
    apply cap_image_fetch _ _ 136 _ (by decide)
    · rw [cap_boundary_guard_added_pc, pc]
      rfl
    · rfl
  have first : execute (capWalkImage true) (1 + (1 + fuel)) state allowCoins =
      (do let result ← execute (capWalkImage true) (1 + fuel)
            (capBoundaryGuardAdded state) allowCoins
          return result.charge 1 0) := by
    rw [Nat.add_comm 1 (1 + fuel), execute_ordinary_step _ _ _ _ _ _ add (by rfl)]
    rfl
  rw [show 2 + fuel = 1 + (1 + fuel) by omega, first,
    cap_flow_execute _ _ _ guard]
  simp only [bind_assoc, pure_bind, charge_pair, capBoundaryGuardState]

end CommitGolfCandidate
