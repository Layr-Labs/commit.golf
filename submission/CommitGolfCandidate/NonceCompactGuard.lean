import CommitGolfCandidate.NonceCompactOuter

/-! The concrete compactor's initial empty-record guard preserves all inputs
and chooses the record loop or its footer directly. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactGuardState (state : MachineState) : MachineState :=
  execInstrBr state (.BEQ .x24 .x0 556)

theorem nonce_compact_guard_execute (state : MachineState) (pc : state.pc=4556)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (1+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactGuardState state) coins
          return result.charge 1 0) := by
  have fetched : fetch nonceCompactImage state=some (.base (.BEQ .x24 .x0 556)) := by
    apply cap_image_fetch _ state 115 _ (by decide) pc
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step nonceCompactImage _ state
    (nonceCompactGuardState state) fuel coins fetched (by rfl)]
  rfl

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x24 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x24 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_compact_guard_memory (state : MachineState) :
    (nonceCompactGuardState state).mem=state.mem := branch_memory state 556

theorem nonce_compact_guard_register (state : MachineState) (reg : Reg) :
    (nonceCompactGuardState state).getReg reg=state.getReg reg := branch_register state 556 reg

theorem nonce_compact_guard_pc (state : MachineState) (pc : state.pc=4556)
    (count : Nat) (small : count<2^64)
    (counter : state.getReg .x24=BitVec.ofNat 64 count) :
    (nonceCompactGuardState state).pc=if count=0 then 5112 else 4560 := by
  have zero : (BitVec.ofNat 64 count : Word)=0 ↔ count=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      change count%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt small] at numeric
      exact numeric
    · rintro rfl
      rfl
  simp only [nonceCompactGuardState, execInstrBr, counter,
    show state.getReg .x0=0 from rfl, beq_iff_eq, zero]
  by_cases empty : count=0 <;>
    simp [empty, MachineState.setPC, pc, signExtend13]

end CommitGolfCandidate
