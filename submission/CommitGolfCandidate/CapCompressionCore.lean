import CommitGolfCandidate.Execution

/-! Image-independent compression syscall definitions and execution bridges.
Legacy cap-state preservation lemmas remain in `CapCompressionStep`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capCompressionInput (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x10).toNat 64)

def capCompressionAnswer (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state (state.getReg .x12) answer

/-- One real ECALL pays eight cycles and one public query, on either coin policy. -/
theorem cap_compression_execute (image : Image) (state : MachineState)
    (fetched : fetch image state = some (.base .ECALL))
    (selectors : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (sourceValid : rangeValid (state.getReg .x10) 64 = true)
    (destinationValid : rangeValid (state.getReg .x12) 32 = true)
    (sourceAligned : (state.getReg .x10).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x12).toNat % 8 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (capCompressionInput state))
          let result ← execute image fuel (capCompressionAnswer state answer) allowCoins
          return result.charge 8 1) := by
  have input : oracleInput state = some (capCompressionInput state) := by
    simp [oracleInput, capCompressionInput, selectors.2.2, selectors.2.1,
      COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, sourceValid, destinationValid]
    refine ⟨⟨sourceAligned, destinationAligned⟩, ?_⟩
    rw [selectors.2.2]
    exact BitVec.setWidth_eq _
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos selectors.1, input]
  simp [capCompressionAnswer, writeOracleAnswer, selectors.2.2,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

theorem cap_compression_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) :
    (capCompressionAnswer state answer).getReg reg = state.getReg reg :=
  writeBits_register state _ answer reg

end CommitGolfCandidate
