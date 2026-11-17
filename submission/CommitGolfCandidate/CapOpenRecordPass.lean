import CommitGolfCandidate.CapOpenFilledMarks

/-! Actual opening setup followed by the complete nonempty record pass.
The input loader, sorted-index reads, real instruction fetches and admitted
copy windows are all supplied by the previously checked ABI handoff. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordsFinal capOpenInitializedState

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_record_pass_execute
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening) (29+263*positions.card+fuel)
      (capProgram.initialState .opening (trapdoor, positions)) allowCoins =
      (do let result ← execute (capProgram.image .opening) fuel
            (capOpenRecordsFinal trapdoor positions) allowCoins
          return result.charge (29+266*positions.card) 0) := by
  have windows := cap_open_abi_record_windows positions
  have loop := cap_open_records_loop_execute capOpenAbiRecordContext
    (capOpenRequestedIndices positions)
    (capProgram.initialState .opening (trapdoor, positions))
    windows.1 windows.2.1 windows.2.2
    (cap_open_abi_record_inputs trapdoor positions) positions.card _
    (cap_open_abi_record_ready trapdoor positions positive) fuel allowCoins
  have loop' : execute (capProgram.image .opening) (263*positions.card+fuel)
      (capOpenInitializedState (capProgram.initialState .opening (trapdoor, positions)))
      allowCoins =
    (do let result ← execute (capProgram.image .opening) fuel
          (capOpenRecordsFinal trapdoor positions) allowCoins
        return result.charge (266*positions.card) 0) := by
    simpa only [capProgram, LOG_LENGTH, capOpenRecordsFinal] using loop
  rw [Nat.add_assoc, cap_open_setup_execute _ rfl]
  rw [loop']
  simp only [capOpenRecordsFinal, bind_assoc, pure_bind, charge_pair,
    Nat.add_comm 29]

end CommitGolfCandidate
