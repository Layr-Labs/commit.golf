import CommitGolfCandidate.CapOpenRecordPass
import CommitGolfCandidate.CapOpenMarkedFinal

/-! Actual nonempty opening execution through traversal entry. Setup, record
emission, occupancy propagation and the two initialization instructions are all
charged here; the DFS and return epilogue remain separate continuations. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenMarkedFinal capOpenTraversalInitial

private theorem charge_pair (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second+first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_open_traversal_entry_execute
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    execute (capProgram.image .opening) (29+263*positions.card+2552+2+fuel)
      (capProgram.initialState .opening (trapdoor, positions)) allowCoins =
      (do let result ← execute (capProgram.image .opening) fuel
            (capOpenTraversalInitial trapdoor positions) allowCoins
          return result.charge (29+266*positions.card+2552+2) 0) := by
  have mark : execute (capProgram.image .opening) (2552+(2+fuel))
      (capOpenRecordsFinal trapdoor positions) allowCoins =
      (do let result ← execute (capProgram.image .opening) (2+fuel)
            (capOpenMarkedFinal trapdoor positions) allowCoins
          return result.charge 2552 0) := by
    simpa only [capProgram, LOG_LENGTH, capOpenMarkedFinal] using
      cap_open_filled_mark_execute trapdoor positions positive (2+fuel) allowCoins
  have entry : execute (capProgram.image .opening) (2+fuel)
      (capOpenMarkedFinal trapdoor positions) allowCoins =
      (do let result ← execute (capProgram.image .opening) fuel
            (capOpenTraversalInitial trapdoor positions) allowCoins
          return result.charge 2 0) := by
    simpa only [capOpenTraversalInitial] using
      cap_open_walk_initial_execute _ (cap_open_marked_final_pc trapdoor positions positive)
        fuel allowCoins
  rw [show 29+263*positions.card+2552+2+fuel =
      29+263*positions.card+(2552+(2+fuel)) by omega,
    cap_open_record_pass_execute trapdoor positions positive, mark, entry]
  simp only [bind_assoc, pure_bind, charge_pair, Nat.add_assoc]

end CommitGolfCandidate
