import CommitGolfCandidate.CapCheckFinalAdmission
import CommitGolfCandidate.CapCheckKnownMarks
import CommitGolfCandidate.CapCheckDfsBudget

/-! Complete actual mark/DFS/final-check execution after successful records.
The collected map supplies both the finalized mark shape and its query count;
the fixed ABI supplies load admission. Actual root/suffix rejection is retained. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] execute

private theorem post_records_charge (result : Execution) :
    (result.charge 2 0).charge 1272 0 = result.charge 1274 0 := by
  simp only [Execution.charge, Nat.zero_add, ← Nat.add_assoc, Nat.reduceAdd]

theorem cap_check_post_records_execute (input : CheckInput)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length)
    (fuel : Nat) (sufficient : 8687 ≤ fuel) (allowCoins : Bool) :
    execute (capProgram.image .check) (1274+fuel) state allowCoins =
      (do let result ← capCheckDfsFinish (capCheckCollectedMarks roots) 510 (.visit 1)
            (capCheckTraversalInitial state)
          return result.charge 1274 0) := by
  have marked := cap_check_filled_mark_execute input ordinal state ready roots collected
    (2+fuel) allowCoins
  rw [show 1272+(2+fuel)=1274+fuel by omega] at marked
  change execute (capProgram.image .check) (1274+fuel) state allowCoins =
    (do let result ← execute (capProgram.image .check) (2+fuel)
          (capCheckMarkedFinal state) allowCoins
        return result.charge 1272 0) at marked
  rw [marked, cap_check_walk_initial_execute _
    (cap_check_marked_final_pc input ordinal state ready roots collected)]
  have finished := cap_check_loaded_dfs_finish input ordinal state ready roots collected
    selectors admitted enough fuel sufficient allowCoins
  change execute (capProgram.image .check) fuel
    (capCheckTraversalInitial state) allowCoins = _ at finished
  change (do
    let result ← (do
      let next ← execute (capProgram.image .check) fuel
        (capCheckTraversalInitial state) allowCoins
      return next.charge 2 0)
    return result.charge 1272 0) = _
  rw [finished]
  simp only [bind_assoc, pure_bind, post_records_charge]

theorem cap_check_post_records_queries (input : CheckInput)
    (ordinal : Nat) (state : MachineState)
    (ready : CapCheckRecordsReady input ordinal 0 state)
    (roots : CapRootMap) (collected : CapCheckCollected state roots)
    (selectors : CapCheckSelectors state)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (enough : 576*input.positions.card ≤ input.proof.length)
    (count : Nat) (known : capMarkedCount (capKnownView roots 7 0) ≤ count)
    (fuel : Nat) (sufficient : 8687 ≤ fuel) (allowCoins : Bool) :
    (execute (capProgram.image .check) (1274+fuel) state allowCoins).IsTotalQueryBound
      (7*count) := by
  rw [cap_check_post_records_execute input ordinal state ready roots collected selectors
    admitted enough fuel sufficient allowCoins]
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    cap_check_dfs_finish_card_queries (capCheckCollectedMarks roots) (capKnownView roots 7 0)
      (cap_check_known_root_marks roots) count known (capCheckTraversalInitial state)

end CommitGolfCandidate
