import CommitGolfCandidate.TwoPermutationCollectLoop
import CommitGolfCandidate.TwoPermutationCheckerFacts
import CommitGolfCandidate.TwoPermutationCapAssembly
import CommitGolfCandidate.TwoPermutationCheckerRootRun

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxHeartbeats 1000000

structure CheckerCapFacts (oracle : Oracle) (input : CheckInput) (state : MachineState) (fuel : Nat) : Prop where
  terminates : (checkEvaluation oracle (recordRows (execute checkerImage fuel state false))).1.1.exit ≠ .unfinished
  queries : (checkEvaluation oracle (recordRows (execute checkerImage fuel state false))).2 ≤ 8*input.positions.card
  paths : let result := checkEvaluation oracle (recordRows (execute checkerImage fuel state false))
    result.1.1.exit = .success →
    ∀ leaf ∈ Opening.groupsBefore input.positions input.positions.card, 256 ≤ leaf → leaf < 512 →
      RecordedPath result.1.2 leaf 8 (capRootAt state leaf) (readBuffer state (8*536871424) 32)
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts →
    (checkEvaluation oracle (recordRows (execute checkerImage fuel state false))).1.1.exit = .success

attribute [local irreducible] execute checkEvaluation collectRecords

theorem checker_body_facts (oracle : Oracle) (input : CheckInput) (beginning : MachineState)
    (cursor : RecordCursor input 0 beginning) (frame : RecordInputFrame input 0 beginning)
    (table : CollectedTable oracle input 0 beginning []) (fuel : Nat)
    (fuelBound : 472*input.positions.card+14840 ≤ fuel)
    (cap : ∀ state rows rest, 14840 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute checkerImage fuel beginning false))) := by
  let collected := collectRecords oracle input input.positions.card 0 beginning
  let rest := fuel-collected.steps
  obtain ⟨run,facts⟩ :=
    collect_records_observation oracle input input.positions.card 0 (by omega) beginning [] cursor frame table rest
  have limit : collected.steps ≤ 472*input.positions.card := facts.stepBound
  have enough : 14840 ≤ rest := by dsimp only [rest]; omega
  have total : collected.steps+rest = fuel := by dsimp only [rest]; omega
  change checkEvaluation oracle (recordRows (execute checkerImage (collected.steps+rest) beginning false)) = _ at run
  rw [total] at run
  rw [run]
  cases rejected : collected.rejected with
  | true =>
    have pc := facts.rejected rejected
    have finish : execute checkerImage rest collected.state false = pure ⟨.failure,rejectState collected.state,3,0⟩ := by
      rw [show rest=3+(rest-3) by omega]
      exact execute_reject _ pc _
    change CheckerObservationFacts oracle input
      (((checkEvaluation oracle (recordRows (execute checkerImage rest collected.state false))).1.1.charge
        collected.cycles (18*collected.records),
        collected.rows ++ (checkEvaluation oracle (recordRows (execute checkerImage rest collected.state false))).1.2),
        18*collected.records+(checkEvaluation oracle (recordRows (execute checkerImage rest collected.state false))).2)
    rw [finish,record_rows_pure,check_evaluation_pure]
    refine ⟨?_,?_,?_,?_⟩
    · intro impossible
      cases impossible
    · have count : collected.records ≤ input.positions.card := facts.queryRecords
      change 18*collected.records+0 ≤ 26*input.positions.card
      omega
    · intro impossible
      cases impossible
    · intro message salts canonical
      have accepts := facts.honest message salts canonical
      rw [rejected] at accepts
      cases accepts
  | false =>
    obtain ⟨_,finalCursor,finalFrame,finalTable⟩ := facts.live rejected
    have verified : CollectedTable oracle input input.positions.card collected.state collected.rows := by
      simpa only [List.nil_append] using finalTable
    have ending := cap collected.state collected.rows rest enough finalCursor finalFrame verified
    refine ⟨ending.terminates,?_,?_,ending.honest⟩
    · exact (checker_global_budget input collected.records _ facts.queryRecords ending.queries).1
    · intro complete
      exact checker_cap_bindings oracle input collected.state collected.rows _ verified finalFrame (ending.paths complete)

theorem CheckerObservationFacts.charge {oracle : Oracle} {input : CheckInput}
    {result : (Execution × List PublicRow) × Nat} (good : CheckerObservationFacts oracle input result)
    (cycles : Nat) :
    CheckerObservationFacts oracle input ((result.1.1.charge cycles 0, result.1.2), result.2) :=
  ⟨good.terminates, good.queries, good.paths, good.honest⟩

end TwoPermutationPrototype.Checker
