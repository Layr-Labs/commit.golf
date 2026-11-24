import CommitGolfCandidate.TwoPermutationPackedCollectLoop
import CommitGolfCandidate.TwoPermutationPackedCheckerExit
import CommitGolfCandidate.TwoPermutationCapAssembly
import CommitGolfCandidate.TwoPermutationPackedNearCap

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame capRootAt checker_cap_group record_input_root
  checker_positions_bound checker_global_budget)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
set_option maxHeartbeats 1000000

structure CheckerObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 41*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    Nonempty (Quartet.RecordedQuartetOpening oracle index.val (input.values index) input.commitment observed.1.2)
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success
  /-- One-byte search: the truncated honest proof (`nearCheckInput`, 128 positions, 128 frontier digests). -/
  nearHonest : ∀ message salts, input = nearCheckInput oracle message input.positions salts →
    input.positions.card = 128 → (honestNodes oracle message input.positions salts).length = 128 →
    observed.1.1.exit = .success

theorem checker_cap_bindings (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (lowerRows capRows : List PublicRow)
    (table : CollectedTable oracle input input.positions.card state lowerRows)
    (framed : RecordInputFrame input input.positions.card state)
    (paths : ∀ leaf ∈ Opening.groupsBefore input.positions input.positions.card, 256 ≤ leaf → leaf < 512 →
      ProjectedPath capRows leaf 8 (capRootAt state leaf) (readBuffer state (8*536871424) 32)) :
    ∀ index : {i // i ∈ input.positions},
      Nonempty (Quartet.RecordedQuartetOpening oracle index.val (input.values index) input.commitment (lowerRows++capRows)) := by
  intro index
  obtain ⟨seen, ⟨lower⟩⟩ := collect_authenticated_index oracle input state lowerRows table index
  obtain ⟨low, high⟩ := checker_cap_group index.val
  have cap := paths (capGroup index.val) seen low high
  have root : readBuffer state (8*536871424) 32 = input.commitment :=
    record_input_root input input.positions.card state framed
  rw [root] at cap
  exact ⟨(lower.mono fun _ => List.mem_append_left _).join
    (cap.mono fun _ => List.mem_append_right _)⟩

structure CheckerCapFacts (oracle : Oracle) (input : CheckInput) (state : MachineState) (fuel : Nat) : Prop where
  terminates : (checkEvaluation oracle (recordRows (execute packedImage fuel state false))).1.1.exit ≠ .unfinished
  queries : (checkEvaluation oracle (recordRows (execute packedImage fuel state false))).2 ≤ 24*input.positions.card
  paths : let result := checkEvaluation oracle (recordRows (execute packedImage fuel state false))
    result.1.1.exit = .success →
    ∀ leaf ∈ Opening.groupsBefore input.positions input.positions.card, 256 ≤ leaf → leaf < 512 →
      ProjectedPath result.1.2 leaf 8 (capRootAt state leaf) (readBuffer state (8*536871424) 32)
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts →
    (checkEvaluation oracle (recordRows (execute packedImage fuel state false))).1.1.exit = .success
  nearHonest : ∀ message salts, input = nearCheckInput oracle message input.positions salts →
    input.positions.card = 128 → (honestNodes oracle message input.positions salts).length = 128 →
    (checkEvaluation oracle (recordRows (execute packedImage fuel state false))).1.1.exit = .success

attribute [local irreducible] execute checkEvaluation collectRecords

theorem checker_body_facts (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record) (oracle : Oracle) (input : CheckInput) (beginning : MachineState)
    (fits : ProofWithin input) (cursor : RecordCursor input 0 beginning) (frame : RecordInputFrame input 0 beginning)
    (table : CollectedTable oracle input 0 beginning []) (fuel : Nat)
    (fuelBound : 2048*input.positions.card+80000 ≤ fuel)
    (cap : ∀ state rows rest, 80000 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel beginning false))) := by
  let collected := collectRecords record oracle input input.positions.card 0 beginning
  let rest := fuel-collected.steps
  obtain ⟨run,facts⟩ :=
    collect_records_observation record verified oracle input input.positions.card 0 (by omega) beginning [] cursor frame table fits rest
  have limit : collected.steps ≤ 2048*input.positions.card := facts.stepBound
  have enough : 80000 ≤ rest := by dsimp only [rest]; omega
  have total : collected.steps+rest = fuel := by dsimp only [rest]; omega
  change checkEvaluation oracle (recordRows (execute packedImage (collected.steps+rest) beginning false)) = _ at run
  rw [total] at run
  rw [run]
  cases rejected : collected.rejected with
  | true =>
    have pc := facts.rejected rejected
    have finish : execute packedImage rest collected.state false = pure ⟨.failure,headerRejectState collected.state,3,0⟩ := by
      rw [show rest=3+(rest-3) by omega]
      exact execute_header_reject _ pc _
    change CheckerObservationFacts oracle input
      (((checkEvaluation oracle (recordRows (execute packedImage rest collected.state false))).1.1.charge
        collected.cycles (17*collected.records),
        collected.rows ++ (checkEvaluation oracle (recordRows (execute packedImage rest collected.state false))).1.2),
        17*collected.records+(checkEvaluation oracle (recordRows (execute packedImage rest collected.state false))).2)
    rw [finish,record_rows_pure,check_evaluation_pure]
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro impossible
      cases impossible
    · have count : collected.records ≤ input.positions.card := facts.queryRecords
      change 17*collected.records+0 ≤ 41*input.positions.card
      omega
    · intro impossible
      cases impossible
    · intro message salts canonical
      have accepts := facts.honest message salts (NearHonest.of_eq canonical)
      rw [rejected] at accepts
      cases accepts
    · intro message salts near _ f
      have many : 9 ≤ (honestNodes oracle message input.positions salts).length := by omega
      have close := near_honest_input oracle message input.positions salts many
      rw [← near] at close
      have accepts := facts.honest message salts close
      rw [rejected] at accepts
      cases accepts
  | false =>
    obtain ⟨_,finalCursor,finalFrame,finalTable⟩ := facts.live rejected
    have verified : CollectedTable oracle input input.positions.card collected.state collected.rows := by
      simpa only [List.nil_append] using finalTable
    have ending := cap collected.state collected.rows rest enough finalCursor finalFrame verified
    refine ⟨ending.terminates,?_,?_,ending.honest,ending.nearHonest⟩
    · exact (show ∀ r q, r ≤ input.positions.card → q ≤ 24*input.positions.card → 17*r+q ≤ 41*input.positions.card
        from fun r q a b => by omega) collected.records _ facts.queryRecords ending.queries
    · intro complete
      exact checker_cap_bindings oracle input collected.state collected.rows _ verified finalFrame (ending.paths complete)

theorem CheckerObservationFacts.charge {oracle : Oracle} {input : CheckInput}
    {result : (Execution × List PublicRow) × Nat} (good : CheckerObservationFacts oracle input result)
    (cycles : Nat) :
    CheckerObservationFacts oracle input ((result.1.1.charge cycles 0, result.1.2), result.2) :=
  ⟨good.terminates, good.queries, good.paths, good.honest, good.nearHonest⟩

end TwoPermutationPrototype.Packed.Checker
