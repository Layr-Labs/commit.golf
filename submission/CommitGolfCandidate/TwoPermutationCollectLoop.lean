import CommitGolfCandidate.TwoPermutationCollectControl

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

structure CollectionResult where
  state : MachineState
  steps : Nat
  cycles : Nat
  records : Nat
  rows : List PublicRow
  rejected : Bool

noncomputable def collectRecords (oracle : Oracle) (input : CheckInput) :
    Nat → Nat → MachineState → CollectionResult
  | 0, _, state => ⟨state, 0, 0, 0, [], false⟩
  | left+1, ordinal, state => by
    classical
    exact if present : ordinal < input.positions.card then
      let index := (honestIndex input.positions ordinal present).val
      let leaf := recordLeaf oracle state (checkSourceWord ordinal) index
      let lower := recordLower oracle state (checkSourceWord ordinal) index
      let group := groupRun lower.state (capGroup index)
      let steps := 33+lower.steps+group.2
      let cycles := 47+lower.cycles+group.2
      let rows := leaf.2 ++ lower.rows
      if GroupAccepted lower.state (capGroup index) then
        let rest := collectRecords oracle input left (ordinal+1) group.1
        ⟨rest.state, steps+rest.steps, cycles+rest.cycles, rest.records+1, rows++rest.rows, rest.rejected⟩
      else ⟨group.1, steps, cycles, 1, rows, true⟩
    else ⟨state, 0, 0, 0, [], true⟩

/-- Successful collection stops at the start of cap processing. A mismatch stops at the rejection HALT. -/
structure CollectionFacts (oracle : Oracle) (input : CheckInput) (left : Nat)
    (result : CollectionResult) (rows : List PublicRow) : Prop where
  stepBound : result.steps ≤ 472*left
  queryRecords : result.records ≤ left
  rejected : result.rejected = true → result.state.pc = 0x1368
  live : result.rejected = false → result.records = left ∧
    RecordCursor input input.positions.card result.state ∧
    RecordInputFrame input input.positions.card result.state ∧
    CollectedTable oracle input input.positions.card result.state (rows++result.rows)
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts → result.rejected = false

attribute [local irreducible] execute checkEvaluation recordLeaf recordLower

theorem collect_records_observation (oracle : Oracle) (input : CheckInput)
    (left ordinal : Nat) (count : ordinal+left=input.positions.card)
    (state : MachineState) (rows : List PublicRow)
    (cursor : RecordCursor input ordinal state) (loaded : RecordInputFrame input ordinal state)
    (table : CollectedTable oracle input ordinal state rows) (fuel : Nat) :
    let collected := collectRecords oracle input left ordinal state
    let tail := checkEvaluation oracle (recordRows (execute checkerImage fuel collected.state false))
    checkEvaluation oracle (recordRows (execute checkerImage (collected.steps+fuel) state false)) =
      ((tail.1.1.charge collected.cycles (18*collected.records), collected.rows++tail.1.2),
        18*collected.records+tail.2) ∧
      CollectionFacts oracle input left collected rows := by
  induction left generalizing ordinal state rows with
  | zero =>
    have done : ordinal=input.positions.card := by omega
    subst ordinal
    refine ⟨?_, ?_⟩
    · simp [collectRecords, Execution.charge]
    · refine ⟨Nat.zero_le _,Nat.zero_le _,?_,?_,fun _ _ _ => rfl⟩
      · intro impossible
        cases impossible
      · intro _
        exact ⟨rfl,cursor,loaded,by simpa only [collectRecords,List.append_nil] using table⟩
  | succ left ih =>
    have present : ordinal < input.positions.card := by omega
    let index := (honestIndex input.positions ordinal present).val
    let leaf := recordLeaf oracle state (checkSourceWord ordinal) index
    let lower := recordLower oracle state (checkSourceWord ordinal) index
    let group := groupRun lower.state (capGroup index)
    let steps := 33+lower.steps+group.2
    let cycles := 47+lower.cycles+group.2
    let extra := leaf.2++lower.rows
    have phase := group_after_record_ready oracle input ordinal present state cursor loaded
    have frame := group_run_state lower.state (capGroup index) (input.positions.card-(ordinal+1)) phase
    have bound : steps ≤ 472 := by
      have one := check_record_steps oracle state (checkSourceWord ordinal) index
      have insert := group_run_cost lower.state (capGroup index) (input.positions.card-(ordinal+1)) phase
      change 33+lower.steps ≤ 449 at one
      change group.2 ≤ 23 at insert
      change 33+lower.steps+group.2 ≤ 472
      omega
    dsimp only
    rw [collectRecords, dite_eq_left present]
    dsimp only
    by_cases accepted : GroupAccepted lower.state (capGroup index)
    · rw [ite_eq_left accepted]
      let tail := collectRecords oracle input left (ordinal+1) group.1
      obtain ⟨nextCursor,nextFrame,nextTable⟩ :=
        group_collect_transition oracle input ordinal present state cursor loaded rows table accepted
      obtain ⟨run, facts⟩ :=
        ih (ordinal+1) (by omega) group.1 (rows++extra) nextCursor nextFrame nextTable
      have firstRun := execute_record_group oracle input ordinal present state cursor loaded (tail.steps+fuel)
      dsimp only at firstRun run facts
      constructor
      · rw [show steps+tail.steps+fuel=steps+(tail.steps+fuel) by omega, firstRun, run]
        simp only [Execution.charge, List.append_assoc, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm]
        rfl
      · refine ⟨?_,?_,facts.rejected,?_,facts.honest⟩
        · have limit : tail.steps ≤ 472*left := facts.stepBound
          change steps+tail.steps ≤ 472*(left+1)
          omega
        · have count : tail.records ≤ left := facts.queryRecords
          change tail.records+1 ≤ left+1
          omega
        · intro acceptedAll
          obtain ⟨countDone,cursorDone,frameDone,tableDone⟩ := facts.live acceptedAll
          exact ⟨congrArg (·+1) countDone,cursorDone,frameDone,
            by simpa only [extra,List.append_assoc] using tableDone⟩
    · rw [ite_eq_right accepted]
      constructor
      · simpa only [Nat.mul_one] using
          execute_record_group oracle input ordinal present state cursor loaded fuel
      · refine ⟨?_,Nat.succ_le_succ (Nat.zero_le _),?_,?_,?_⟩
        · change steps ≤ 472*(left+1)
          omega
        · intro _
          exact frame.pc.trans (ite_eq_right accepted)
        · intro impossible
          cases impossible
        · intro message salts canonical
          exact False.elim (accepted (group_accepts_honest oracle input ordinal present state cursor loaded rows table
            message salts canonical))

end TwoPermutationPrototype.Checker
