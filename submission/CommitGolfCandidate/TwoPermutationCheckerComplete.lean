import CommitGolfCandidate.TwoPermutationCheckerCapABI

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

/-- The header's three exits, as loaded by the actual check ABI. -/
structure CheckerHeaderFacts : Prop where
  empty : ∀ input : CheckInput, input.proof.length ≤ Assembly.submission.sizes.proof →
    input.positions.card = 0 →
    ∃ result : Execution,
      execute checkerImage 17179934720 (Assembly.submission.initialState .check input) false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success)
  short : ∀ input : CheckInput, input.proof.length ≤ Assembly.submission.sizes.proof →
    input.proof.length < 528*input.positions.card →
    ∃ result : Execution,
      execute checkerImage 17179934720 (Assembly.submission.initialState .check input) false = pure result ∧
      result.exit = .failure
  positive : ∀ input : CheckInput, input.proof.length ≤ Assembly.submission.sizes.proof →
    input.positions.card ≠ 0 →
    528*input.positions.card ≤ input.proof.length →
    ∃ state : MachineState, ∃ cost ≤ 64,
      RecordCursor input 0 state ∧ state.mem = (Assembly.submission.initialState .check input).mem ∧
      ∀ fuel, execute checkerImage (cost+fuel) (Assembly.submission.initialState .check input) false =
        (do let result ← execute checkerImage fuel state false
            return result.charge cost 0)

attribute [local irreducible] execute checkEvaluation

theorem checker_complete_observation (head : CheckerHeaderFacts) (oracle : Oracle) (input : CheckInput) :
    CheckerObservationFacts oracle input (checkObservation Assembly.submission oracle input) := by
  by_cases admitted : input.proof.length ≤ Assembly.submission.sizes.proof
  · rw [check_observation_admitted oracle input admitted]
    by_cases empty : input.positions.card = 0
    · obtain ⟨result, executed, terminal, succeeds⟩ := head.empty input admitted empty
      rw [executed, record_rows_pure, check_evaluation_pure]
      refine ⟨terminal,Nat.zero_le _,?_,?_⟩
      · intro _ index
        have nonempty := Finset.card_pos.mpr ⟨index.val,index.property⟩
        omega
      · intro message salts canonical
        apply succeeds
        exact canonical.symm ▸ honest_input_empty oracle message input.positions salts empty
    · by_cases short : input.proof.length < 528*input.positions.card
      · obtain ⟨result,executed,failed⟩ := head.short input admitted short
        rw [executed, record_rows_pure, check_evaluation_pure]
        refine ⟨?_,Nat.zero_le _,?_,?_⟩
        · change result.exit ≠ .unfinished
          rw [failed]
          decide
        · intro impossible
          change result.exit = .success at impossible
          rw [failed] at impossible
          cases impossible
        · intro message salts canonical
          have required : 528*input.positions.card ≤ input.proof.length :=
            canonical.symm ▸ honest_input_records_fit oracle message input.positions salts
          omega
      · obtain ⟨state,cost,steps,cursor,memory,executeHeader⟩ :=
          head.positive input admitted empty (Nat.le_of_not_gt short)
        let fuel := 17179934720-cost
        have cardinal := checker_positions_bound input
        have enough : 472*input.positions.card+14840 ≤ fuel := by dsimp only [fuel]; omega
        have initialFrame : RecordInputFrame input 0 state := by
          intro word _ _
          exact congrFun memory (wordAddress word)
        have table := collected_table_empty oracle input state memory
        have body := checker_body_facts oracle input state cursor initialFrame table fuel enough
          (checker_cap_facts oracle input empty)
        have headerRun := executeHeader fuel
        rw [show cost+fuel=17179934720 by dsimp only [fuel]; omega] at headerRun
        rw [headerRun, bind_pure_comp, check_recorded_map]
        exact body.charge cost
  · exact checker_oversized_observation oracle input (Nat.lt_of_not_ge admitted)

theorem checker_facts_of_header (head : CheckerHeaderFacts) : Assembly.CheckerFacts :=
  checker_facts_of_observations (checker_complete_observation head)

end TwoPermutationPrototype.Checker
