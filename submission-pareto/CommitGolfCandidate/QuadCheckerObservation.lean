import CommitGolfCandidate.QuadCheckPentaBody
import CommitGolfCandidate.QuadHeaderAssembly
import CommitGolfCandidate.QuadBindingPaths
import CommitGolfCandidate.PentaCapFacts
import CommitGolfCandidate.PentaWrapCheckImage

/-! Checker facts for cap proofs. The wrapper (`PentaWrapRunC`) rejects every admitted proof whose
length is not `PentaWrap.capLength`, without oracle calls; otherwise it returns to word 1 with the expanded
input in memory, and the donor header and record body run on the expanded input unchanged.
Binding transfers because expansion keeps the commitment, positions and values; honest
acceptance transfers through `expand_cap_check_input`. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map)
open TwoPermutationPrototype.QuadCertificate (capCheckInput cap_check_input_length expand_cap_check_input
  CapCheckerFacts)
open TwoPermutationPrototype.PentaWrap (expandInput WrapExit WrapLayout wrap_accept wrap_reject TBW
  view_of_mem expand_proof_length)

set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

attribute [local irreducible] execute checkEvaluation

/-- The donor's observation facts, with honest acceptance stated for the cap honest input. -/
structure CapObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 25*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    PentaOpening oracle index.val (input.values index) input.commitment observed.1.2
  honest : ∀ message salts, input = capCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success

/-- Facts of the donor checker on the expanded input are cap facts on the submitted input. -/
theorem cap_facts_of_expanded {oracle : Oracle} {input : CheckInput}
    {observed : (Execution × List PublicRow) × Nat}
    (facts : CheckerObservationFacts oracle (expandInput input) observed) :
    CapObservationFacts oracle input observed where
  terminates := facts.terminates
  queries := facts.queries
  paths := facts.paths
  honest := by
    intro message salts canonical
    apply facts.honest message salts
    have h := expand_cap_check_input oracle message input.positions salts
    rw [← canonical] at h
    exact h

theorem loader_wrap_layout : WrapLayout loaderReference := ⟨rfl, rfl⟩

private theorem loader_hop {s t : MachineState} {a b : Nat}
    (hop : PentaWrap.Hop (loaderReference.image .check) s t a b) : Hop s t a b := hop

private theorem header_start (input : CheckInput) (state : MachineState)
    (exit : WrapExit loaderReference input state) : HeaderStart (expandInput input) state :=
  ⟨exit.pc, exit.factor, exit.regs, expand_proof_length _ _⟩

private theorem observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ loaderReference.sizes.proof) :
    checkObservation loaderReference oracle input =
      checkEvaluation oracle (recordRows
        (execute packedImage 1099511627776 (loaderReference.initialState .check input) false)) := by
  unfold checkObservation
  erw [check_run_admitted input admitted]

private theorem observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : loaderReference.sizes.proof < input.proof.length) :
    checkObservation loaderReference oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [check_run_oversized input oversized]
  rw [record_rows_pure,check_evaluation_pure]

private abbrev rawObserved (oracle : Oracle) (input : CheckInput) :=
  checkEvaluation oracle (recordRows
    (execute packedImage 1099511627776 (loaderReference.initialState .check input) false))

private theorem cap_length_admitted (positions : Positions) : PentaWrap.capLength positions ≤ 23890755584 := by
  have card : positions.card ≤ 16777216 := by
    have : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact this
  unfold PentaWrap.capLength
  split <;> omega

private theorem raw_reject (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 23890755584) (wrong : input.proof.length ≠ PentaWrap.capLength input.positions) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨steps, result, bound, failed, _, runs⟩ := wrap_reject loader_wrap_layout quad_wrap_image input fits wrong
  have run : execute packedImage 1099511627776 (loaderReference.initialState .check input) false = pure result := by
    have h : execute packedImage (steps + (1099511627776 - steps)) (loaderReference.initialState .check input) false =
        pure result := runs (1099511627776 - steps)
    rwa [show steps + (1099511627776 - steps) = 1099511627776 by omega] at h
  unfold rawObserved
  rw [run, record_rows_pure, check_evaluation_pure]
  refine ⟨?_, Nat.zero_le _, ?_, ?_⟩
  · change result.exit ≠ .unfinished
    rw [failed]
    decide
  · intro impossible
    change result.exit = .success at impossible
    rw [failed] at impossible
    cases impossible
  · intro message salts canonical
    have h := cap_check_input_length oracle message input.positions salts
    rw [← canonical] at h
    exact (wrong h).elim

private theorem raw_empty (oracle : Oracle) (input : CheckInput)
    (exact : input.proof.length = PentaWrap.capLength input.positions) (empty : input.positions.card = 0) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨final, steps, cycles, bound, hop, exit⟩ := wrap_accept loader_wrap_layout quad_wrap_image input exact
  have start := header_start input final exit
  rw [empty] at bound
  obtain ⟨result, run, success, _⟩ := wrapped_header_empty start empty (1099511627776 - steps - 7)
  have whole : execute packedImage 1099511627776 (loaderReference.initialState .check input) false =
      pure (result.charge cycles 0) := by
    have h := loader_hop hop (7 + (1099511627776 - steps - 7))
    rw [run, show steps + (7 + (1099511627776 - steps - 7)) = 1099511627776 by omega] at h
    simpa only [pure_bind] using h
  unfold rawObserved
  rw [whole, record_rows_pure, check_evaluation_pure]
  refine ⟨?_, Nat.zero_le _, ?_, ?_⟩
  · change result.exit ≠ .unfinished
    rw [success]
    decide
  · intro _ index
    have nonempty := Finset.card_pos.mpr ⟨index.val, index.property⟩
    omega
  · intro _ _ _
    exact success

private theorem observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact body.charge cycles

private theorem raw_positive (oracle : Oracle) (input : CheckInput)
    (exact : input.proof.length = PentaWrap.capLength input.positions) (nonempty : input.positions.card ≠ 0) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨final, steps, cycles, bound, hop, exit⟩ := wrap_accept loader_wrap_layout quad_wrap_image input exact
  have start := header_start input final exit
  obtain ⟨state, cursor, memory, header⟩ := wrapped_header_positive start nonempty
  have cardinal := checker_positions_bound input
  have fits : ProofWithin (expandInput input) := by
    refine ⟨by rw [start.exact], ?_⟩
    rw [start.exact]
    change 1424*input.positions.card ≤ 1424*2^24
    omega
  have frame : RecordInputFrame (expandInput input) 0 state := by
    intro word small used
    rw [view_of_mem memory]
    apply exit.memory word small
    right
    have card : (expandInput input).positions.card ≤ 16777216 := cardinal
    rcases used with ⟨first, _⟩ | ⟨first, _⟩ | first
    · unfold TBW
      omega
    · unfold checkIndexWord at first
      unfold TBW
      omega
    · unfold checkSourceWord at first
      unfold TBW
      omega
  have enough : 2048*(expandInput input).positions.card+5 ≤ 1099511627776 - steps - 21 := by
    change 2048*input.positions.card+5 ≤ _
    omega
  have body := checker_body_facts oracle (expandInput input) state fits cursor frame _ enough
  have afterWrap := observation_hop oracle (expandInput input) final state 21 24 _ header body
  have whole := observation_hop oracle (expandInput input) (loaderReference.initialState .check input) final
    steps cycles _ (loader_hop hop) afterWrap
  rw [show steps + (21 + (1099511627776 - steps - 21)) = 1099511627776 by omega] at whole
  exact cap_facts_of_expanded whole

private theorem raw_checker_observation (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 23890755584) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  by_cases exact : input.proof.length = PentaWrap.capLength input.positions
  · by_cases empty : input.positions.card = 0
    · exact raw_empty oracle input exact empty
    · exact raw_positive oracle input exact empty
  · exact raw_reject oracle input fits exact

theorem checker_complete_observation (oracle : Oracle) (input : CheckInput) :
    CapObservationFacts oracle input (checkObservation loaderReference oracle input) := by
  by_cases admitted : input.proof.length ≤ loaderReference.sizes.proof
  · rw [observation_admitted oracle input admitted]
    exact raw_checker_observation oracle input admitted
  · rw [observation_oversized oracle input (Nat.lt_of_not_ge admitted)]
    refine ⟨by decide,Nat.zero_le _,?_,?_⟩
    · intro impossible
      cases impossible
    · intro message salts canonical
      have h := cap_check_input_length oracle message input.positions salts
      rw [← canonical] at h
      exact (admitted (h ▸ cap_length_admitted input.positions)).elim

theorem cap_checker_facts_of_observations (s : Submission)
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      CapObservationFacts oracle input (checkObservation s oracle input)) :
    CapCheckerFacts s := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by omega), ?_, ?_⟩
  · apply binding_of_penta_trace s ?_
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts
    exact (checked oracle (capCheckInput oracle message positions salts)).honest message salts rfl

end TwoPermutationPrototype.Quad.Checker
