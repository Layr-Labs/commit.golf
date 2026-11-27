import CommitGolfCandidate.QuadCheckPentaBody
import CommitGolfCandidate.QuadHeaderAssembly
import CommitGolfCandidate.QuadBindingPaths
import CommitGolfCandidate.PentaCapFacts
import CommitGolfCandidate.HybWrapTail

/-! Checker facts for compact hybrid proofs. The wrapper (`HybWrap`) jumps to the donor's reject for
every admitted proof whose length is not `HybWrap.compactLength`, without oracle calls; for no
positions it hands the submitted input to the donor's empty exit; otherwise it makes the 68 upper-node
calls and returns to word 1 with the expanded input in memory, and the donor header and record body
run on the expanded input unchanged. Binding transfers because expansion keeps the commitment,
positions and values; honest acceptance transfers through `expand_cap_check_input`. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map)
open TwoPermutationPrototype.QuadCertificate (capCheckInput cap_check_input_length expand_cap_check_input
  CapCheckerFacts)
open TwoPermutationPrototype.HybWrap (expandInput Obs wrap_positive wrap_empty wrap_reject compactLength)

set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

attribute [local irreducible] execute checkEvaluation

/-- The donor's observation facts, with honest acceptance stated for the compact honest input. -/
structure CapObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 14*input.positions.card + (if input.positions.card = 0 then 0 else 68)
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    PentaOpening oracle index.val (input.values index) input.commitment observed.1.2
  honest : ∀ message salts, input = capCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success

/-- Facts of the donor checker on the expanded input, behind the 68 recorded hash calls, are
compact facts on the submitted input. -/
theorem cap_facts_of_expanded {oracle : Oracle} {input : CheckInput}
    (nonempty : input.positions.card ≠ 0)
    {observed : (Execution × List PublicRow) × Nat} (rows : List PublicRow) (cycles : Nat)
    (facts : CheckerObservationFacts oracle (expandInput oracle input) observed) :
    CapObservationFacts oracle input ((observed.1.1.charge cycles 68, rows ++ observed.1.2), 68 + observed.2) where
  terminates := by
    have := facts.terminates
    simpa [Execution.charge] using this
  queries := by
    have := facts.queries
    change 68 + observed.2 ≤ _
    rw [if_neg nonempty]
    change observed.2 ≤ 14*input.positions.card at this
    omega
  paths := by
    intro accepted index
    have h := facts.paths (by simpa [Execution.charge] using accepted) index
    exact h.mono (fun row member => List.mem_append_right _ member)
  honest := by
    intro message salts canonical
    have h := facts.honest message salts (by
      have e := expand_cap_check_input oracle message input.positions salts
      rw [← canonical] at e
      exact e)
    simpa [Execution.charge] using h

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

private theorem compact_length_admitted (positions : Positions) : compactLength positions ≤ 41204842496 := by
  have card : positions.card ≤ 16777216 := by
    have : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact this
  unfold compactLength
  split <;> omega

private theorem raw_reject (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 41204842496) (nonempty : input.positions.card ≠ 0)
    (wrong : input.proof.length ≠ 848*input.positions.card+8608) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨result, run, failed⟩ := wrap_reject oracle input (by omega) nonempty wrong (1099511627776 - 12)
  unfold rawObserved
  rw [show 1099511627776 = 12 + (1099511627776 - 12) by rfl]
  erw [run]
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
    unfold compactLength at h
    rw [if_neg nonempty] at h
    exact (wrong h).elim

private theorem raw_empty (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 41204842496) (empty : input.positions.card = 0) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨t, cycles, obs, start⟩ := wrap_empty oracle input empty
  obtain ⟨result, run, accepts, finished, calls⟩ := wrapped_header_empty start empty (by omega) (1099511627776 - 6 - 7)
  have whole := obs (7 + (1099511627776 - 6 - 7))
  rw [run, record_rows_pure, check_evaluation_pure] at whole
  unfold rawObserved
  rw [show 1099511627776 = 6 + (7 + (1099511627776 - 6 - 7)) by rfl]
  erw [whole]
  refine ⟨?_, by simp, ?_, ?_⟩
  · change (result.charge cycles 0).exit ≠ .unfinished
    exact finished
  · intro _ index
    have nonempty := Finset.card_pos.mpr ⟨index.val, index.property⟩
    omega
  · intro message salts canonical
    have h := cap_check_input_length oracle message input.positions salts
    rw [← canonical] at h
    unfold compactLength at h
    rw [if_pos empty, empty] at h
    exact accepts.mpr (by simpa using h)

private theorem observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact body.charge cycles

theorem expand_virt (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < (expandInput oracle input).positions.card) :
    recordVirt (expandInput oracle input) ordinal =
      virtIndex (TwoPermutationPrototype.Quad.Honest.honestIndex (expandInput oracle input).positions ordinal
        present).val.val := by
  have small := checker_positions_bound input
  have pres : ordinal < input.positions.card := present
  unfold recordVirt siblingWord
  rw [show 1350566927+195*ordinal-1 = PentaWrap.proofWord + 195*ordinal + 2 by unfold PentaWrap.proofWord; omega,
    HybWrap.expanded_loader HybWrap.loader_layout oracle input _ (by unfold PentaWrap.proofWord; omega),
    if_neg (by omega), if_pos (by omega), show PentaWrap.proofWord + 195*ordinal + 2 - PentaWrap.proofWord = 195*ordinal+2
      by omega, HybWrap.expanded_virt, HybWrap.honest_index_sorted _ _ present]
  show _ = virtIndex (sortedIndex input.positions ordinal)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := virt_index_lt (sortedIndex input.positions ordinal)
  have : (5:Nat) ^ PENTA_LEVELS < 2^64 := by decide
  omega

private theorem raw_positive (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 41204842496) (nonempty : input.positions.card ≠ 0)
    (exact : input.proof.length = 848*input.positions.card+8608) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  let ext := expandInput oracle input
  have cardinal := checker_positions_bound input
  obtain ⟨F, cycles, rows, obs, start, frameF⟩ := wrap_positive oracle input (by omega) nonempty exact
  have extLen : ext.proof.length = 1560*input.positions.card := HybWrap.expand_proof_length _ _ _
  have sameCard : ext.positions.card = input.positions.card := rfl
  obtain ⟨state, cursor, memory, header⟩ := wrapped_header_positive start nonempty
    ⟨by rw [extLen]; exact le_rfl, by rw [extLen]; omega⟩
  have proofFits : ProofWithin ext := by
    refine ⟨by rw [extLen]; exact le_rfl, ?_⟩
    rw [extLen]
    change 1560*input.positions.card ≤ 2456*2^24
    omega
  have frame : RecordInputFrame ext 0 state := by
    intro word small used
    have view : memoryView state word = memoryView F word := by
      unfold memoryView MachineState.getMem; rw [memory]
    rw [view]
    apply frameF word small
    right
    rcases used with ⟨first, _⟩ | ⟨first, _⟩ | first
    · omega
    · unfold checkIndexWord at first
      omega
    · unfold checkSourceWord at first
      omega
  obtain ⟨rest, hrest⟩ : ∃ rest, rest = 1099511627776 - (3569 + 754*input.positions.card) - 21 := ⟨_, rfl⟩
  have enough : 2048*ext.positions.card+5 ≤ rest := by
    change 2048*input.positions.card+5 ≤ _
    omega
  have body := checker_body_facts oracle ext state proofFits cursor frame
    (fun ordinal present => expand_virt oracle input ordinal present) rest enough
  have afterHeader := observation_hop oracle ext F state 21 24 rest header body
  have hashed := cap_facts_of_expanded nonempty rows cycles afterHeader
  have whole := obs (21 + rest)
  unfold rawObserved
  rw [show 1099511627776 = (3569 + 754*input.positions.card) + (21 + rest) by omega]
  erw [whole]
  exact hashed

private theorem raw_checker_observation (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 41204842496) :
    CapObservationFacts oracle input (rawObserved oracle input) := by
  by_cases empty : input.positions.card = 0
  · exact raw_empty oracle input fits empty
  · by_cases exact : input.proof.length = 848*input.positions.card+8608
    · exact raw_positive oracle input fits empty exact
    · exact raw_reject oracle input fits empty exact

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
      exact (admitted (h ▸ compact_length_admitted input.positions)).elim

theorem cap_checker_facts_of_observations (s : Submission)
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      CapObservationFacts oracle input (checkObservation s oracle input)) :
    CapCheckerFacts s := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by split <;> omega), ?_, ?_⟩
  · apply binding_of_penta_trace s ?_
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by split at count <;> omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts
    exact (checked oracle (capCheckInput oracle message positions salts)).honest message salts rfl

end TwoPermutationPrototype.Quad.Checker
