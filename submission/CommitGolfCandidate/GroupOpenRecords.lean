import CommitGolfCandidate.GroupOpenRecordsAPI

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (sortedIndex RecordMarks)

attribute [local irreducible] execute

private theorem records_cost_next (size ordinal count : Nat) (limit : ordinal+(count+1) ≤ size) :
    recordsCost size ordinal (count+1) =
      recordCost (decide (ordinal+1=size))+recordsCost size (ordinal+1) count := by
  have sum : ordinal+(count+1)=ordinal+1+count := by omega
  by_cases last : ordinal+1=size
  · have empty : count = 0 := by omega
    subst count
    simp [recordsCost, recordCost, last]
  · by_cases finished : ordinal+(count+1)=size
    · have now : 0<count+1 ∧ ordinal+(count+1)=size := ⟨by omega, finished⟩
      have later : 0<count ∧ ordinal+1+count=size := ⟨by omega, by omega⟩
      simp only [recordsCost, ite_eq_left now, ite_eq_left later, recordCost,
        decide_eq_false last, Bool.false_eq_true, ite_false]
      omega
    · have now : ¬ (0<count+1 ∧ ordinal+(count+1)=size) := fun h => finished h.2
      have later : ¬ (0<count ∧ ordinal+1+count=size) := by omega
      simp only [recordsCost, ite_eq_right now, ite_eq_right later, recordCost,
        decide_eq_false last, Bool.false_eq_true, ite_false]
      omega

theorem same_input_byte {before after : MachineState} (unchanged : SameOpeningInput before after)
    (address : Nat) (above : trapdoorBase ≤ address) (below : address < proofBase) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have upper : aligned.toNat ≤ address := by
    unfold aligned alignToDword
    have limit : proofBase < 2^64 := by decide
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)]
    exact Nat.and_le_left
  have lower : trapdoorBase ≤ aligned.toNat := by
    apply aligned_dword_above trapdoorBase address (by decide) above
    have : proofBase+8 ≤ 2^64 := by decide
    omega
  have stable := unchanged aligned.toNat lower (by omega) (aligned_word_mod _)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at stable
  change extractByte (after.getMem aligned) _ = _
  rw [stable]
  rfl

theorem same_input_half {before after : MachineState} (unchanged : SameOpeningInput before after)
    (address : Nat) (above : trapdoorBase ≤ address) (below : address+2 ≤ proofBase) :
    after.getHalfword (BitVec.ofNat 64 address) = before.getHalfword (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have limit : proofBase+8 ≤ 2^64 := by decide
  have upper : aligned.toNat ≤ address := by
    unfold aligned alignToDword
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)]
    exact Nat.and_le_left
  have lower : trapdoorBase ≤ aligned.toNat :=
    aligned_dword_above trapdoorBase address (by decide) above (by omega)
  have stable := unchanged aligned.toNat lower (by omega) (aligned_word_mod _)
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at stable
  change extractHalfword (after.getMem aligned) _ = extractHalfword (before.getMem aligned) _
  rw [stable]

private theorem collected_record (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal : Nat)
    (present : ordinal < positions.card) (start : RecordBoundary s trapdoor positions before ordinal)
    (step : OneRecord s trapdoor positions before after ordinal present)
    (earlier : CompletedRecords s trapdoor positions before ordinal) :
    CompletedRecords s trapdoor positions after (ordinal+1) := by
  intro prior priorPresent first
  let index := sortedIndex positions prior priorPresent
  have len : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have baseOrder : trapdoorBase ≤ proofBase := by decide
  have heapSource (level byte : Nat) (hb : byte < 32) :
      trapdoorBase ≤ siblingAddress index level+byte ∧ siblingAddress index level+byte+2 ≤ proofBase := by
    have bound := upper_swap_bound index level
    have heapEnd := heap_before_nonces
    have tapeEnd := nonces_end_at_indices
    have order := indices_before_records
    unfold siblingAddress
    omega
  by_cases current : prior = ordinal
  · subst prior
    obtain rfl : priorPresent = present := rfl
    refine ⟨?_, ?_, ?_⟩
    · intro byte hb
      have low := first_source_above index byte
      have high := first_source_before index byte hb
      exact (step.nonce byte hb).trans (same_input_byte start.input _ low high)
    · intro level hl byte hb
      have narrow := plain_width_le level
      have wide := sibling_width_le level
      have ⟨low, high⟩ := heapSource level byte (by omega)
      exact (step.sibling level hl byte hb).trans (same_input_byte start.input _ low
        (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) high))
    · intro k hk b hb
      rw [step.fold k hk b hb]
      have ⟨l1, h1⟩ := heapSource (6+k) 28 (by omega)
      have ⟨l2, h2⟩ := heapSource 13 28 (by omega)
      rw [same_input_half start.input _ l1 h1, same_input_half start.input _ l2 h2]
  · have older : prior < ordinal := by omega
    obtain ⟨oldNonce, oldPath, oldFold⟩ := earlier prior priorPresent older
    have limit := all_record_ends_fit ordinal (by omega)
    have memory : recordBase ordinal ≤ MEMORY_BYTES := by
      unfold recordBase recordBytes at *
      omega
    have earlierThan : recordBase (prior+1) ≤ recordBase ordinal := by
      unfold recordBase recordBytes
      omega
    refine ⟨?_, ?_, ?_⟩
    · intro byte hb
      have low : trapdoorBase ≤ recordBase prior+byte := by unfold recordBase; omega
      have high : recordBase prior+byte < recordBase ordinal := by unfold recordBase recordBytes; omega
      exact (step.frame _ (by omega) low (Or.inl high)).trans (oldNonce byte hb)
    · intro level hl byte hb
      have fit := (all_sibling_copies_fit index prior level (by omega) hl).2.2.2
      have narrow := plain_width_le level
      have inPrior : siblingDestination prior level+byte < recordBase (prior+1) := by
        have stepOrder := destination_mono prior (show level+1 ≤ 14 by omega)
        rw [record_end] at stepOrder
        have successor : siblingDestination prior (level+1) =
            siblingDestination prior level + siblingWidth level := by
          simp only [siblingDestination, sibling_offset_next level hl, Nat.add_assoc]
        omega
      exact (step.frame _ (by omega) (by unfold siblingDestination recordBase; omega)
        (Or.inl (by omega))).trans (oldPath level hl byte hb)
    · intro k hk b hb
      have inPrior : siblingDestination prior (6+k)+28+b < recordBase (prior+1) := by
        have stepOrder := destination_mono prior (show 7+k ≤ 14 by omega)
        rw [record_end] at stepOrder
        have successor : siblingDestination prior (6+k+1) =
            siblingDestination prior (6+k) + siblingWidth (6+k) := by
          unfold siblingDestination
          rw [sibling_offset_next (6+k) (by omega)]
          omega
        have width : siblingWidth (6+k) = 30 := by unfold siblingWidth; rw [if_neg (by omega), if_pos (by omega)]
        rw [show 6+k+1 = 7+k by omega] at successor
        omega
      exact (step.frame _ (by omega) (by unfold siblingDestination recordBase; omega)
        (Or.inl (by omega))).trans (oldFold k hk b hb)

theorem execute_records_from_step (execute_record : RecordExecute) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal count : Nat) (limit : ordinal+count ≤ positions.card)
    (start : RecordBoundary s trapdoor positions state ordinal)
    (marks : RecordMarks positions state ordinal)
    (bytes : CompletedRecords s trapdoor positions state ordinal) :
    RecordsFinished s trapdoor positions state (runRecords positions.card ordinal count state) ordinal count := by
  induction count generalizing ordinal state with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro fuel coins
      simp [runRecords, recordsCost, Execution.charge]
    · simpa only [runRecords, Nat.add_zero] using start
    · simpa only [runRecords, Nat.add_zero] using marks
    · simpa only [runRecords, Nat.add_zero] using bytes
  | succ count ih =>
    have present : ordinal < positions.card := by omega
    let next := runRecord state (decide (ordinal+1=positions.card))
    have step := execute_record s layout trapdoor positions state ordinal present start
    have withMark : RecordMarks positions next (ordinal+1) := by
      intro node bounded
      rw [step.marks node bounded, marks node bounded, Opening.groups_before_next positions ordinal present]
      by_cases same : node = Sampling.capGroup (sortedIndex positions ordinal present)
      · simp [same]
      · simp [List.mem_append, same]
    have withBytes := collected_record s trapdoor positions state next ordinal present start step bytes
    have rest := ih next (ordinal+1) (by omega) step.next withMark withBytes
    have shift : ordinal+(count+1)=ordinal+1+count := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [records_cost_next _ _ _ limit]
      exact step.run.next rest.run
    · rw [shift]
      exact rest.boundary
    · rw [shift]
      exact rest.marks
    · rw [shift]
      exact rest.bytes

end TwoPermutationPrototype.GroupedOpening
