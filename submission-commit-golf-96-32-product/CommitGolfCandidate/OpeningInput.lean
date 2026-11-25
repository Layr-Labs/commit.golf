import CommitGolfCandidate.Opening
import CommitGolf.Statements

/-! Connect the opening image's loop proofs to the trusted input loader. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem index_word (index : Index) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (BitVec.ofNat 8 (index.val / 2 ^ (8 * j))).toNat * 2 ^ (8 * j)) =
        BitVec.ofNat 64 index.val := by
  congr 1
  have bounded : index.val < 16777216 := index.isLt
  norm_num [Finset.sum_range_succ, BitVec.toNat_ofNat]
  omega

/-- Reading an aligned serialized index recovers exactly the corresponding element
of the sorted position set, for every trapdoor and position set. -/
theorem opening_input_index (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (bounded : offset < positions.card) :
    (submission.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (submission.layout.indices + 8 * offset)) =
        BitVec.ofNat 64 ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val := by
  let byteAt := fun address : Nat =>
    match (submission.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ address ∧ address < b.address + b.length)) with
    | some b => b.byteAt (address - b.address)
    | none => if dataBase (submission.image .opening) ≤ address then
        (submission.image .opening).data[address - dataBase (submission.image .opening)]?.getD 0
      else 0
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have addressNat : (BitVec.ofNat 64 (submission.layout.indices + 8 * offset)).toNat =
      submission.layout.indices + 8 * offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH,
      LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  change BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
    (byteAt ((BitVec.ofNat 64 (submission.layout.indices + 8 * offset)).toNat + j)).toNat *
      2 ^ (8 * j)) = _
  rw [addressNat]
  have bytes (j : Nat) (hj : j < 8) :
      byteAt (submission.layout.indices + 8 * offset + j) =
        BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (submission.layout.trapdoor ≤ submission.layout.indices + 8 * offset + j ∧
        submission.layout.indices + 8 * offset + j <
          submission.layout.trapdoor + (8 * submission.sizes.trapdoor + 7) / 8) := by
      norm_num [submission, candidate, layout, sizes, trapdoorBytes, LENGTH, LOG_LENGTH,
        LEAF_SIZE, DIGEST_BYTES]
      omega
    have inside : submission.layout.indices ≤ submission.layout.indices + 8 * offset + j ∧
        submission.layout.indices + 8 * offset + j <
          submission.layout.indices + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have selected : (submission.inputBuffers .opening (trapdoor, positions)).find?
        (fun b => decide (b.address ≤ submission.layout.indices + 8 * offset + j ∧
          submission.layout.indices + 8 * offset + j < b.address + b.length)) =
          some (positionsBuffer submission.layout.indices positions) := by
      simp only [Submission.inputBuffers, List.find?_cons, fixedBuffer]
      simp only [before, decide_false]
      simp only [positionsBuffer, inside]
      rfl
    simp only [byteAt, selected, positionsBuffer]
    have quotient : (submission.layout.indices + 8 * offset + j - submission.layout.indices) / 8 = offset := by omega
    have remainder : (submission.layout.indices + 8 * offset + j - submission.layout.indices) % 8 = j := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using bounded)]
  calc
    _ = BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
        (BitVec.ofNat 8 (((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val /
          2 ^ (8 * j))).toNat * 2 ^ (8 * j)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [bytes j (Finset.mem_range.mp hj)]
    _ = _ := index_word _


/-- Exact result of the submitted opening image on any valid ABI input. -/
def openingResult (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success, openingExitState (openingPositionState^[positions.card]
    (openingInitializedState (submission.initialState .opening (trapdoor, positions)))),
    1322 + 309 * positions.card, 0⟩

/-- The declared proof capacity: the 4096-byte cap and 576 bytes per position. -/
theorem submission_proof_capacity : submission.sizes.proof = 4096 + 576 * LENGTH := by
  norm_num [submission, candidate, sizes, proofBytes, capBytes, capCount, capLog, openingBytes,
    LENGTH, LOG_LENGTH]

/-- The setup and cap emission keep every input byte stored before the proof buffer. -/
theorem opening_initialized_memory (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (address : Word)
    (below : address.toNat < submission.layout.proof) :
    (openingInitializedState (submission.initialState .opening (trapdoor, positions))).getMem address =
      (submission.initialState .opening (trapdoor, positions)).getMem address := by
  apply opening_setup_memory_below
  · change (BitVec.ofNat 64 submission.layout.proof).toNat + 4096 ≤ MEMORY_BYTES
    decide
  · change address.toNat < (BitVec.ofNat 64 submission.layout.proof).toNat
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    exact below

set_option maxRecDepth 4096 in
private theorem opening_ready_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (submission.image .opening) (309 * positions.card + (10 + fuel))
      (openingInitializedState (submission.initialState .opening (trapdoor, positions))) true =
        pure ⟨.success, (openingResult trapdoor positions).state, 309 * positions.card + 13, 0⟩ := by
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have small : positions.card < 2 ^ 64 := by
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have counter : ready.getReg .x27 = BitVec.ofNat 64 positions.card :=
    (opening_setup_registers initial).2.2.2.1
  have heap : ready.getReg .x9 = BitVec.ofNat 64 submission.layout.trapdoor :=
    (opening_setup_registers initial).1
  have indexPointer : ready.getReg .x24 = BitVec.ofNat 64 submission.layout.indices :=
    (opening_setup_registers initial).2.1
  have outputPointer : ready.getReg .x25 = BitVec.ofNat 64 (submission.layout.proof + 4096) := by
    rw [(opening_setup_registers initial).2.2.1]
    change BitVec.ofNat 64 submission.layout.proof + BitVec.ofNat 64 4096 = _
    rw [BitVec.ofNat_add]
  have leaves : ready.getReg .x19 = 16777216 := (opening_setup_registers initial).2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 (submission.layout.trapdoor + 1610612736) := by
    rw [(opening_setup_registers initial).2.2.2.2.2.1]
    change BitVec.ofNat 64 submission.layout.trapdoor + BitVec.ofNat 64 1610612736 = _
    rw [BitVec.ofNat_add]
  have readyPC : 0 < positions.card → ready.pc = 4292 := by
    intro positive
    have nonzero : BitVec.ofNat 64 positions.card ≠ 0#64 := by
      intro zero
      have equal := congrArg BitVec.toNat zero
      change positions.card % 2 ^ 64 = 0 at equal
      rw [Nat.mod_eq_of_lt small] at equal
      omega
    simp [ready, openingInitializedState, MachineState.setPC, initialCount, nonzero]
  have indices : ∀ offset < positions.card,
      (ready.getMem (ready.getReg .x24 + BitVec.ofNat 64 (8 * offset))).toNat < 2 ^ 24 := by
    intro offset bounded
    have below : (BitVec.ofNat 64 (submission.layout.indices + 8 * offset)).toNat <
        submission.layout.proof := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      · norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH,
          LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
        omega
      · norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH,
          LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
        omega
    rw [indexPointer, ← BitVec.ofNat_add, opening_initialized_memory trapdoor positions _ below,
      opening_input_index trapdoor positions offset bounded]
    have indexBound : ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).val < 2 ^ 24 :=
      ((positions.sort (· ≤ ·))[offset]'(by simpa using bounded)).isLt
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact indexBound
  have indexSpace : (ready.getReg .x24).toNat + 8 * positions.card ≤ (ready.getReg .x25).toNat := by
    rw [indexPointer, outputPointer]
    norm_num [submission, candidate, layout, trapdoorBytes, LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have indexAligned : (ready.getReg .x24).toNat % 8 = 0 := by rw [indexPointer]; decide
  have saltBound : (ready.getReg .x18).toNat + 2 ^ 29 ≤ MEMORY_BYTES := by rw [salts]; decide
  have saltAligned : (ready.getReg .x18).toNat % 8 = 0 := by rw [salts]; decide
  have heapBound : (ready.getReg .x9).toNat + 3 * 2 ^ 29 ≤ MEMORY_BYTES := by rw [heap]; decide
  have heapAligned : (ready.getReg .x9).toNat % 8 = 0 := by rw [heap]; decide
  have outputBound : (ready.getReg .x25).toNat + 576 * positions.card ≤ MEMORY_BYTES := by
    rw [outputPointer]
    norm_num [submission, candidate, layout, trapdoorBytes, MEMORY_BYTES,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES]
    norm_num [LENGTH, LOG_LENGTH] at cardinal
    omega
  have outputAligned : (ready.getReg .x25).toNat % 8 = 0 := by rw [outputPointer]; decide
  have finishedPC : (openingPositionState^[positions.card] ready).pc = 4440 := by
    by_cases empty : positions.card = 0
    · simp [empty, ready, openingInitializedState, MachineState.setPC, initialCount]
    · exact (opening_positions_finished positions.card (by omega) ready counter).1
  change execute (submission.image .opening) (309 * positions.card + (10 + fuel)) ready true = _
  rw [opening_positions_loop positions.card cardinal ready counter readyPC indices indexSpace indexAligned
      leaves saltBound saltAligned heapBound heapAligned outputBound outputAligned,
    opening_exit _ finishedPC]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  rfl

private theorem opening_execution_extra (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute (submission.image .opening) (1309 + (309 * positions.card + (10 + fuel)))
      (submission.initialState .opening (trapdoor, positions)) true =
        pure (openingResult trapdoor positions) := by
  have heapPointer : (submission.initialState .opening (trapdoor, positions)).getReg .x12 =
      BitVec.ofNat 64 submission.layout.trapdoor := rfl
  have proofPointer : (submission.initialState .opening (trapdoor, positions)).getReg .x15 =
      BitVec.ofNat 64 submission.layout.proof := rfl
  rw [opening_setup _ rfl (by rw [heapPointer]; decide) (by rw [heapPointer]; decide)
    (by rw [proofPointer]; decide) (by rw [proofPointer]; decide), opening_ready_execution]
  simp only [pure_bind, Execution.charge, openingResult]
  congr 2
  omega

private theorem run_opening_eq_execute (candidate : Submission)
    (input : Input candidate.sizes .opening) :
    candidate.run .opening input = execute (candidate.image .opening) (candidate.steps .opening)
      (candidate.initialState .opening input) true := rfl

set_option maxRecDepth 4096 in
/-- Every actual opening input succeeds, with exact cycle and query counts.
This includes all position sets and arbitrary serialized trapdoors. -/
theorem opening_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.run .opening (trapdoor, positions) = pure (openingResult trapdoor positions) := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have steps : submission.steps .opening =
      1309 + (309 * positions.card + (10 + (submission.steps .opening - (1319 + 309 * positions.card)))) := by
    norm_num [submission, candidate, LENGTH, LOG_LENGTH] at cardinal ⊢
    omega
  exact (run_opening_eq_execute submission (trapdoor, positions)).trans
    ((congrArg (fun fuel => execute (submission.image .opening) fuel
      (submission.initialState .opening (trapdoor, positions)) true) steps).trans
        (opening_execution_extra trapdoor positions _))

/-- The machine returns the 4096-byte cap and 576 proof bytes per requested position. -/
theorem opening_result_length (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ((openingResult trapdoor positions).state.getReg .x11).toNat = 4096 + 576 * positions.card := by
  apply opening_exit_length
  · simpa [Index] using Finset.card_le_univ positions
  · rw [opening_positions_preserves_count, (opening_setup_registers _).2.2.2.2.2.2]
    rfl

/-- No opening is rejected or cut off, and its reported length fits the declared buffer. -/
theorem opening_result_succeeded (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.openingSucceeded (openingResult trapdoor positions) = true := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  simp only [Submission.openingSucceeded, opening_result_length, submission_proof_capacity]
  change (true && decide (4096 + 576 * positions.card ≤ 4096 + 576 * LENGTH)) = true
  simp only [Bool.true_and, decide_eq_true_eq]
  omega

/-- The scored batch's actual opening cost, proved for arbitrary trapdoors and sets. -/
theorem opening_batch_cycles (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (batch : positions.card = BATCH) :
    (openingResult trapdoor positions).cycles = 40874 := by
  simp [openingResult, batch, BATCH]


/-- Actual transmitted proof length, after the success and buffer-capacity checks. -/
theorem opening_proof_length (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    (submission.readProof (openingResult trapdoor positions)).length = 4096 + 576 * positions.card := by
  simp [Submission.readProof, opening_result_succeeded, opening_result_length]

private theorem scheme_opening_eq_map (candidate : Submission)
    (trapdoor : BitVec (8 * candidate.sizes.trapdoor)) (positions : Positions) :
    candidate.scheme.opening trapdoor positions =
      candidate.readProof <$> candidate.run .opening (trapdoor, positions) := rfl

/-- The scheme's opening operation is exactly the successful machine output. -/
theorem opening_scheme_execution (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    submission.scheme.opening trapdoor positions =
      pure (submission.readProof (openingResult trapdoor positions)) := by
  rw [scheme_opening_eq_map, opening_execution]
  simp

private theorem oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

/-- Opening termination in the same probabilistic form required by the certificate. -/
theorem opening_termination (oracle : Oracle)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$> (oracle.run (submission.run .opening (trapdoor, positions))))) = 1 := by
  rw [opening_execution, oracle_run_pure]
  simp [openingResult]

/-- The certificate's proof-size requirement follows from the actual machine image,
even before the commitment and checking programs' correctness proofs are supplied. -/
theorem submission_proof_size : submission.scheme.ProofSize 77824 := by
  intro oracle message positions batch
  unfold Scheme.honest
  apply le_antisymm (prEvent_le_one _)
  apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
  rintro ⟨⟨root, trapdoor⟩, calls⟩ _
  dsimp only
  rw [opening_scheme_execution trapdoor positions, oracle_run_pure]
  simp [opening_proof_length trapdoor positions, batch, BATCH]


/-- Exact resources for a scored opening, expressed through the same oracle runner
used by the certificate: 40,874 cycles, zero queries, and 77,824 proof bytes. -/
theorem opening_batch_resources (oracle : Oracle)
    (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card = BATCH) :
    (prEvent ((fun result => result.1.cycles = 40874 ∧ result.2 = 0 ∧
      (submission.readProof result.1).length = 77824) <$> (oracle.run (submission.run .opening (trapdoor, positions))))) = 1 := by
  rw [opening_execution, oracle_run_pure]
  simp [opening_batch_cycles trapdoor positions batch, opening_proof_length trapdoor positions,
    batch, BATCH]

end CommitGolfCandidate
