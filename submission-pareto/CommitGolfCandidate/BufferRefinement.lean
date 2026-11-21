import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.OpeningInput

/-! Concrete input-buffer contents for the submitted images. These are properties of
actual loader memory, not assumptions about a separate abstract implementation. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem positions_card_bound (positions : Positions) : positions.card ≤ 2^24 := by
  have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  exact bound

/-- A commitment input contains the selected message leaf byte-for-byte. -/
theorem commit_input_byte (message : Message) (index : Index) (offset : Nat)
    (inside : offset < 256) :
    (submission.initialState .commit message).getByte
      (BitVec.ofNat 64 (submission.layout.message + 256*index.val + offset)) =
        (message index).extractLsb' (8*offset) 8 := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [initial_input_byte submission .commit message _ (by change 4096 + 256*index.val + offset < 2^64; omega)]
  have selected : submission.layout.message ≤ submission.layout.message + 256*index.val + offset ∧
      submission.layout.message + 256*index.val + offset <
        submission.layout.message + LENGTH * (LEAF_SIZE/8) := by
    change 4096 ≤ 4096+256*index.val+offset ∧ 4096+256*index.val+offset < 4096+16777216*256
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, messageBuffer,
    selected, and_self, decide_true]
  have quotient : (submission.layout.message + 256*index.val + offset -
      submission.layout.message) / (LEAF_SIZE/8) = index.val := by change _ / 256 = _; omega
  have remainder : (submission.layout.message + 256*index.val + offset -
      submission.layout.message) % (LEAF_SIZE/8) = offset := by change _ % 256 = _; omega
  simp only [quotient, remainder, index.isLt, dite_true]

/-- The eight compression blocks consumed by the commitment leaf loop are exactly
that leaf's eight 256-bit slices. -/
theorem commit_input_block (message : Message) (index : Index) (block : Nat)
    (inside : block < 8) :
    readBuffer (submission.initialState .commit message)
      (submission.layout.message + 256*index.val + 32*block) 32 =
        (message index).extractLsb' (256*block) 256 := by
  have decoded := read_serialized_slice (submission.initialState .commit message) (message index)
    (submission.layout.message + 256*index.val + 32*block) (32*block) 32 (by
      intro j hj
      simpa only [Nat.add_assoc] using commit_input_byte message index (32*block+j) (by omega))
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using decoded

/-- Private state is loaded without modification before opening. -/
theorem opening_input_byte (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (inside : offset < submission.sizes.trapdoor) :
    (submission.initialState .opening (trapdoor, positions)).getByte
      (BitVec.ofNat 64 (submission.layout.trapdoor+offset)) =
        trapdoor.extractLsb' (8*offset) 8 := by
  have size : submission.sizes.trapdoor = 1610612736 := rfl
  rw [initial_input_byte submission .opening (trapdoor, positions) _ (by change 4294971424+offset < 2^64; omega)]
  have selected : submission.layout.trapdoor ≤ submission.layout.trapdoor+offset ∧
      submission.layout.trapdoor+offset < submission.layout.trapdoor + (8*submission.sizes.trapdoor+7)/8 := by
    rw [size]
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    selected, and_self, decide_true, Nat.add_sub_cancel_left]

/-- The opening machine reads exact digest slices from its serialized trapdoor. -/
theorem opening_input_digest (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) (offset : Nat) (inside : offset+32 ≤ submission.sizes.trapdoor) :
    readBuffer (submission.initialState .opening (trapdoor, positions))
      (submission.layout.trapdoor+offset) 32 = trapdoor.extractLsb' (8*offset) 256 := by
  apply read_serialized_slice
  intro j hj
  simpa only [Nat.add_assoc] using opening_input_byte trapdoor positions (offset+j) (by omega)

/-- Passing the actual commitment memory through the serialized trapdoor preserves
all tree nodes and salts read by opening. -/
theorem opening_input_roundtrip (state : MachineState) (positions : Positions) (offset : Nat)
    (inside : offset+32 ≤ submission.sizes.trapdoor) :
    readBuffer (submission.initialState .opening
      (readBuffer state submission.layout.trapdoor submission.sizes.trapdoor, positions))
      (submission.layout.trapdoor+offset) 32 =
        readBuffer state (submission.layout.trapdoor+offset) 32 := by
  rw [opening_input_digest _ positions offset inside,
    read_buffer_slice _ _ _ _ _ inside]

/-- The checker sees exactly the submitted commitment. -/
theorem check_input_commitment (input : CheckInput) :
    readBuffer (submission.initialState .check input) submission.layout.commitment 32 =
      input.commitment := by
  have decoded := read_serialized_slice (submission.initialState .check input) input.commitment
    submission.layout.commitment 0 32 (by
      intro j hj
      rw [initial_input_byte submission .check input _ (by change 4294971392+j < 2^64; omega)]
      have selected : submission.layout.commitment ≤ submission.layout.commitment+j ∧
          submission.layout.commitment+j < submission.layout.commitment+(DIGEST_BITS+7)/8 := by
        change _ ≤ _ ∧ _ < submission.layout.commitment+32
        omega
      simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
        selected, and_self, decide_true, Nat.add_sub_cancel_left, Nat.zero_add])
  exact decoded.trans BitVec.extractLsb'_eq_self

/-- Every proof byte accepted by the ABI is loaded at the proof buffer address. -/
theorem check_input_proof_byte (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) (offset : Nat)
    (inside : offset < input.proof.length) :
    (submission.initialState .check input).getByte
      (BitVec.ofNat 64 (submission.layout.proof+offset)) = input.proof[offset] := by
  have cardinal := positions_card_bound input.positions
  rw [initial_input_byte submission .check input _ (by
    change 10334769184+offset < 2^64
    change input.proof.length ≤ 13421772800 at valid
    omega)]
  have outsideRoot : ¬ (submission.layout.commitment ≤ submission.layout.proof+offset ∧
      submission.layout.proof+offset < submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 10334769184+offset ∧ 10334769184+offset < 4294971424)
    omega
  have outsideIndices : ¬ (submission.layout.indices ≤ submission.layout.proof+offset ∧
      submission.layout.proof+offset < submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 10334769184+offset ∧ 10334769184+offset < 5905584160+8*input.positions.card)
    omega
  have outsideValues : ¬ (submission.layout.values ≤ submission.layout.proof+offset ∧
      submission.layout.proof+offset < submission.layout.values+(LEAF_SIZE/8)*input.positions.card) := by
    change ¬ (6039801888 ≤ 10334769184+offset ∧ 10334769184+offset < 6039801888+256*input.positions.card)
    omega
  have selected : submission.layout.proof ≤ submission.layout.proof+offset ∧
      submission.layout.proof+offset < submission.layout.proof+input.proof.length := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, outsideValues, decide_false, selected, and_self, decide_true,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem inside, Option.getD_some]

/-- Reading a proof digest is the little-endian decoding of exactly those 32 bytes. -/
theorem check_input_proof_digest (input : CheckInput)
    (valid : input.proof.length ≤ submission.sizes.proof) (offset : Nat)
    (inside : offset+32 ≤ input.proof.length) :
    readBuffer (submission.initialState .check input) (submission.layout.proof+offset) 32 =
      BitVec.ofNat 256 (∑ j ∈ Finset.range 32,
        (input.proof[offset+j]?.getD 0).toNat * 2^(8*j)) := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat 256)
  apply Finset.sum_congr rfl
  intro j hj
  have bounded : offset+j < input.proof.length := by have := Finset.mem_range.mp hj; omega
  rw [Nat.add_assoc, check_input_proof_byte input valid (offset+j) bounded,
    List.getElem?_eq_getElem bounded, Option.getD_some]

/-- The checker receives the caller's leaf values in the ABI's sorted order. -/
theorem check_input_value_byte (input : CheckInput) (ordinal offset : Nat)
    (present : ordinal < input.positions.card) (inside : offset < 256) :
    (submission.initialState .check input).getByte
      (BitVec.ofNat 64 (submission.layout.values+256*ordinal+offset)) =
      (input.values ((input.positions.attach.sort (· ≤ ·))[ordinal]'(by
        simpa using present))).extractLsb' (8*offset) 8 := by
  have cardinal := positions_card_bound input.positions
  rw [initial_input_byte submission .check input _ (by
    change 6039801888+256*ordinal+offset < 2^64
    omega)]
  have outsideRoot : ¬ (submission.layout.commitment ≤ submission.layout.values+256*ordinal+offset ∧
      submission.layout.values+256*ordinal+offset < submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 6039801888+256*ordinal+offset ∧ 6039801888+256*ordinal+offset < 4294971424)
    omega
  have outsideIndices : ¬ (submission.layout.indices ≤ submission.layout.values+256*ordinal+offset ∧
      submission.layout.values+256*ordinal+offset < submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 6039801888+256*ordinal+offset ∧
      6039801888+256*ordinal+offset < 5905584160+8*input.positions.card)
    omega
  have selected : submission.layout.values ≤ submission.layout.values+256*ordinal+offset ∧
      submission.layout.values+256*ordinal+offset < submission.layout.values+(LEAF_SIZE/8)*input.positions.card := by
    change _ ≤ _ ∧ _ < submission.layout.values+256*input.positions.card
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, decide_false, selected, and_self, decide_true]
  have quotient : (submission.layout.values+256*ordinal+offset-submission.layout.values)/(LEAF_SIZE/8) = ordinal := by
    change _ / 256 = _
    omega
  have remainder : (submission.layout.values+256*ordinal+offset-submission.layout.values)%(LEAF_SIZE/8) = offset := by
    change _ % 256 = _
    omega
  rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]

/-- The checker leaf loop reads the same eight blocks as the supplied opened value. -/
theorem check_input_value_block (input : CheckInput) (ordinal block : Nat)
    (present : ordinal < input.positions.card) (inside : block < 8) :
    readBuffer (submission.initialState .check input)
      (submission.layout.values+256*ordinal+32*block) 32 =
      (input.values ((input.positions.attach.sort (· ≤ ·))[ordinal]'(by
        simpa using present))).extractLsb' (256*block) 256 := by
  have decoded := read_serialized_slice (submission.initialState .check input)
    (input.values ((input.positions.attach.sort (· ≤ ·))[ordinal]'(by
      simpa using present))) (submission.layout.values+256*ordinal+32*block) (32*block) 32 (by
      intro j hj
      simpa only [Nat.add_assoc] using check_input_value_byte input ordinal (32*block+j) present (by omega))
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using decoded

/-- The actual bytes returned by opening are the bytes loaded by verification.
This covers every honest opening input and does not assume the Merkle proof is valid. -/
theorem check_opening_proof_byte (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) (commitment : Commitment) (values : Values positions)
    (offset : Nat) (inside : offset < 800*positions.card) :
    (submission.initialState .check
      ⟨commitment, positions, values, submission.readProof (openingResult trapdoor positions)⟩).getByte
      (BitVec.ofNat 64 (submission.layout.proof+offset)) =
        (openingResult trapdoor positions).state.getByte
          (BitVec.ofNat 64 (submission.layout.proof+offset)) := by
  let input : CheckInput :=
    ⟨commitment, positions, values, submission.readProof (openingResult trapdoor positions)⟩
  have valid : input.proof.length ≤ submission.sizes.proof := by
    change (submission.readProof _).length ≤ _
    rw [opening_proof_length]
    have cardinal := positions_card_bound positions
    change 800*positions.card ≤ 13421772800
    omega
  have bounded : offset < input.proof.length := by
    change offset < (submission.readProof _).length
    rw [opening_proof_length]
    exact inside
  have loaded := check_input_proof_byte input valid offset bounded
  apply loaded.trans
  simp only [input, Submission.readProof, opening_result_succeeded, if_true,
    opening_result_length, List.getElem_map, List.getElem_range]

/-- Salt and sibling digests survive the opening-output/check-input boundary exactly. -/
theorem check_opening_proof_digest (trapdoor : BitVec (8*submission.sizes.trapdoor))
    (positions : Positions) (commitment : Commitment) (values : Values positions)
    (offset : Nat) (inside : offset+32 ≤ 800*positions.card) :
    readBuffer (submission.initialState .check
      ⟨commitment, positions, values, submission.readProof (openingResult trapdoor positions)⟩)
      (submission.layout.proof+offset) 32 =
        readBuffer (openingResult trapdoor positions).state (submission.layout.proof+offset) 32 := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat 256)
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_assoc, check_opening_proof_byte trapdoor positions commitment values (offset+j)
    (by have := Finset.mem_range.mp hj; omega)]

end CommitGolfCandidate
