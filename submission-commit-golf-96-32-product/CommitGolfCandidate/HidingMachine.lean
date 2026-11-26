import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Identify the commitment and every transmitted proof byte with the salted
reference tree. This removes machine memory from the remaining privacy argument,
without replacing the machine-derived scheme being certified. A leaf's salt is the
24-byte value stored by the machine, used as the initial state `saltState salt`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The heap constructed by the machine is the unique reference heap for its
message and retained salts, on every slot above the cap level (heap slots 128 and up).
Slots below the cap are never committed to and need not be consistent. -/
theorem committed_heap_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, saltState (readBuffer state (5905584160+24*index.val) 24) = salt index)
    (node : Nat) (above : 127 < node) (inside : node < 2*LENGTH) :
    heapDigest state 4294971424 node = saltedHeap oracle.compression message salt node := by
  apply heap_eq_reference_above oracle.compression LENGTH 127 _ _ correct.2.1 _ (2*LENGTH) node
    (by omega) above inside
  intro index below
  have leaf := correct.2.2 ⟨index, below⟩
  rw [salts] at leaf
  simpa only [dif_pos below] using leaf

/-- The commitment is the 64-call chain over the reference cap. -/
theorem committed_root_reference (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, saltState (readBuffer state (5905584160+24*index.val) 24) = salt index) :
    readBuffer state submission.layout.commitment 32 =
      capRoot oracle.compression (referenceCap (saltedHeap oracle.compression message salt)) := by
  refine correct.1.trans ?_
  apply congrArg (capRoot oracle.compression)
  funext node
  unfold heapCap referenceCap
  split
  · exact committed_heap_reference oracle message state correct salt salts (128+node)
      (by omega) (by change 128+node < 2*16777216; omega)
  · rfl

theorem opening_index_record (positions : Positions) (ordinal : Nat) :
    openingIndex positions ordinal = hidingRecordIndex positions ordinal := rfl

/-- The 24 low bytes of a zero-extended salt state are the salt's bytes. -/
theorem salt_state_byte (salt : BitVec 192) (part : Nat) (inside : part < 24) :
    (saltState salt).extractLsb' (8*part) 8 = salt.extractLsb' (8*part) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  simp only [saltState, BitVec.getLsbD_extractLsb', below, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  have small : 8*part+bit < 192 := by omega
  simp [small]

theorem opening_reference_cap (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, saltState (readBuffer state (5905584160+24*index.val) 24) = salt index)
    (positions : Positions) (node : Nat) (inside : node < 128) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state (submission.layout.proof+32*node) 32 =
      saltedHeap oracle.compression message salt (128+node) := by
  dsimp only
  rw [(opening_output_records state positions).1 node inside]
  exact committed_heap_reference oracle message state correct salt salts (128+node)
    (by omega) (by change 128+node < 2*16777216; omega)

/-- Every byte inside the reported proof length is the reference proof byte. -/
theorem opening_reference_byte (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, saltState (readBuffer state (5905584160+24*index.val) 24) = salt index)
    (positions : Positions) (offset : Nat) (below : offset < 4096+568*positions.card) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    (openingResult trapdoor positions).state.getByte (BitVec.ofNat 64 (submission.layout.proof+offset)) =
      referenceProofByte (saltedHeap oracle.compression message salt) salt positions offset := by
  dsimp only
  unfold referenceProofByte
  by_cases cap : offset < 4096
  · have node : offset/32 < 128 := by omega
    have address : submission.layout.proof+32*(offset/32)+offset%32 =
        submission.layout.proof+offset := by omega
    have digest := opening_reference_cap oracle message state correct salt salts positions
      (offset/32) node
    rw [if_pos cap, ← digest, read_buffer_byte _ _ 32 (offset%32) (by omega), address]
  · rw [if_neg cap]
    have present : (offset-4096)/568 < positions.card :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    have records := (opening_output_records state positions).2 _ present
    simp only [opening_index_record] at records
    dsimp only
    by_cases saltPart : (offset-4096)%568 < 24
    · rw [if_pos saltPart]
      have address : submission.layout.proof+4096+568*((offset-4096)/568)+(offset-4096)%568 =
          submission.layout.proof+offset := by omega
      rw [← salts]
      try simp only [Fin.val_mk]
      rw [salt_state_byte _ _ saltPart, ← records.1, read_buffer_byte _ _ 24 _ saltPart, address]
    · rw [if_neg saltPart]
      have level : ((offset-4096)%568-24)/32 < 17 := by omega
      have address : submission.layout.proof+4096+568*((offset-4096)/568)+24+
          32*(((offset-4096)%568-24)/32)+((offset-4096)%568-24)%32 =
            submission.layout.proof+offset := by omega
      have bounds := opening_cap_sibling_bounds ⟨hidingRecordIndex positions ((offset-4096)/568),
        hiding_record_index_bound positions ((offset-4096)/568)⟩ _ level
      have sibling := records.2 _ level
      have heap := committed_heap_reference oracle message state correct salt salts _ bounds.1 bounds.2
      simp only [Fin.val_mk, heapDigest] at heap
      try simp only [Fin.val_mk]
      rw [← heap, ← sibling, read_buffer_byte _ _ 32 _ (by omega), address]

/-- All bytes emitted by the actual opening image equal the reference proof.
The proof covers arbitrary opening sets, including the empty set. -/
theorem opening_reference_bytes (oracle : Oracle) (message : Message)
    (state : MachineState) (correct : CommittedState oracle message state)
    (salt : Index → Digest)
    (salts : ∀ index, saltState (readBuffer state (5905584160+24*index.val) 24) = salt index)
    (positions : Positions) :
    let trapdoor := readBuffer state submission.layout.trapdoor submission.sizes.trapdoor
    submission.readProof (openingResult trapdoor positions) =
      referenceOpening (saltedHeap oracle.compression message salt) salt positions := by
  dsimp only
  rw [Submission.readProof, opening_result_succeeded, if_pos rfl, opening_result_length]
  unfold referenceOpening
  apply List.map_congr_left
  intro offset present
  exact opening_reference_byte oracle message state correct salt salts positions offset
    (List.mem_range.mp present)

end CommitGolfCandidate
