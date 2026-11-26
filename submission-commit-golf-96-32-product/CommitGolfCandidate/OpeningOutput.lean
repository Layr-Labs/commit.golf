import CommitGolfCandidate.OpeningRecords
import CommitGolfCandidate.BufferRefinement

/-! Exact proof records after the full opening ABI and machine execution. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- A total index lookup used only to describe the already-sorted ABI index list. -/
def openingIndex (positions : Positions) (ordinal : Nat) : Nat :=
  if present : ordinal < positions.card then
    ((positions.sort (· ≤ ·))[ordinal]'(by simpa using present)).val
  else 0

theorem opening_index_bound (positions : Positions) (ordinal : Nat) :
    openingIndex positions ordinal < LENGTH := by
  unfold openingIndex
  split
  · exact Fin.isLt _
  · decide

private theorem initial_heap (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x12 =
      BitVec.ofNat 64 program.layout.trapdoor := rfl

private theorem initial_indices (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x13 =
      BitVec.ofNat 64 program.layout.indices := rfl

private theorem initial_output (program : Submission)
    (trapdoor : BitVec (8*program.sizes.trapdoor)) (positions : Positions) :
    (program.initialState .opening (trapdoor, positions)).getReg .x15 =
      BitVec.ofNat 64 program.layout.proof := rfl

/-- Reads of two aligned digests agree when their four words agree pairwise. -/
private theorem read_digest_transfer (left right : MachineState) (first second : Nat)
    (firstAligned : first % 8 = 0) (secondAligned : second % 8 = 0)
    (words : ∀ i < 4, left.getMem (BitVec.ofNat 64 (first + 8*i)) =
      right.getMem (BitVec.ofNat 64 (second + 8*i))) :
    readBuffer left first 32 = readBuffer right second 32 := by
  rw [read_digest_words _ _ firstAligned, read_digest_words _ _ secondAligned]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  have w3 := words 3 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]

attribute [local irreducible] openingPositionState openingInitializedState

set_option maxRecDepth 4096 in
/-- Every emitted cap node, salt and sibling equals the corresponding digest of the
actual commitment memory, after serialization into the opening's private-state input.
The proof starts with the 128 cap nodes (heap slots 128..255), followed by one
568-byte record (24-byte salt and 17 siblings) per position. -/
theorem opening_output_records (committed : MachineState) (positions : Positions) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    (∀ node < 128, readBuffer (openingResult trapdoor positions).state
        (submission.layout.proof+32*node) 32 =
          readBuffer committed (4294971424+heapOffset (128+node)) 32) ∧
    ∀ ordinal < positions.card,
      readBuffer (openingResult trapdoor positions).state
        (submission.layout.proof+4096+568*ordinal) 24 =
          readBuffer committed (5905584160+24*openingIndex positions ordinal) 24 ∧
      ∀ level < 17,
        readBuffer (openingResult trapdoor positions).state
          (submission.layout.proof+4096+568*ordinal+24+32*level) 32 =
            readBuffer committed
              (4294971424+heapOffset (((LENGTH+openingIndex positions ordinal)/2^level) ^^^ 1)) 32 := by
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have cardinalSmall : positions.card ≤ 16777216 := cardinal
  have regs := opening_setup_registers initial
  have heap : ready.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    regs.1.trans (initial_heap submission trapdoor positions)
  have indices : ready.getReg .x24 = BitVec.ofNat 64 6442455072 :=
    regs.2.1.trans (initial_indices submission trapdoor positions)
  have output : ready.getReg .x25 = BitVec.ofNat 64 10871644192 := by
    rw [regs.2.2.1, initial_output submission trapdoor positions]
    rfl
  have leaves : ready.getReg .x19 = BitVec.ofNat 64 LENGTH := regs.2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 5905584160 := by
    rw [regs.2.2.2.2.2.1, initial_heap submission trapdoor positions]
    rfl
  have memoryBelow (address : Nat) (below : address < 10871640096) :
      ready.getMem (BitVec.ofNat 64 address) = initial.getMem (BitVec.ofNat 64 address) := by
    apply opening_initialized_memory trapdoor positions
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact below
  have indexData (ordinal : Nat) (present : ordinal < positions.card) :
      ready.getMem (BitVec.ofNat 64 (6442455072+8*ordinal)) =
        BitVec.ofNat 64 (openingIndex positions ordinal) := by
    rw [memoryBelow _ (by omega)]
    exact (opening_input_index trapdoor positions ordinal present).trans (by
      simp only [openingIndex, dif_pos present])
  have heapData (slot : Nat) (inside : slot < 2^25) :
      readBuffer ready (4294971424+heapOffset slot) 32 =
        readBuffer committed (4294971424+heapOffset slot) 32 := by
    have within := heap_offset_bound slot (2^24) (by omega)
    have aligned := heap_offset_aligned slot
    rw [read_digest_congr _ initial _ (by omega) (fun i hi => memoryBelow _ (by omega))]
    exact opening_input_roundtrip committed positions (heapOffset slot) (by
      change heapOffset slot+32 ≤ 2147483648; omega)
  have saltData (index : Nat) (inside : index < LENGTH) :
      readBuffer ready (5905584160+24*index) 24 = readBuffer committed (5905584160+24*index) 24 := by
    have small : index < 16777216 := inside
    rw [read_salt_congr _ initial _ _ (by omega) (by omega) (fun i hi => memoryBelow _ (by omega))]
    have result := opening_input_roundtrip_bytes committed positions (1610612736+24*index) 24 (by
      change 1610612736+24*index+24 ≤ 2147483648; omega)
    change readBuffer initial (4294971424+(1610612736+24*index)) 24 =
      readBuffer committed (4294971424+(1610612736+24*index)) 24 at result
    simpa only [← Nat.add_assoc] using result
  have records := opening_all_records ready
    (fun slot => readBuffer committed (4294971424+heapOffset slot) 32)
    (fun index => readBuffer committed (5905584160+24*index) 24)
    (openingIndex positions) 4294971424 5905584160 6442455072 10871644192 positions.card
    heap salts leaves indices output (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    (by change 10871644192+568*positions.card ≤ 2^36; omega)
    indexData (fun ordinal _ => opening_index_bound positions ordinal) heapData saltData
  have cap := opening_setup_cap initial 4294971424 10871640096
    (initial_heap submission trapdoor positions) (initial_output submission trapdoor positions)
    (by decide) (by decide)
  have finalMemory : (openingResult trapdoor positions).state.mem =
      (openingPositionState^[positions.card] ready).mem := opening_exit_memory _
  have proofAddress : submission.layout.proof = 10871640096 := rfl
  dsimp only
  rw [proofAddress]
  constructor
  · intro node inside
    rw [read_buffer_memory_congr _ _ finalMemory]
    have kept : readBuffer (openingPositionState^[positions.card] ready) (10871640096+32*node) 32 =
        readBuffer ready (10871640096+32*node) 32 := by
      apply read_digest_congr _ _ _ (by omega)
      intro i hi
      apply opening_positions_memory_below
      · rw [output, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
        change 10871644192+568*positions.card ≤ 2^36
        omega
      · rw [output, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 10871640096+32*node+8*i < 2^64),
          Nat.mod_eq_of_lt (by decide : 10871644192 < 2^64)]
        omega
    rw [kept]
    have offsetAligned : (4294971424+heapOffset (128+node)) % 8 = 0 := by
      unfold heapOffset; omega
    have offsetBound : heapOffset (128+node)+32 ≤ 2147483648 := by
      unfold heapOffset; omega
    rw [read_digest_transfer ready initial _ (4294971424+heapOffset (128+node)) (by omega)
      offsetAligned (fun i hi => by
        rw [show 10871640096+32*node+8*i = 10871640096+64*(node/2)+8*(4*(node%2)+i) by omega,
          show 4294971424+heapOffset (128+node)+8*i =
            4294971424+6144+96*(node/2)+8*(4*(node%2)+i) by unfold heapOffset; omega]
        exact cap (node/2) (by omega) (4*(node%2)+i) (by omega))]
    exact opening_input_roundtrip committed positions (heapOffset (128+node)) offsetBound
  · intro ordinal present
    rw [read_buffer_memory_congr _ _ finalMemory,
      show 10871640096+4096+568*ordinal = 10871644192+568*ordinal by omega]
    refine ⟨(records ordinal present).1, fun level inside => ?_⟩
    rw [read_buffer_memory_congr _ _ finalMemory,
      show 10871644192+568*ordinal+24+32*level = 10871644192+568*ordinal+24+32*level from rfl]
    exact (records ordinal present).2 level inside

end CommitGolfCandidate
