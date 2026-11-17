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

private theorem opening_exit_memory (state : MachineState) :
    (openingExitState state).mem = state.mem := rfl

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

attribute [local irreducible] openingPositionState openingInitializedState

set_option maxRecDepth 4096 in
/-- Every emitted salt and sibling equals the corresponding digest of the actual
commitment memory, after serialization into the opening's private-state input. -/
theorem opening_output_records (committed : MachineState) (positions : Positions) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    ∀ ordinal < positions.card,
      readBuffer (openingResult trapdoor positions).state
        (submission.layout.proof+800*ordinal) 32 =
          readNonce committed (5368713248+24*openingIndex positions ordinal) ∧
      ∀ level < 24,
        readBuffer (openingResult trapdoor positions).state
          (submission.layout.proof+800*ordinal+32+32*level) 32 =
            readBuffer committed
              (4294971424+32*(((LENGTH+openingIndex positions ordinal)/2^level) ^^^ 1)) 32 := by
  let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
  let initial := submission.initialState .opening (trapdoor, positions)
  let ready := openingInitializedState initial
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have cardinalSmall : positions.card ≤ 16777216 := cardinal
  have regs := opening_setup_registers initial
  have heap : ready.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    regs.1.trans (initial_heap submission trapdoor positions)
  have indices : ready.getReg .x24 = BitVec.ofNat 64 5905584160 :=
    regs.2.1.trans (initial_indices submission trapdoor positions)
  have output : ready.getReg .x25 = BitVec.ofNat 64 10334769184 :=
    regs.2.2.1.trans (initial_output submission trapdoor positions)
  have leaves : ready.getReg .x19 = BitVec.ofNat 64 LENGTH := regs.2.2.2.2.1
  have salts : ready.getReg .x18 = BitVec.ofNat 64 5368713248 := by
    rw [regs.2.2.2.2.2.1, initial_heap submission trapdoor positions]
    rfl
  have memory : ready.mem = initial.mem := regs.2.2.2.2.2.2.2
  have indexData (ordinal : Nat) (present : ordinal < positions.card) :
      ready.getMem (BitVec.ofNat 64 (5905584160+8*ordinal)) =
        BitVec.ofNat 64 (openingIndex positions ordinal) := by
    rw [show ready.getMem = initial.getMem from congrArg (fun mem address => mem address) memory]
    exact (opening_input_index trapdoor positions ordinal present).trans (by
      simp only [openingIndex, dif_pos present])
  have heapData (slot : Nat) (inside : slot < 2^25) :
      readBuffer ready (4294971424+32*slot) 32 = readBuffer committed (4294971424+32*slot) 32 := by
    rw [read_buffer_memory_congr _ _ memory]
    exact opening_input_roundtrip committed positions (32*slot) (by
      change 32*slot+32 ≤ 1610612736; omega)
  have saltData (index : Nat) (inside : index < LENGTH) :
      readNonce ready (5368713248+24*index) = readNonce committed (5368713248+24*index) := by
    have small : index < 16777216 := inside
    unfold readNonce
    rw [read_buffer_memory_congr _ _ memory]
    have result := opening_input_roundtrip committed positions (1073741824+24*index) (by
      change 1073741824+24*index+32 ≤ 1610612736; omega)
    change readBuffer initial (4294971424+(1073741824+24*index)) 32 =
      readBuffer committed (4294971424+(1073741824+24*index)) 32 at result
    exact congrArg (fun bits : BitVec 256 => expandNonce192 (bits.extractLsb' 0 192)) (by simpa only [← Nat.add_assoc] using result)
  have records := opening_all_records ready
    (fun slot => readBuffer committed (4294971424+32*slot) 32)
    (fun index => readNonce committed (5368713248+24*index))
    (openingIndex positions) 4294971424 5368713248 5905584160 10334769184 positions.card
    heap salts leaves indices output (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    (by change 10334769184+800*positions.card ≤ 2^36; omega)
    indexData (fun ordinal _ => opening_index_bound positions ordinal) heapData saltData
  dsimp only
  intro ordinal present
  have finalMemory : (openingResult trapdoor positions).state.mem =
      (openingPositionState^[positions.card] ready).mem := opening_exit_memory _
  constructor
  · rw [read_buffer_memory_congr _ _ finalMemory]
    exact (records ordinal present).1
  · intro level inside
    rw [read_buffer_memory_congr _ _ finalMemory]
    exact (records ordinal present).2 level inside

end CommitGolfCandidate
