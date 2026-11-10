import CommitGolfCandidate.Compact.OpeningInput
import CommitGolfCandidate.Compact.OpeningRecords
import CommitGolfCandidate.OpeningOutput
import CommitGolfCandidate.BufferRefinement

/-! Exact proof records after the full opening ABI and machine execution. -/
namespace CommitGolfCandidate.Compact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

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
theorem arbitrary_output_records (trapdoor : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :
    ∀ ordinal < positions.card,
      readBuffer (openingResult trapdoor positions).state
        (submission.layout.proof+792*ordinal) 24 =
          (readNonce (openingInitializedState (submission.initialState .opening (trapdoor,positions))) (5368713248+24*openingIndex positions ordinal)).extractLsb' 0 192 ∧
      ∀ level < 24,
        readBuffer (openingResult trapdoor positions).state
          (submission.layout.proof+792*ordinal+24+32*level) 32 =
            readBuffer (openingInitializedState (submission.initialState .opening (trapdoor,positions)))
              (4294971424+32*(((LENGTH+openingIndex positions ordinal)/2^level) ^^^ 1)) 32 := by
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
  have records := opening_all_records ready
    (fun slot => readBuffer ready (4294971424+32*slot) 32)
    (fun index => readNonce ready (5368713248+24*index))
    (openingIndex positions) 4294971424 5368713248 5905584160 10334769184 positions.card
    heap salts leaves indices output (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega)
    (by change 10334769184+792*positions.card ≤ 2^36; omega)
    indexData (fun ordinal _ => opening_index_bound positions ordinal) (fun _ _ => rfl) (fun _ _ => rfl)
  intro ordinal present
  have finalMemory : (openingResult trapdoor positions).state.mem =
      (openingPositionState^[positions.card] ready).mem := opening_exit_memory _
  constructor
  · rw [read_buffer_memory_congr _ _ finalMemory]
    exact (records ordinal present).1
  · intro level inside
    rw [read_buffer_memory_congr _ _ finalMemory]
    exact (records ordinal present).2 level inside

end CommitGolfCandidate.Compact
