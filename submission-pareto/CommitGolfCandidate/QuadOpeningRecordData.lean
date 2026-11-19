import CommitGolfCandidate.QuadOpeningLowerRun

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open QOpening (OpeningLayout proofBase sortedIndex SameOpeningInput trapdoorBase)

def recordData (state : MachineState) := lowerRun 0 12 (nonceBlock state)

structure RecordData (state after : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state after 685
  cursor : LowerCursor after index ordinal 12
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x10 → reg ≠ .x11 → reg ≠ .x21 → reg ≠ .x30 →
    reg ≠ .x31 → after.getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    after.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)
  frame : ∀ address < 2^64, address < recordBase ordinal ∨ recordBase (ordinal+1) ≤ address →
    after.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)
  nonce : ∀ byte < 16, after.getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    state.getByte (BitVec.ofNat 64 (nonceAddress index+byte))
  leaf : ∀ j < 3, ∀ byte < 32, after.getByte (BitVec.ofNat 64 (leafDestination ordinal j+byte)) =
    state.getByte (BitVec.ofNat 64 (leafAddress index j+byte))
  quad : ∀ j < 3, ∀ byte < 32, after.getByte (BitVec.ofNat 64 (quadDestination ordinal j+byte)) =
    state.getByte (BitVec.ofNat 64 (quadAddress index j+byte))
  sibling : ∀ level < 12, ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      state.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

theorem execute_record_data (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    RecordData state (recordData state) (sortedIndex positions ordinal present) ordinal := by
  let index := sortedIndex positions ordinal present
  let middle := nonceBlock state
  let final := recordData state
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have n := execute_ordinal_nonce s layout trapdoor positions state ordinal present ready
  have low := execute_lower middle index ordinal 0 12 (by omega) (by decide) n.next
  have ⟨_, _, _, nonceFit⟩ := all_nonce_copies_fit index ordinal (by omega)
  have ram : MEMORY_BYTES < 2^64 := by decide
  have start : siblingDestination ordinal 0 = recordBase ordinal+208 := rfl
  refine ⟨n.run.next low.run, low.next,
    fun r a b c d e f g => (low.register r a b e g).trans (n.register r a b c d e f g),
    fun address valid => (low.input address valid).trans (n.input address valid), ?_, ?_, ?_, ?_, ?_⟩
  · intro address fit outside
    have tail := low.frame address fit
    rw [start, show (0:Nat)+12=12 by decide, record_end] at tail
    have later : recordBase ordinal+208 ≤ recordBase (ordinal+1) := by
      unfold recordBase recordBytes
      omega
    exact (tail (outside.imp (by omega) id)).trans
      (n.frame address fit (outside.imp id (by rw [start]; omega)))
  · intro byte inside
    have stable := low.frame (recordBase ordinal+byte) (by omega) (Or.inl (by rw [start]; omega))
    exact stable.trans (n.nonce byte inside)
  · intro j valid byte inside
    have dest : leafDestination ordinal j+byte < siblingDestination ordinal 0 := by
      rw [start]; unfold leafDestination leafOffset; omega
    have fit := all_leaf_copies_fit index ordinal j (by omega) valid
    have stable := low.frame (leafDestination ordinal j+byte) (by omega) (Or.inl dest)
    exact stable.trans (n.leaf j valid byte inside)
  · intro j valid byte inside
    have dest : quadDestination ordinal j+byte < siblingDestination ordinal 0 := by
      rw [start]; unfold quadDestination quadOffset; omega
    have fit := all_quad_copies_fit index ordinal j (by omega) valid
    have stable := low.frame (quadDestination ordinal j+byte) (by omega) (Or.inl dest)
    exact stable.trans (n.quad j valid byte inside)
  · intro level levelBound byte inside
    have sibling := low.fields level (Nat.zero_le _) levelBound byte inside
    have before : siblingAddress index level+byte < recordBase ordinal := by
      have nodeBound := lower_swap_bound index level
      have heapEnd := QOpening.heap_before_nonces
      have nonceEnd := QOpening.nonces_end_at_indices
      have indicesEnd := QOpening.indices_before_records
      have roomy : siblingWidth level ≤ 32 := by unfold siblingWidth; split <;> decide
      unfold siblingAddress recordBase
      omega
    exact sibling.trans (n.frame _ (by omega) (Or.inl before))

end TwoPermutationPrototype.QuadOpening
