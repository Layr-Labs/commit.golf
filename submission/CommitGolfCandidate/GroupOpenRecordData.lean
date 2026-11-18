import CommitGolfCandidate.GroupOpenPrefix
import CommitGolfCandidate.TwoPermutationOpeningRecordStart

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (sortedIndex)

structure RecordStart (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc=0x103c
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21=BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  input : SameOpeningInput (s.initialState .opening (trapdoor,positions)) state
  mult : state.getReg .x4=368

def recordData (s : MachineState) := lowerRun 0 14 (recordPrefix s)

structure RecordData (s u : MachineState) (i : Index) (o : Nat) : Prop where
  run : RunsOpeningSlack s u 630 3
  cursor : LowerCursor u i o 14
  register : Keeps s u
  input : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)
  frame : ∀ a<2^64, a<recordBase o ∨ recordBase (o+1)≤a →
    u.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)
  nonce : ∀ b<112, u.getByte (BitVec.ofNat 64 (recordBase o+b))=s.getByte (BitVec.ofNat 64 (firstSource i b))
  sibling : ∀ l<14, ∀ b<siblingWidth l, u.getByte (BitVec.ofNat 64 (siblingDestination o l+b)) =
    s.getByte (BitVec.ofNat 64 (siblingAddress i l+b))

theorem first_source_above (i : Index) (b : Nat) : trapdoorBase ≤ firstSource i b := by
  unfold firstSource
  split
  · unfold nonceAddress nonceBase; omega
  · unfold leafAddress groupSlots; omega

theorem execute_record_data (s : Submission) (layout : OpeningLayout s) (t : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (st : MachineState) (o : Nat) (present : o<positions.card)
    (atStart : RecordStart s t positions st o) :
    RecordData st (recordData st) (sortedIndex positions o present) o := by
  let i := sortedIndex positions o present
  have cardinal : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have io := indices_before_records
  have ia : trapdoorBase ≤ indicesBase+8*o := by unfold indicesBase; omega
  have ib : indicesBase+8*o<proofBase := by omega
  have ram : MEMORY_BYTES<2^64 := by decide
  have bounds := packed_proof_memory
  have access : accessValid (st.getReg .x8) 8 = true := by
    rw [atStart.index]
    apply Opening.aligned_access
    · have : indicesBase %8=0 := by decide
      omega
    · omega
  have index : st.getMem (st.getReg .x8)=BitVec.ofNat 64 i.val := by
    have align : (indicesBase+8*o)%8=0 := by
      have a : indicesBase%8=0 := by decide
      omega
    rw [atStart.index,atStart.input _ ia ib align]
    exact input_index s layout t positions o present
  have px : PrefixStart st i o :=
    ⟨atStart.pc,atStart.heap,atStart.slots,atStart.mult,atStart.nonce,atStart.leaves,atStart.dest,index,access⟩
  obtain ⟨run0,cursor,written,kept⟩ := execute_record_prefix st i o (by omega) px
  have low := execute_lower (recordPrefix st) i o 0 14 (by omega) (by decide) cursor
  have beginEq : siblingDestination o 0=recordBase o+112 := rfl
  have endFit := all_record_ends_fit o (by omega)
  have endEq : recordBase (o+1) = recordBase o+534 := by unfold recordBase recordBytes; omega
  have smallSource (l b : Nat) (hb : b<siblingWidth l) : siblingAddress i l+b < proofBase := by
    have z := upper_swap_bound i l
    have p := heap_before_nonces
    have n := nonces_end_at_indices
    have w : siblingWidth l≤32 := by unfold siblingWidth; split <;> decide
    unfold siblingAddress
    omega
  have base : proofBase≤recordBase o := by unfold recordBase; omega
  refine ⟨run0.then low.run,low.next,?_,fun a ha => (low.input a ha).trans (written.input a ha),?_,?_,?_⟩
  · intro r free
    have w := free
    simp only [prefixScratch,List.mem_cons,List.not_mem_nil,or_false,not_or] at w
    exact (low.register r w.1 w.2.1 w.2.2.2.1 w.2.2.2.2.2).trans (kept r free)
  · intro a fit outside
    have rest := low.frame a fit
    rw [beginEq,show (0:Nat)+14=14 by decide,record_end] at rest
    exact (rest (outside.imp (by omega) id)).trans
      (written.frame a fit (outside.imp (by omega) (by omega)))
  · intro b hb
    exact (low.frame _ (by omega) (Or.inl (by rw [beginEq]; omega))).trans (written.bytes b (by omega) hb)
  · intro l hl b hb
    have src := smallSource l b hb
    exact (low.fields l (by omega) hl b hb).trans (written.frame _ (by omega) (Or.inl (by omega)))

end TwoPermutationPrototype.GroupedOpening
