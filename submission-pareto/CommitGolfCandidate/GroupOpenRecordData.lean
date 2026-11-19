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

/-- The registers one record may change. -/
def recordScratch : List Reg := [.x6,.x7,.x10,.x21,.x28,.x29,.x31]

/-- One record's data: the prefix (salt and mates), levels 0..12, then level 13 with the fold. -/
def recordData (s : MachineState) := lastLevel (lowerRun 0 13 (recordPrefix s))

structure RecordData (s u : MachineState) (i : Index) (o : Nat) : Prop where
  run : RunsOpeningBlock s u (178+recordExtra o)
  cursor : LowerCursor u i o 14
  register : ∀ r, r ∉ recordScratch → u.getReg r = s.getReg r
  input : ∀ a<proofBase, u.getMem (BitVec.ofNat 64 a)=s.getMem (BitVec.ofNat 64 a)
  frame : ∀ a<2^64, a<recordBase o ∨ recordBase (o+1)≤a →
    u.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)
  nonce : ∀ b<112, u.getByte (BitVec.ofNat 64 (recordBase o+b))=s.getByte (BitVec.ofNat 64 (firstSource i b))
  sibling : ∀ l<14, ∀ b<plainWidth l, u.getByte (BitVec.ofNat 64 (siblingDestination o l+b)) =
    s.getByte (BitVec.ofNat 64 (siblingAddress i l+b))
  fold : ∀ k < 7, ∀ b < 2, u.getByte (BitVec.ofNat 64 (siblingDestination o (6+k)+28+b)) =
    (foldValue (s.getHalfword (BitVec.ofNat 64 (siblingAddress i (6+k)+28)))
      ((s.getHalfword (BitVec.ofNat 64 (siblingAddress i 13+28))).zeroExtend 64 >>> (2*k))).extractLsb' (8*b) 8

theorem first_source_above (i : Index) (b : Nat) : trapdoorBase ≤ firstSource i b := by
  unfold firstSource
  split
  · unfold nonceAddress nonceBase; omega
  · unfold leafAddress groupSlots; omega

/-- Two states hold the same halfword when they hold the same two bytes. -/
theorem halfword_transfer (s t : MachineState) (a b : Nat) (aEven : a % 2 = 0) (bEven : b % 2 = 0)
    (aFit : a+16 ≤ 2^64) (bFit : b+16 ≤ 2^64)
    (low : t.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 b))
    (high : t.getByte (BitVec.ofNat 64 (a+1)) = s.getByte (BitVec.ofNat 64 (b+1))) :
    t.getHalfword (BitVec.ofNat 64 a) = s.getHalfword (BitVec.ofNat 64 b) := by
  have hs := halfword_bytes s b bEven bFit
  have ht := halfword_bytes t a aEven aFit
  exact half_ext _ _ (by rw [ht.1, hs.1, low]) (by rw [ht.2, hs.2, high])

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
  have ramRoom : MEMORY_BYTES+16 ≤ 2^64 := by decide
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
    ⟨atStart.pc,atStart.heap,atStart.slots,atStart.nonce,atStart.leaves,atStart.dest,index,access⟩
  obtain ⟨run0,cursor,written,kept⟩ := execute_record_prefix st i o (by omega) px
  let pre := recordPrefix st
  let lowEnd := lowerRun 0 13 pre
  have low := execute_lower pre i o 0 13 (by omega) (by decide) cursor
  have last := execute_last lowEnd i o (by omega) low.next
  have beginEq : siblingDestination o 0=recordBase o+112 := rfl
  have endFit := all_record_ends_fit o (by omega)
  have endEq : recordBase (o+1) = recordBase o+534 := by unfold recordBase recordBytes; omega
  have end14 : siblingDestination o 14 = recordBase (o+1) := record_end o
  have mono := destination_mono o
  have smallSource (l b : Nat) (hb : b<32) : siblingAddress i l+b < proofBase := by
    have z := upper_swap_bound i l
    have p := heap_before_nonces
    have n := nonces_end_at_indices
    unfold siblingAddress
    omega
  have base : proofBase≤recordBase o := by unfold recordBase; omega
  have dests (l : Nat) (hl : l ≤ 14) : recordBase o+112 ≤ siblingDestination o l ∧
      siblingDestination o l ≤ recordBase o+534 := by
    have a := sibling_offset_start l
    have b := sibling_offset_le l hl
    unfold siblingDestination
    omega
  -- the fold bytes sit at bytes 28, 29 of the folded slots
  have foldAt (k : Nat) (hk : k < 7) : siblingDestination o (6+k)+30 = siblingDestination o (7+k) := by
    have := sibling_offset_next (6+k) (by omega)
    unfold siblingDestination
    rw [show 7+k = 6+k+1 by omega, this]
    unfold siblingWidth
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have awayFold (a : Nat) (h : ∀ k < 7, ¬ (siblingDestination o (6+k)+28 ≤ a ∧ a < siblingDestination o (6+k)+30)) :
      ∀ k < 7, a ≠ siblingDestination o (6+k)+28 ∧ a ≠ siblingDestination o (6+k)+29 := by
    intro k hk
    have := h k hk
    constructor <;> intro e <;> apply this <;> omega
  have lowFrame : ∀ a < 2^64, a < siblingDestination o 0 ∨ siblingDestination o 13 ≤ a →
      lowEnd.getByte (BitVec.ofNat 64 a) = pre.getByte (BitVec.ofNat 64 a) := low.frame
  have lowFields : ∀ l < 13, ∀ b < siblingWidth l,
      lowEnd.getByte (BitVec.ofNat 64 (siblingDestination o l+b)) =
        pre.getByte (BitVec.ofNat 64 (siblingAddress i l+b)) :=
    fun l hl b hb => low.fields l (Nat.zero_le _) (by omega) b hb
  have lowSrc (q : Nat) (hq : q < proofBase) : lowEnd.getByte (BitVec.ofNat 64 q) = st.getByte (BitVec.ofNat 64 q) := by
    have below : q < siblingDestination o 0 := by rw [beginEq]; omega
    exact (lowFrame q (by omega) (Or.inl below)).trans (written.frame q (by omega) (Or.inl (by omega)))
  show RecordData st (lastLevel lowEnd) i o
  refine ⟨?_, last.next, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have total := (run0.next low.run).next last.run
    rw [lower_total_cost, show 39+3*recordCopyCost o+(69+levelCopies o+recordCopyCost o)+70 = 178+recordExtra o by
      unfold recordExtra; omega] at total
    exact total
  · intro r free
    simp only [recordScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at free
    have keptFree : r ∉ prefixScratch := by
      simp only [prefixScratch, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨free.1, free.2.1, free.2.2.1, free.2.2.2.1, free.2.2.2.2.1, free.2.2.2.2.2.1, free.2.2.2.2.2.2⟩
    exact (last.register r free.1 free.2.1 free.2.2.2.1 free.2.2.2.2.1 free.2.2.2.2.2.1 free.2.2.2.2.2.2).trans
      ((low.register r free.1 free.2.1 free.2.2.2.1 free.2.2.2.2.2.2 free.2.2.2.2.2.1).trans (kept r keptFree))
  · intro a ha
    exact (last.input a ha).trans ((low.input a ha).trans (written.input a ha))
  · intro a fit outside
    have d13 := dests 13 (by omega)
    have stepLast := last.frame a fit (by
      rcases outside with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by rw [end14]; exact h)) (awayFold a (fun k hk => by
        have := dests (6+k) (by omega); have := dests (7+k) (by omega); have := foldAt k hk; omega))
    have stepLow := lowFrame a fit (by
      rcases outside with h | h
      · exact Or.inl (by rw [beginEq]; omega)
      · exact Or.inr (by have := mono (show 13 ≤ 14 by omega); omega))
    exact stepLast.trans (stepLow.trans (written.frame a fit (outside.imp (by omega) (by omega))))
  · intro b hb
    have d6 := dests 6 (by omega)
    have stepLast := last.frame (recordBase o+b) (by omega) (Or.inl (by have := dests 13 (by omega); omega))
      (awayFold _ (fun k hk => by have := mono (show 6 ≤ 6+k by omega); omega))
    exact stepLast.trans ((lowFrame (recordBase o+b) (by omega) (Or.inl (by rw [beginEq]; omega))).trans
      (written.bytes b (by omega) hb))
  · intro l hl b hb
    have src := smallSource l b (by have := plain_width_le l; have := sibling_width_le l; omega)
    by_cases thirteen : l = 13
    · subst l
      have b28 : b < 28 := by simpa [plainWidth, folded, siblingWidth] using hb
      exact (last.copied b b28).trans (lowSrc _ src)
    · have inner : l < 13 := by omega
      have wide : b < siblingWidth l := by have := plain_width_le l; omega
      have dl := dests l (by omega)
      have dnext := mono (show l+1 ≤ 13 by omega)
      have stepNext : siblingDestination o (l+1) = siblingDestination o l+siblingWidth l := by
        unfold siblingDestination; rw [sibling_offset_next l (by omega)]; omega
      have stepLast := last.frame (siblingDestination o l+b) (by have := dests 13 (by omega); omega)
        (Or.inl (by have := sibling_width_le l; omega))
        (awayFold _ (fun k hk => by
          have a1 := foldAt k hk
          by_cases same : 6+k = l
          · subst same
            have narrow : b < 28 := by simpa [plainWidth, folded, show 6 ≤ 6+k by omega, show 6+k < 13 by omega] using hb
            omega
          · by_cases lower : 6+k < l
            · have := mono (show 7+k ≤ l by omega); omega
            · have := mono (show l+1 ≤ 6+k by omega); omega))
      exact stepLast.trans ((lowFields l inner b wide).trans
        (written.frame _ (by omega) (Or.inl (by omega))))
  · intro k hk b hb
    have d := dests (6+k) (by omega)
    have dn := dests (7+k) (by omega)
    have fa := foldAt k hk
    have destEven := even_sibling_destination o (6+k)
    have srcFit := (all_sibling_copies_fit i o (6+k) (by omega) (by omega))
    have width : siblingWidth (6+k) = 30 := by unfold siblingWidth; rw [if_neg (by omega), if_pos (by omega)]
    have slotHalf : lowEnd.getHalfword (BitVec.ofNat 64 (siblingDestination o (6+k)+28)) =
        st.getHalfword (BitVec.ofNat 64 (siblingAddress i (6+k)+28)) := by
      apply halfword_transfer st lowEnd _ _ (by omega) (by have := srcFit.1; omega) (by omega)
        (by have := smallSource (6+k) 29 (by omega); omega)
      · refine (lowFields (6+k) (by omega) 28 (by omega)).trans ?_
        exact written.frame _ (by have := smallSource (6+k) 28 (by omega); omega)
          (Or.inl (by have := smallSource (6+k) 28 (by omega); omega))
      · show lowEnd.getByte (BitVec.ofNat 64 (siblingDestination o (6+k)+29)) =
          st.getByte (BitVec.ofNat 64 (siblingAddress i (6+k)+29))
        refine (lowFields (6+k) (by omega) 29 (by omega)).trans ?_
        exact written.frame _ (by have := smallSource (6+k) 29 (by omega); omega)
          (Or.inl (by have := smallSource (6+k) 29 (by omega); omega))
    have src13 := all_sibling_copies_fit i o 13 (by omega) (by omega)
    have topHalf : lowEnd.getHalfword (BitVec.ofNat 64 (siblingAddress i 13+28)) =
        st.getHalfword (BitVec.ofNat 64 (siblingAddress i 13+28)) := by
      apply halfword_transfer st lowEnd _ _ (by have := src13.1; omega) (by have := src13.1; omega)
        (by have := smallSource 13 29 (by omega); omega) (by have := smallSource 13 29 (by omega); omega)
      · exact lowSrc _ (smallSource 13 28 (by omega))
      · show lowEnd.getByte (BitVec.ofNat 64 (siblingAddress i 13+29)) =
          st.getByte (BitVec.ofNat 64 (siblingAddress i 13+29))
        exact lowSrc _ (smallSource 13 29 (by omega))
    rw [last.folds k hk b hb, slotHalf, topHalf]

end TwoPermutationPrototype.GroupedOpening
