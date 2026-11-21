import CommitGolfCandidate.GroupOpenWholeRecords
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
  /-- The prefix pass's pointer word of the record's quartet: the address of its level-22 sibling node. -/
  pointer : ∀ present : ordinal<positions.card,
    state.getMem (BitVec.ofNat 64 (pointerAddress (sortedIndex positions ordinal present).val)) =
      BitVec.ofNat 64 (quadAddress (sortedIndex positions ordinal present).val)

/-- The registers one record may change. -/
def recordScratch : List Reg := [.x6,.x7,.x10,.x21,.x28,.x29,.x31]

/-- One record's data: the prefix (salt and mates), levels 0..12, then level 13 with the fold. -/
def recordData (s : MachineState) :=
  let c := (s.getReg .x21).toNat%8/2
  Whole.runNodes c 0 14 (recordPrefix c s)

structure RecordData (s u : MachineState) (i : Index) (o : Nat) : Prop where
  run : RunsOpeningBlock s u (127+recordExtra o)
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
  let c : Fin 4:=⟨Whole.pageClass o,Whole.class_lt o⟩
  let pre:=recordPrefix c st
  let u:=Whole.runNodes c 0 14 pre
  have cEq : (st.getReg .x21).toNat%8/2=c.val := by
    rw [atStart.dest,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show recordBase o<2^64 by
      have := all_record_ends_fit o (by omega)
      have ram : MEMORY_BYTES<2^64 := by decide
      unfold recordBase recordBytes at *;omega)]
    rfl
  obtain ⟨run0,cur,writes,kept,slot,loaded⟩:=execute_record_prefix st i o (by omega) px
  have facts:=pointer_address_inside i.val i.isLt
  have ptr : pre.getMem (BitVec.ofNat 64 (pointerAddress i.val))=BitVec.ofNat 64 (quadAddress i.val) :=
    (writes.input _ (by have:=nonces_end_at_indices;omega)).trans (atStart.pointer present)
  have result:=Whole.run_nodes pre i o 0 14 (by omega) (by decide) cur (fun _ => ⟨slot,ptr⟩)
  have eq : recordData st=u := by unfold recordData;rw [cEq]
  rw [eq]
  have d0 : siblingDestination o 0=recordBase o+112 := rfl
  have end14 : siblingDestination o 14=recordBase (o+1) := record_end o
  have endEq : recordBase (o+1)=recordBase o+534 := by unfold recordBase recordBytes;omega
  have fit:=all_record_ends_fit o (by omega)
  have before : ∀ l, siblingAddress i l+32<proofBase := by intro l;have h:=(sibling_address_inside i l).2.2; exact lt_of_le_of_lt h (by decide : nonceBase<proofBase)
  refine ⟨?_,⟨result.next.pc,result.next.heap,result.next.node,result.next.dest⟩,?_,
    fun a ha => (result.input a ha).trans (writes.input a ha),?_,?_,?_,?_⟩
  · have chain:=run0.next result.run
    have price : ∀ c : Fin 4, (9+(Whole.row c 7-Whole.row c 0))+
        (Whole.point c (0+14)-Whole.point c 0)=127+(Whole.row c 22-Whole.row c 0-118) := by decide
    change RunsOpeningBlock st u (127+recordExtra o)
    rw [show 127+recordExtra o=(9+(Whole.row c 7-Whole.row c 0))+(Whole.point c (0+14)-Whole.point c 0) from (price c).symm]
    exact chain
  · intro r free
    refine (result.kept r ?_ ?_ ?_ ?_ ?_).trans (kept r free)
    all_goals intro eq; subst r; exact free (by decide)
  · intro a afit outside
    exact (result.frame a afit (by change a<siblingDestination o 0 ∨ siblingDestination o 14≤a;rw [d0,end14];omega)).trans
      (writes.frame a afit (by omega))
  · intro b hb
    exact (result.frame _ (by omega) (Or.inl (by rw [d0];omega))).trans (writes.bytes b (by omega) hb)
  · intro l hl b hb
    have h:=result.fields l (by omega) hl b (lt_of_lt_of_le hb (plain_width_le l))
    have raw : ¬(folded l ∧ 28≤b) := by intro ⟨f,g⟩;unfold plainWidth at hb;rw [if_pos f] at hb;omega
    rw [Whole.payload,if_neg raw] at h
    exact h.trans (Whole.byte_from_words writes.input _ (by have:=before l;have:=sibling_width_le l;have:=plain_width_le l;omega))
  · intro k hk b hb
    have f : folded (6+k) := by unfold folded;omega
    have wid : siblingWidth (6+k)=30 := by unfold siblingWidth;rw [if_neg (by omega),if_pos (by omega)]
    have h:=result.fields (6+k) (by omega) (by omega) (28+b) (by rw [wid];omega)
    have direct : (6+k)-6=k := by omega
    rw [Whole.payload,if_pos ⟨f,by omega⟩,Whole.tag,show 28+b-28=b by omega,direct] at h
    rw [show pre.getReg .x10=_ from loaded,
      Whole.half_from_words writes.input (siblingAddress i (6+k)+28) (by have:=before (6+k);omega),
      Whole.half_from_words writes.input (siblingAddress i 13+28) (by have:=before 13;omega)] at h
    simpa only [Nat.add_assoc] using h

end TwoPermutationPrototype.GroupedOpening
