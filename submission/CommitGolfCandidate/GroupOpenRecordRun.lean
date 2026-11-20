import CommitGolfCandidate.GroupOpenRecordsAPI
import CommitGolfCandidate.GroupOpenRecordTail
import CommitGolfCandidate.GroupOpenSetup
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (sortedIndex markBase
  RecordMarks groupsBefore machineMarks nat_address_injective)

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem tail_register (state : MachineState) (reg : Reg)
    (temp : reg ≠ .x7) (index : reg ≠ .x8) :
    (recordTailPrefix state 5).getReg reg = state.getReg reg := by
  by_cases done : state.getReg .x8 + 8#64 = state.getReg .x17 <;>
    simp [recordTailPrefix, recordTailInstructions, Opening.recordTailInstructions, execInstrBr,
      signExtend12, done, Ne.symm temp, Ne.symm index]

attribute [local irreducible] execute recordData recordTailPrefix

private theorem after_latch_memory (marked : MachineState) (final : Bool) :
    (afterLatch marked final).mem = marked.mem := by cases final <;> rfl

private theorem after_latch_register (marked : MachineState) (final : Bool) (r : Reg) :
    (afterLatch marked final).getReg r = marked.getReg r := by cases final <;> rfl

private theorem record_tail_target (state : MachineState) (pc : state.pc = 0x1a08)
    (last : Prop) [Decidable last]
    (matchEnd : state.getReg .x8 + 8#64 = state.getReg .x17 ↔ last) :
    (recordTailPrefix state 5).pc = (if last then 0x1a1c else 0x103c) := by
  rw [(record_tail_post state pc).2.2]
  by_cases h : last
  · rw [ite_eq_left (matchEnd.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun z => h (matchEnd.mp z)), ite_eq_right h]

private theorem tail_mark_memory (prepared : MachineState) (final : Bool) (pc : prepared.pc = 0x1a08)
    (address : Word) (target : Opening.recordMarkAddress prepared = address)
    (flag : prepared.getReg .x23 = 1#64) :
    (afterLatch (recordTailPrefix prepared 5) final).mem = (prepared.setMem address 1#64).mem := by
  refine Eq.trans (after_latch_memory _ final) ?_
  have post : (recordTailPrefix prepared 5).mem =
      (prepared.setMem (Opening.recordMarkAddress prepared) (prepared.getReg .x23)).mem :=
    (record_tail_post prepared pc).1
  rw [post, target, flag]

private def latchCost (final : Bool) : Nat := if final then 6 else 5

private theorem run_latch (state : MachineState) (last : Prop) [Decidable last]
    (run : RunsOpeningBlock state (recordTailPrefix state 5) 5)
    (pc : (recordTailPrefix state 5).pc = if last then 0x1a1c else 0x103c) :
    RunsOpeningBlock state (afterLatch (recordTailPrefix state 5) (decide last)) (latchCost (decide last)) := by
  by_cases h : last
  · have bit : decide last = true := decide_eq_true h
    rw [bit]
    have jumpPC : (recordTailPrefix state 5).pc = 0x1a1c := pc.trans (ite_eq_left h)
    have jump : RunsOpeningBlock (recordTailPrefix state 5)
        ((recordTailPrefix state 5).setPC 0x1a24) 1 := fun fuel coins =>
      execute_record_final _ jumpPC fuel coins
    exact run.next jump
  · have bit : decide last = false := decide_eq_false h
    rw [bit]
    exact run

private theorem latch_target (marked : MachineState) (last : Prop) [Decidable last]
    (pc : marked.pc = if last then 0x1a1c else 0x103c) :
    (afterLatch marked (decide last)).pc = if last then 0x1a24 else 0x103c := by
  by_cases h : last
  · rw [show decide last = true from decide_eq_true h, ite_eq_left h]
    rfl
  · rw [show decide last = false from decide_eq_false h, ite_eq_right h]
    exact pc.trans (ite_eq_right h)

private theorem complete_record_cost (ordinal : Nat) (final : Bool) :
    130+recordExtra ordinal+latchCost final = recordCost ordinal final := by
  cases final <;> simp [recordCost, latchCost] <;> omega

private theorem execute_record_with_data (s : Submission)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state prepared : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (data : RecordData state prepared (sortedIndex positions ordinal present) ordinal) :
    OneRecord s trapdoor positions state
      (afterLatch (recordTailPrefix prepared 5) (decide (ordinal+1=positions.card))) ordinal present := by
  let index := sortedIndex positions ordinal present
  let marked := recordTailPrefix prepared 5
  let done := afterLatch marked (decide (ordinal+1=positions.card))
  have sameBase : Opening.trapdoorBase = trapdoorBase := rfl
  let group := Sampling.capGroup index
  let markAddr := markBase+8*group
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have pc : prepared.pc = 0x1a08 := data.cursor.pc
  have groupBound : group < 512 := (Opening.lower_cap_range index).2
  have markFit : markAddr < trapdoorBase := by
    have room := Opening.marks_before_trapdoor
    unfold markAddr
    omega
  have address : Opening.recordMarkAddress prepared = BitVec.ofNat 64 markAddr :=
    Opening.record_mark_address prepared group
      ((data.register .x26 (by decide)).trans boundary.marks)
      data.cursor.node
  have safe : accessValid (Opening.recordMarkAddress prepared) 8 = true := by
    rw [address]
    apply Opening.aligned_access
    · have aligned : markBase % 8 = 0 := by decide
      unfold markAddr
      omega
    · have room : trapdoorBase+8 ≤ MEMORY_BYTES := by decide
      omega
  have post := record_tail_post prepared pc
  have pointer : prepared.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal) :=
    (data.register .x8 (by decide)).trans boundary.index
  have finish : prepared.getReg .x17 = BitVec.ofNat 64 (indicesBase+8*positions.card) :=
    (data.register .x17 (by decide)).trans boundary.endIndex
  have bumped : prepared.getReg .x8 + 8#64 = BitVec.ofNat 64 (indicesBase+8*(ordinal+1)) := by
    rw [pointer, ← BitVec.ofNat_add]
    congr 1
  have nowEnd : prepared.getReg .x8 + 8#64 = prepared.getReg .x17 ↔ ordinal+1=positions.card := by
    have base : indicesBase = 9395245088 := rfl
    have length : LENGTH = 16777216 := rfl
    rw [bumped, finish]
    constructor
    · intro z
      have eq := nat_address_injective (by omega) (by omega) z
      omega
    · intro z
      rw [z]
  have markPC := record_tail_target prepared pc (ordinal+1=positions.card) nowEnd
  have doneMem : done.mem = marked.mem := after_latch_memory marked _
  have doneReg (r : Reg) : done.getReg r = marked.getReg r := after_latch_register marked _ r
  have saved (r : Reg) (free : r ∉ recordScratch) (b : r ≠ .x7) (e : r ≠ .x8) : done.getReg r=state.getReg r :=
    (doneReg r).trans ((tail_register prepared r b e).trans (data.register r free))
  have one : prepared.getReg .x23 = 1#64 :=
    (data.register .x23 (by decide)).trans boundary.one
  have store : done.mem = (prepared.setMem (BitVec.ofNat 64 markAddr) 1#64).mem :=
    tail_mark_memory prepared (decide (ordinal+1=positions.card)) pc _ address one
  have stableWord (query : Word) (neq : query ≠ BitVec.ofNat 64 markAddr) :
      done.getMem query = prepared.getMem query := by
    have same := congrFun store query
    exact same.trans (MachineState.getMem_setMem_ne neq)
  have fit64 : MEMORY_BYTES+8 ≤ 2^64 := by decide
  have stableByte (query : Nat) (fit : query < MEMORY_BYTES) (above : trapdoorBase ≤ query) :
      done.getByte (BitVec.ofNat 64 query) = prepared.getByte (BitVec.ofNat 64 query) := by
    have different : alignToDword (BitVec.ofNat 64 query) ≠ BitVec.ofNat 64 markAddr := by
      intro same
      have aligned := aligned_dword_above trapdoorBase query (by decide) above (by omega)
      rw [same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : markAddr < 2^64)] at aligned
      omega
    simp only [MachineState.getByte, stableWord _ different]
  have markRun : RunsOpeningBlock prepared marked 5 := fun fuel coins =>
    execute_record_tail prepared pc fuel coins safe
  have nextPC : (afterLatch (recordTailPrefix prepared 5) (decide (ordinal+1=positions.card))).pc =
      (if ordinal+1=positions.card then 0x1a24 else 0x103c) :=
    @latch_target (recordTailPrefix prepared 5) (ordinal+1=positions.card) (inferInstance) markPC
  refine ⟨?_, ⟨nextPC,
    (saved .x9 (by decide) (by decide) (by decide)).trans boundary.heap,
    ?_, (saved .x22 (by decide) (by decide) (by decide)).trans boundary.nonce,
    ?_, (saved .x19 (by decide) (by decide) (by decide)).trans boundary.leaves,
    (saved .x24 (by decide) (by decide) (by decide)).trans boundary.slots, ?_,
    (saved .x17 (by decide) (by decide) (by decide)).trans boundary.endIndex,
    (saved .x26 (by decide) (by decide) (by decide)).trans boundary.marks,
    (saved .x23 (by decide) (by decide) (by decide)).trans boundary.one,
    (saved .x25 (by decide) (by decide) (by decide)).trans boundary.capHeap,
    (saved .x27 (by decide) (by decide) (by decide)).trans boundary.capLeaves,
    (saved .x20 (by decide) (by decide) (by decide)).trans boundary.proofBegin⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · have tail : RunsOpeningBlock prepared done (latchCost (decide (ordinal+1=positions.card))) :=
      run_latch prepared (ordinal+1=positions.card) markRun markPC
    have whole := data.run.next tail
    change RunsOpeningBlock state done (recordCost ordinal (decide (ordinal+1=positions.card)))
    rw [← complete_record_cost]
    exact whole
  · have pointer := (data.register .x8 (by decide)).trans boundary.index
    have bump := congrArg (fun a : Word => a+8#64) pointer
    apply (doneReg .x8).trans (post.2.1.trans (bump.trans _))
    rw [← BitVec.ofNat_add]
    congr 1
  · have nextDest := data.cursor.dest.trans (congrArg (BitVec.ofNat 64) (record_end ordinal))
    exact (doneReg .x21).trans ((tail_register prepared .x21 (by decide) (by decide)).trans nextDest)
  · intro query above below aligned
    have limit : proofBase < 2^64 := by decide
    have neq : BitVec.ofNat 64 query ≠ BitVec.ofNat 64 markAddr := by
      intro same
      have eq := nat_address_injective (by omega) (by omega) same
      omega
    exact (stableWord _ neq).trans ((data.input _ below).trans (boundary.input _ above below aligned))
  · intro node bounded
    change machineMarks done node = if node=group then 1 else machineMarks state node
    by_cases same : node = group
    · subst node
      rw [ite_eq_left rfl]
      exact (congrFun store (BitVec.ofNat 64 markAddr)).trans MachineState.getMem_setMem_eq
    · have fit := Opening.marks_before_trapdoor
      have heapFit : trapdoorBase < 2^64 := by decide
      have different : BitVec.ofNat 64 (markBase+8*node) ≠ BitVec.ofNat 64 markAddr := by
        intro sameAddr
        have eq := nat_address_injective (by omega) (by omega) sameAddr
        unfold markAddr at eq
        apply same
        omega
      have valid : markBase+8*node < proofBase := by
        have afterHeap : trapdoorBase ≤ proofBase := by decide
        omega
      rw [ite_eq_right same]
      exact (stableWord _ different).trans (data.input _ valid)
  · intro query fit above outside
    exact (stableByte query fit above).trans (data.frame query (by omega) outside)
  · intro b inside
    have fits := all_record_ends_fit ordinal (by omega)
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    have targetFit : recordBase ordinal+b < MEMORY_BYTES := by unfold recordBase recordBytes at *; omega
    exact (stableByte _ (by omega) (by unfold recordBase; omega)).trans (data.nonce b inside)
  · intro l hl b inside
    have fits := (all_sibling_copies_fit index ordinal l (by omega) hl).2.2.2
    have narrow := plain_width_le l
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    exact (stableByte _ (by omega) (by unfold siblingDestination recordBase; omega)).trans (data.sibling l hl b inside)
  · intro k hk b hb
    have fits := (all_sibling_copies_fit index ordinal (6+k) (by omega) (by omega)).2.2.2
    have width : siblingWidth (6+k) = 30 := by unfold siblingWidth; rw [if_neg (by omega), if_pos (by omega)]
    have mem : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have low : trapdoorBase ≤ proofBase := by decide
    exact (stableByte _ (by omega) (by unfold siblingDestination recordBase; omega)).trans (data.fold k hk b hb)

theorem execute_record (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal) :
    OneRecord s trapdoor positions state (runRecord state (decide (ordinal+1=positions.card))) ordinal present :=
  execute_record_with_data s trapdoor positions state (recordData state) ordinal present boundary
    (execute_record_data s layout trapdoor positions state ordinal present (boundary.start present))

end TwoPermutationPrototype.GroupedOpening
