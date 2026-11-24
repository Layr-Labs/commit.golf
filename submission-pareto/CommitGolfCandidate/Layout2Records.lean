import CommitGolfCandidate.Layout2First
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

/-! Layout 2 V2 record blocks (used by the fused opener's loop, `Layout2FusedLoop`): record `j` is written by phase
`j % 4` at `destOf j`. Its written dwords hold V1's writer dwords (`writtenByte (j%4) (srcAt loaded positions j)
(carryAt loaded positions j)`), with the sources read from the loaded state and the carry chaining through the
records; its retained bytes (salt, three mates) are those of a reference state `pass` (`v2Byte`). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase writerByte writerCarry recordSource streamRun)
open CommitGolfCandidate.Layout2Phase2 (bodyLen written writtenByte)
open Opening (sortedIndex groupsBefore)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- The position written as record `j` (0 past the end). -/
def posAt (positions : Positions) (j : Nat) : Index :=
  if h : j<positions.card then sortedIndex positions j h else ⟨0, by decide⟩

/-- Start of record `j`'s block. -/
def destOf (j : Nat) : Nat := proofBase+2136*(j/4)+phaseBase (j%4)

/-- Record `j`'s sources, read from the loaded state. -/
def srcAt (loaded : MachineState) (positions : Positions) (j : Nat) : Nat → Byte :=
  recordSource loaded (quadAddress (posAt positions j).val) (posAt positions j).val

/-- The physical carry entering record `j` (phase 0 ignores it). -/
def carryAt (loaded : MachineState) (positions : Positions) : Nat → Word
  | 0 => 0
  | j+1 => writerCarry (j%4) (srcAt loaded positions j) (carryAt loaded positions j)

/-- Byte `b` of record `i`'s block after the record loop: a written dword holds the writer's V1 dword, a
retained byte (salt, mates) the byte the pass left there. -/
def v2Byte (loaded pass : MachineState) (positions : Positions) (i b : Nat) : Byte :=
  if written ((posAt positions i).val%4) (b/8) then writtenByte (i%4) (srcAt loaded positions i) (carryAt loaded positions i) b
  else pass.getByte (BitVec.ofNat 64 (destOf i+b))

/-- The blocks of the first `count` records. -/
def L2Bytes (loaded pass : MachineState) (positions : Positions) (state : MachineState) (count : Nat) : Prop :=
  ∀ j<count, ∀ b<stride (j%4), state.getByte (BitVec.ofNat 64 (destOf j+b))=v2Byte loaded pass positions j b

/-- Cycles of the loop for the first `j` records (header 1, body `bodyLen`, tail 6). -/
def loopCost : Nat → Nat
  | 0 => 0
  | j+1 => loopCost j+bodyLen (j%4)+7

/-- Cycles of the whole record loop from word 4096 to the cap stage at 6960, for `k ≥ 1` records. -/
def l2RecordsCost (k : Nat) : Nat := loopCost k+exitCost ((k+3)%4)

theorem records_cost_batch : l2RecordsCost 128=25953 := by decide

/-- V2b's byte marks after `j` records: byte `4096+256+i` (`i < 256`) is `1` exactly when cap leaf `256+i` holds one
of the first `j` records (the form of the cap stage's `CapB.ByteMarks`). -/
def ByteMarks (positions : Positions) (state : MachineState) (j : Nat) : Prop :=
  ∀ i<256, state.getByte (BitVec.ofNat 64 (Opening.markBase+256+i))=
    BitVec.ofNat 8 (Sampling.capIsMarked (groupsBefore positions j) (256+i) 0).toNat

/-! ### Phase 0 ignores the incoming carry -/

theorem stream_phase0 (src : Nat → Byte) (c c' : Word) : streamRun 0 src c=streamRun 0 src c' := by
  have r : List.range 8=0 :: List.range' 1 7 := by decide
  simp only [streamRun, r, List.map_cons, List.foldl_cons, Layout2Phase.carryIn, ite_true]
  simp [Layout2Phase.streamStep]

theorem writer_byte_phase0 (src : Nat → Byte) (c c' : Word) (j : Nat) :
    writerByte 0 src c j=writerByte 0 src c' j := by
  simp only [writerByte, Layout2Phase.writerDwords, stream_phase0 src c c']

theorem writer_carry_phase0 (src : Nat → Byte) (c c' : Word) : writerCarry 0 src c=writerCarry 0 src c' := by
  simp only [writerCarry, stream_phase0 src c c']

theorem written_byte_phase0 (src : Nat → Byte) (c c' : Word) (j : Nat) :
    writtenByte 0 src c j=writtenByte 0 src c' j := by
  simp only [writtenByte, Layout2Phase.writerDwords, stream_phase0 src c c']

/-! ### Geometry -/

theorem dest_next (j : Nat) : destOf j+stride (j%4)=destOf (j+1) := by
  unfold destOf phaseBase stride
  have h := Nat.mod_lt j (show 4>0 by decide)
  rcases (show j%4=0 ∨ j%4=1 ∨ j%4=2 ∨ j%4=3 by omega) with e|e|e|e <;>
    rw [e] <;> simp only [ite_true, ite_false, reduceCtorEq, OfNat.ofNat_ne_zero, Nat.succ_ne_zero] <;>
    · have : (j+1)%4=(j%4+1)%4 := by omega
      have : (j+1)/4=j/4+(if j%4=3 then 1 else 0) := by split <;> omega
      split_ifs at * <;> simp_all <;> omega

theorem dest_aligned (j : Nat) : destOf j%8=0 := by
  have hp : proofBase%8=0 := by decide
  unfold destOf phaseBase
  split_ifs <;> omega

theorem dest_bound (j : Nat) : proofBase ≤ destOf j ∧ destOf j+stride (j%4) ≤ proofBase+534*(j+1) := by
  unfold destOf phaseBase stride
  have h := Nat.mod_lt j (show 4>0 by decide)
  split_ifs <;> omega

/-- Where the records end: the exit flush ends at `proofBase + 534 k`. -/
theorem dest_flush (k : Nat) (pos : 0<k) : destOf k+flushLen ((k+3)%4)=proofBase+534*k := by
  unfold destOf phaseBase flushLen
  split_ifs <;> omega

/-! ### Sources lie in the input region -/

theorem source_inside (pos k : Nat) (hp : pos<16777216) (hk : k<560) :
    trapdoorBase ≤ Layout2Phase.sourceAddress (quadAddress pos) pos k ∧
      Layout2Phase.sourceAddress (quadAddress pos) pos k<proofBase := by
  have quad := quad_address_inside pos (by unfold LENGTH LOG_LENGTH; omega)
  have xorMate (h : k<112) : (32*(pos%4)) ^^^ (32*((k-16)/32+1))<128 :=
    Nat.xor_lt_two_pow (n := 7) (by omega) (by omega)
  have node : ((4194304+pos/4) >>> ((k-112)/32)) ^^^ 1<8388608 := by
    apply Nat.xor_lt_two_pow (n := 23) _ (by decide)
    rw [Nat.shiftRight_eq_div_pow]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have tb : trapdoorBase=4294971424 := by decide
  have nb : nonceBase=9126809632 := by decide
  have pb : proofBase=13824430176 := by decide
  rw [tb, nb] at quad
  rw [tb, pb]
  unfold Layout2Phase.sourceAddress Layout2Phase.saltBase Layout2Phase.slotBase Layout2Phase.heapBase
  split_ifs with h1 h2 h3
  · omega
  · have := xorMate h2; omega
  · omega
  · omega

/-- Two states agreeing on the input region agree on every byte there. -/
theorem byte_from_input (before after : MachineState) (input : SameOpeningInput before after) (x : Nat)
    (lo : trapdoorBase ≤ x) (hi : x<proofBase) :
    after.getByte (BitVec.ofNat 64 x)=before.getByte (BitVec.ofNat 64 x) := by
  have fx : x<2^64 := by have : proofBase<2^64 := by decide
                         omega
  have tb : trapdoorBase%8=0 := by decide
  unfold MachineState.getByte
  rw [table_align_eq x fx, input (x-x%8) (by omega) (by omega) (by omega)]

theorem source_from_input (before after : MachineState) (input : SameOpeningInput before after) (pos : Nat)
    (hp : pos<16777216) (k : Nat) (hk : k<560) :
    recordSource after (quadAddress pos) pos k=recordSource before (quadAddress pos) pos k := by
  obtain ⟨lo, hi⟩ := source_inside pos k hp hk
  exact byte_from_input before after input _ lo hi

/-! ### The loop frame -/

/-- What holds at every record boundary from record `j` on: the fixed registers, input agreement, the blocks of the
records from `j` on as the pass left them (with their saved pointers), the marks and the blocks of the records
before `j`. -/
structure L2Frame (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (pass state : MachineState) (j : Nat) : Prop where
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 (indicesBase+8*j)
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  endIndex : state.getReg .x17=BitVec.ofNat 64 (indicesBase+8*positions.card)
  marks : state.getReg .x26=BitVec.ofNat 64 Opening.markBase
  one : state.getReg .x23=1#64
  capHeap : state.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27=256#64
  proofBegin : state.getReg .x20=BitVec.ofNat 64 proofBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  ahead : ∀ a, j ≤ a → a<positions.card → ∀ x<stride (a%4),
    state.getByte (BitVec.ofNat 64 (destOf a+x))=pass.getByte (BitVec.ofNat 64 (destOf a+x))
  pointer : ∀ a, j ≤ a → a<positions.card →
    state.getMem (BitVec.ofNat 64 (destOf a+16))=BitVec.ofNat 64 (quadAddress (posAt positions a).val)
  marked : ByteMarks positions state j
  bytes : L2Bytes (s.initialState .opening (trapdoor, positions)) pass positions state j

theorem pos_at_lt (positions : Positions) (j : Nat) : (posAt positions j).val<16777216 := (posAt positions j).isLt

theorem pos_at_eq (positions : Positions) (j : Nat) (hj : j<positions.card) :
    posAt positions j=sortedIndex positions j hj := by
  unfold posAt; rw [dif_pos hj]

theorem cap_group_pos (positions : Positions) (j : Nat) (hj : j<positions.card) :
    Sampling.capGroup (sortedIndex positions j hj)=256+(posAt positions j).val/65536 := by
  rw [pos_at_eq positions j hj]
  have h := (sortedIndex positions j hj).isLt
  change _<16777216 at h
  unfold Sampling.capGroup
  change (16777216+_)/65536=_
  omega

theorem mark_key_ne (g a : Nat) (hg : g<512) (ha : trapdoorBase ≤ a) (hb : a<2^64) :
    BitVec.ofNat 64 a ≠ alignToDword (BitVec.ofNat 64 (Opening.markBase+g)) := by
  rw [table_align_eq (Opening.markBase+g) (by unfold Opening.markBase; omega)]
  intro e
  have := congrArg BitVec.toNat e
  have tb : trapdoorBase=4294971424 := by decide
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by unfold Opening.markBase; omega)]
    at this
  unfold Opening.markBase at this
  omega

theorem byte_after_mark (t : MachineState) (g x : Nat) (hg : g<512) (hx : proofBase ≤ x) (fx : x<2^64) :
    (t.setByte (BitVec.ofNat 64 (Opening.markBase+g)) 1#8).getByte (BitVec.ofNat 64 x)=t.getByte (BitVec.ofNat 64 x) := by
  rw [set_byte_read, if_neg]
  intro e
  have := congrArg BitVec.toNat e
  have pb : proofBase=13824430176 := by decide
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fx, Nat.mod_eq_of_lt (by unfold Opening.markBase; omega)]
    at this
  unfold Opening.markBase at this
  omega

/-! ### The writer only reads source bytes below 560 -/

theorem dword_congr {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (k : Nat) (hk : k+8 ≤ 560) :
    Layout2Phase.dwordOf src k=Layout2Phase.dwordOf src' k := by
  unfold Layout2Phase.dwordOf
  rw [h k (by omega), h (k+1) (by omega), h (k+2) (by omega), h (k+3) (by omega), h (k+4) (by omega),
    h (k+5) (by omega), h (k+6) (by omega), h (k+7) (by omega)]

theorem stream_congr {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (p : Nat) (c : Word) :
    streamRun p src c=streamRun p src' c := by
  unfold streamRun
  congr 1
  apply List.map_congr_left
  intro b hb
  have := List.mem_range.mp hb
  exact dword_congr h _ (by omega)

theorem writer_congr {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (p : Nat) (c : Word) :
    Layout2Phase.writerDwords p src c=Layout2Phase.writerDwords p src' c := by
  have mc (n : Nat) (f : Nat → Nat) (hf : ∀ i<n, f i+8 ≤ 560) :
      List.map (fun i => Layout2Phase.dwordOf src (f i)) (List.range n)=
        List.map (fun i => Layout2Phase.dwordOf src' (f i)) (List.range n) := by
    apply List.map_congr_left; intro i hi
    exact dword_congr h _ (hf i (List.mem_range.mp hi))
  unfold Layout2Phase.writerDwords Layout2Phase.bandATails Layout2Phase.tailA
  rw [stream_congr h p c, dword_congr h 0 (by decide), dword_congr h 8 (by decide),
    dword_congr h (176+32*0+24) (by decide), dword_congr h (176+32*1+24) (by decide),
    dword_congr h (176+32*2+24) (by decide), dword_congr h (176+32*3+24) (by decide),
    mc 12 (fun i => 16+8*i) (fun i hi => by omega),
    mc 4 (fun i => 112+8*i) (fun i hi => by omega),
    mc 4 (fun i => 144+8*i) (fun i hi => by omega),
    mc 12 (fun i => 176+32*(i/3)+8*(i%3)) (fun i hi => by omega),
    mc 24 (fun i => 304+32*(i/3)+8*(i%3)) (fun i hi => by omega)]

theorem writer_byte_congr {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (p : Nat) (c : Word) (b : Nat) :
    writerByte p src c b=writerByte p src' c b := by
  unfold writerByte; rw [writer_congr h p c]

theorem written_byte_congr' {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (p : Nat) (c : Word) (b : Nat) :
    writtenByte p src c b=writtenByte p src' c b := by
  unfold writtenByte; rw [writer_congr h]

theorem writer_carry_congr {src src' : Nat → Byte} (h : ∀ k<560, src k=src' k) (p : Nat) (c : Word) :
    writerCarry p src c=writerCarry p src' c := by
  unfold writerCarry; rw [stream_congr h p c]

theorem dest_mono (i j : Nat) (h : i<j) : destOf i+stride (i%4) ≤ destOf j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [← dest_next j]
    by_cases e : i=j
    · subst e; omega
    · have := ih (by omega); omega

theorem mem_reads (a b : MachineState) (h : a.mem=b.mem) (q : Word) : a.getMem q=b.getMem q := by
  unfold MachineState.getMem; rw [h]

theorem byte_reads (a b : MachineState) (h : a.mem=b.mem) (q : Word) : a.getByte q=b.getByte q := by
  unfold MachineState.getByte; rw [mem_reads a b h]

theorem card_bound (positions : Positions) : positions.card ≤ 16777216 := by
  have h : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have l : LENGTH=16777216 := by unfold LENGTH LOG_LENGTH; norm_num
  omega

/-- The index word of record `j` in a state agreeing with the loaded input. -/
theorem index_word (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (st : MachineState)
    (input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) st) (j : Nat) (hj : j<positions.card) :
    st.getMem (BitVec.ofNat 64 (indicesBase+8*j))=BitVec.ofNat 64 (posAt positions j).val := by
  have card := card_bound positions
  have order1 := nonces_end_at_indices
  have order2 := indices_before_records
  have tb : trapdoorBase ≤ indicesBase := by decide
  have ib : indicesBase%8=0 := by decide
  rw [input _ (by omega) (by unfold LENGTH LOG_LENGTH at *; omega) (by omega), input_index s layout trapdoor positions j hj,
    pos_at_eq positions j hj]
  rfl

/-- A header leaves the loop frame (only `x6` changes). -/
theorem frame_of_regs {s : Submission} {trapdoor : BitVec (8*s.sizes.trapdoor)} {positions : Positions}
    {pass st e : MachineState} {j : Nat} (fr : L2Frame s trapdoor positions pass st j)
    (keep : ∀ r, r ≠ .x6 → e.getReg r=st.getReg r) (mem : e.mem=st.mem) :
    L2Frame s trapdoor positions pass e j := by
  have k (r : Reg) (a : r ≠ .x6) := keep r a
  refine ⟨(k .x9 (by decide)).trans fr.heap, (k .x8 (by decide)).trans fr.index,
    (k .x22 (by decide)).trans fr.nonce, (k .x19 (by decide)).trans fr.leaves,
    (k .x24 (by decide)).trans fr.slots,
    (k .x17 (by decide)).trans fr.endIndex, (k .x26 (by decide)).trans fr.marks,
    (k .x23 (by decide)).trans fr.one, (k .x25 (by decide)).trans fr.capHeap,
    (k .x27 (by decide)).trans fr.capLeaves, (k .x20 (by decide)).trans fr.proofBegin,
    fun a lo hi al => (mem_reads e st mem _).trans (fr.input a lo hi al),
    fun a ha hk x hx => (byte_reads e st mem _).trans (fr.ahead a ha hk x hx),
    fun a ha hk => (mem_reads e st mem _).trans (fr.pointer a ha hk), ?_, ?_⟩
  · intro i hi; rw [byte_reads e st mem]; exact fr.marked i hi
  · intro i hi b hb; rw [byte_reads e st mem]; exact fr.bytes i hi b hb

/-- The state at word 4096 when the records begin (the pass has just ended in `state`). -/
structure L2Start (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) : Prop where
  pc : state.pc=address 4096
  dest : state.getReg .x21=BitVec.ofNat 64 proofBase
  frame : L2Frame s trapdoor positions state state 0

end TwoPermutationPrototype.GroupedOpening.Layout2
