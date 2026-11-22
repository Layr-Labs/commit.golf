import CommitGolfCandidate.Layout2First
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

/-! Layout 2 opener: the record loop by induction over the records, against the phase-writer guarantee
`PhaseFacts openingImage p` as a hypothesis. Record `j` is written by phase `j % 4` at `destOf j`; its block is
`writerByte (j%4) (srcAt loaded positions j) (carryAt loaded positions j)`, where the sources are read from the
loaded state and the carry chains through the records. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open CommitGolfCandidate.Layout2Phase (stride phaseBase bodyWord bodyLen tailWord PhaseFacts PhaseEntry writerByte
  writerCarry recordSource streamRun)
open Opening (sortedIndex RecordMarks groupsBefore machineMarks)
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

/-- The blocks of the first `count` records. -/
def L2Bytes (loaded : MachineState) (positions : Positions) (state : MachineState) (count : Nat) : Prop :=
  ∀ j<count, ∀ b<stride (j%4), state.getByte (BitVec.ofNat 64 (destOf j+b))=
    writerByte (j%4) (srcAt loaded positions j) (carryAt loaded positions j) b

/-- Cycles of the loop body for the first `j` records (`bodyLen + 7` each). -/
def loopCost : Nat → Nat
  | 0 => 0
  | j+1 => loopCost j+bodyLen (j%4)+7

/-- Cycles of the whole record loop from word 15 to the cap preparation, for `k ≥ 1` records. -/
def l2RecordsCost (k : Nat) : Nat := 6+3*(k-1)+loopCost k+exitCost ((k+3)%4)

theorem records_cost_batch : l2RecordsCost 128=30820 := by decide

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

/-- What holds at every record boundary from record `j` on: the fixed registers, input agreement, the
pointer words, the marks and the blocks of the records before `j`. -/
structure L2Frame (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (j : Nat) : Prop where
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 (indicesBase+8*j)
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  stash : state.getReg .x18=BitVec.ofNat 64 (groupSlots+584)
  endIndex : state.getReg .x17=BitVec.ofNat 64 (indicesBase+8*positions.card)
  marks : state.getReg .x26=BitVec.ofNat 64 Opening.markBase
  one : state.getReg .x23=1#64
  capHeap : state.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27=256#64
  proofBegin : state.getReg .x20=BitVec.ofNat 64 proofBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  pointer : ∀ prior (present : prior<positions.card),
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (pointerAddress (sortedIndex positions prior present).val)) =
      BitVec.ofNat 64 (quadAddress (sortedIndex positions prior present).val)
  marked : RecordMarks positions state j
  bytes : L2Bytes (s.initialState .opening (trapdoor, positions)) positions state j

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

private theorem mark_key_ne (g a : Nat) (hg : g<512) (ha : trapdoorBase ≤ a) (hb : a<2^64) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (Opening.markBase+8*g) := by
  intro e
  have := congrArg BitVec.toNat e
  have tb : trapdoorBase=4294971424 := by decide
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by unfold Opening.markBase; omega)]
    at this
  unfold Opening.markBase at this
  omega

private theorem byte_after_mark (t : MachineState) (g x : Nat) (hg : g<512) (hx : proofBase ≤ x) (fx : x<2^64) :
    (t.setMem (BitVec.ofNat 64 (Opening.markBase+8*g)) 1#64).getByte (BitVec.ofNat 64 x)=t.getByte (BitVec.ofNat 64 x) := by
  unfold MachineState.getByte
  have pb : trapdoorBase ≤ proofBase := by decide
  have tb8 : trapdoorBase%8=0 := by decide
  rw [table_align_eq x fx, MachineState.getMem_setMem_ne (mark_key_ne g _ hg (by omega) (by omega))]

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

private theorem mem_reads (a b : MachineState) (h : a.mem=b.mem) (q : Word) : a.getMem q=b.getMem q := by
  unfold MachineState.getMem; rw [h]

private theorem byte_reads (a b : MachineState) (h : a.mem=b.mem) (q : Word) : a.getByte q=b.getByte q := by
  unfold MachineState.getByte; rw [mem_reads a b h]

theorem card_bound (positions : Positions) : positions.card ≤ 16777216 := by
  have h : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have l : LENGTH=16777216 := by unfold LENGTH LOG_LENGTH; norm_num
  omega

/-- One record from its body entry: the phase writer, then the tail with the mark and the latch. -/
theorem body_and_tail (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (e : MachineState) (j : Nat)
    (hj : j<positions.card) (fr : L2Frame s trapdoor positions e j) (pc : e.pc=address (bodyWord (j%4)))
    (dest : e.getReg .x21=BitVec.ofNat 64 (destOf j))
    (x6 : e.getReg .x6=BitVec.ofNat 64 (posAt positions j).val)
    (x7 : e.getReg .x7=BitVec.ofNat 64 (nonceBase+16*(posAt positions j).val))
    (carry : j%4 ≠ 0 → e.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions j) :
    ∃ u, RunsOpeningBlock e u (bodyLen (j%4)+7) ∧ L2Frame s trapdoor positions u (j+1) ∧
      u.pc=address (if j+1=positions.card then exitWord (j%4) else hdrWord ((j+1)%4)) ∧
      u.getReg .x21=BitVec.ofNat 64 (destOf (j+1)) ∧
      ((j+1)%4 ≠ 0 → u.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions (j+1)) := by
  have hp4 : j%4<4 := Nat.mod_lt _ (by decide)
  have posLt := pos_at_lt positions j
  have card := card_bound positions
  have bound := dest_bound j
  have quad := quad_address_inside (posAt positions j).val (by unfold LENGTH LOG_LENGTH; omega)
  have ptr := pointer_address_inside (posAt positions j).val (by unfold LENGTH LOG_LENGTH; omega)
  have order1 := nonces_end_at_indices
  have order2 := indices_before_records
  have pointerE : e.getMem (BitVec.ofNat 64 (Layout2Phase.slotBase+1024*((posAt positions j).val/4)+712))=
      BitVec.ofNat 64 (quadAddress (posAt positions j).val) := by
    have eq : Layout2Phase.slotBase+1024*((posAt positions j).val/4)+712=pointerAddress (posAt positions j).val := by
      unfold pointerAddress; rw [slot_base]
    rw [eq, fr.input _ ptr.2.1 (by omega) ptr.1]
    have h := fr.pointer j hj
    rw [← pos_at_eq positions j hj] at h
    exact h
  have mem36 : proofBase+534*(j+1) ≤ MEMORY_BYTES := by
    have : proofBase+534*16777216 ≤ 68719476736 := by decide
    unfold MEMORY_BYTES; omega
  have entry : PhaseEntry e (j%4) (posAt positions j).val (destOf j) (quadAddress (posAt positions j).val)
      (e.getReg .x11) :=
    { phase := hp4, pc := pc, index := posLt, posReg := x6,
      salt := by rw [x7, salt_base], dest := dest, aligned := dest_aligned j,
      room := ⟨by rw [record_base0]; exact bound.1, by omega⟩,
      carry := rfl, heap := by rw [fr.heap, heap_base], slots := by rw [fr.stash, slot_base],
      leaves := fr.leaves, pointer := pointerE,
      quad := ⟨quad.1, by rw [heap_base]; exact quad.2.1, by rw [salt_base]; exact quad.2.2⟩ }
  obtain ⟨t, runT, pcT, bytesT, carryT, x6T, keepT, frameT, rawT⟩ :=
    phases (j%4) hp4 e (posAt positions j).val (destOf j) (quadAddress (posAt positions j).val) _ entry
  have kt (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h28 : r ≠ .x28)
      (h31 : r ≠ .x31) : t.getReg r=e.getReg r := keepT r h6 h7 h10 h11 h28 h31
  obtain ⟨runU, pcU, x21U, x8U, memU, keepU⟩ := tail_step (j%4) hp4 t (destOf j) (posAt positions j).val j
    positions.card pcT
    (by rw [kt .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact dest)
    x6T posLt
    (by rw [kt .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fr.index)
    (by rw [kt .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fr.endIndex)
    hj card
    (by rw [kt .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fr.marks)
    (by rw [kt .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact fr.one)
  let u := walkRows t (tailRows (j%4))
  have runT' : RunsOpeningBlock e t (bodyLen (j%4)) := runT
  have mod1 : (j%4+1)%4=(j+1)%4 := by omega
  rw [mod1] at pcU
  have ku (r : Reg) (a : r ≠ .x21) (b : r ≠ .x6) (c : r ≠ .x7) (d : r ≠ .x8) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
      (h28 : r ≠ .x28) (h31 : r ≠ .x31) : u.getReg r=e.getReg r :=
    (keepU r a b c d).trans (kt r b c h10 h11 h28 h31)
  have g := 256+(posAt positions j).val/65536
  have gLt : 256+(posAt positions j).val/65536<512 := by omega
  -- memory facts of `u`
  have memAt (q : Word) : u.getMem q=(t.setMem (BitVec.ofNat 64 (Opening.markBase+8*(256+(posAt positions j).val/65536))) 1#64).getMem q :=
    mem_reads _ _ memU q
  have srcEq : ∀ k<560, recordSource e (quadAddress (posAt positions j).val) (posAt positions j).val k=
      srcAt (s.initialState .opening (trapdoor, positions)) positions j k :=
    fun k hk => source_from_input _ e fr.input _ posLt k hk
  have carryEq : writerCarry (j%4) (recordSource e (quadAddress (posAt positions j).val) (posAt positions j).val)
      (e.getReg .x11)=carryAt (s.initialState .opening (trapdoor, positions)) positions (j+1) := by
    rw [writer_carry_congr srcEq]
    show _=writerCarry (j%4) _ _
    by_cases z : j%4=0
    · rw [z]; exact writer_carry_phase0 _ _ _
    · rw [carry z]
  refine ⟨u, runT'.next runU, ⟨?_, x8U, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fr.pointer, ?_, ?_⟩, pcU, ?_, ?_⟩
  · rw [ku .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.heap
  · rw [ku .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.nonce
  · rw [ku .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.leaves
  · rw [ku .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.slots
  · rw [ku .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.stash
  · rw [ku .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.endIndex
  · rw [ku .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.marks
  · rw [ku .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.one
  · rw [ku .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.capHeap
  · rw [ku .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.capLeaves
  · rw [ku .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact fr.proofBegin
  · -- input
    intro a lo hi al
    have fa : a<2^64 := by have : proofBase<2^64 := by decide
                           omega
    rw [memAt, MachineState.getMem_setMem_ne (mark_key_ne _ a gLt lo fa),
      rawT _ (Or.inl (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fa]; omega))]
    exact fr.input a lo hi al
  · -- marks
    intro node bounded
    have fm : Opening.markBase+8*node<2^64 := by unfold Opening.markBase; omega
    unfold machineMarks
    rw [memAt]
    rw [Opening.groups_before_next positions j hj, cap_group_pos positions j hj]
    by_cases same : node=256+(posAt positions j).val/65536
    · subst same
      rw [MachineState.getMem_setMem_eq]
      simp
    · have ne : BitVec.ofNat 64 (Opening.markBase+8*node) ≠ BitVec.ofNat 64 (Opening.markBase+8*(256+(posAt positions j).val/65536)) := by
        intro e; have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fm, Nat.mod_eq_of_lt (by unfold Opening.markBase; omega)] at this
        omega
      rw [MachineState.getMem_setMem_ne ne, rawT _ (Or.inl (by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fm]
        have : Opening.markBase+8*512 ≤ proofBase := by decide
        omega))]
      have old := fr.marked node bounded
      unfold machineMarks at old
      rw [old]
      simp [List.mem_append, same]
  · -- bytes
    intro i hi b hb
    have pb : proofBase+534*16777216<2^64 := by decide
    have fx : destOf i+b<2^64 := by have := dest_bound i; omega
    have above : proofBase ≤ destOf i+b := by have := dest_bound i; omega
    rw [byte_reads u _ memU, byte_after_mark t _ _ gLt above fx]
    by_cases older : i<j
    · have mono := dest_mono i j older
      rw [frameT _ fx (Or.inl (by omega))]
      exact fr.bytes i older b hb
    · have same : i=j := by omega
      subst same
      rw [bytesT b hb, writer_byte_congr srcEq]
      by_cases z : i%4=0
      · rw [z]; exact writer_byte_phase0 _ _ _ _
      · rw [carry z]
  · -- x21
    rw [x21U, dest_next]
  · -- carry
    intro _
    rw [keepU .x11 (by decide) (by decide) (by decide) (by decide), carryT]
    exact carryEq

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

/-- A header leaves the loop frame (only `x6`, `x7` change). -/
theorem frame_of_regs {s : Submission} {trapdoor : BitVec (8*s.sizes.trapdoor)} {positions : Positions}
    {st e : MachineState} {j : Nat} (fr : L2Frame s trapdoor positions st j)
    (keep : ∀ r, r ≠ .x6 → r ≠ .x7 → e.getReg r=st.getReg r) (mem : e.mem=st.mem) :
    L2Frame s trapdoor positions e j := by
  have k (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) := keep r a b
  refine ⟨(k .x9 (by decide) (by decide)).trans fr.heap, (k .x8 (by decide) (by decide)).trans fr.index,
    (k .x22 (by decide) (by decide)).trans fr.nonce, (k .x19 (by decide) (by decide)).trans fr.leaves,
    (k .x24 (by decide) (by decide)).trans fr.slots, (k .x18 (by decide) (by decide)).trans fr.stash,
    (k .x17 (by decide) (by decide)).trans fr.endIndex, (k .x26 (by decide) (by decide)).trans fr.marks,
    (k .x23 (by decide) (by decide)).trans fr.one, (k .x25 (by decide) (by decide)).trans fr.capHeap,
    (k .x27 (by decide) (by decide)).trans fr.capLeaves, (k .x20 (by decide) (by decide)).trans fr.proofBegin,
    fun a lo hi al => (mem_reads e st mem _).trans (fr.input a lo hi al), fr.pointer, ?_, ?_⟩
  · intro node bounded; unfold machineMarks; rw [mem_reads e st mem]; exact fr.marked node bounded
  · intro i hi b hb; rw [byte_reads e st mem]; exact fr.bytes i hi b hb

/-- A record after the first: its header, body and tail. -/
theorem record_step (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (st : MachineState) (j : Nat)
    (hj : j<positions.card) (fr : L2Frame s trapdoor positions st j) (pc : st.pc=address (hdrWord (j%4)))
    (dest : st.getReg .x21=BitVec.ofNat 64 (destOf j))
    (carry : j%4 ≠ 0 → st.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions j) :
    ∃ u, RunsOpeningBlock st u (3+(bodyLen (j%4)+7)) ∧ L2Frame s trapdoor positions u (j+1) ∧
      u.pc=address (if j+1=positions.card then exitWord (j%4) else hdrWord ((j+1)%4)) ∧
      u.getReg .x21=BitVec.ofNat 64 (destOf (j+1)) ∧
      ((j+1)%4 ≠ 0 → u.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions (j+1)) := by
  have card := card_bound positions
  have order := indices_before_records
  have ib : indicesBase%8=0 := by decide
  obtain ⟨r1, p1, x6, x7, m1, k1⟩ := hdr_step (j%4) (Nat.mod_lt _ (by decide)) st (indicesBase+8*j)
    (posAt positions j).val pc fr.index (by omega)
    (by have : indicesBase+8*16777216+8 ≤ MEMORY_BYTES := by decide
        omega)
    (index_word s layout trapdoor positions st fr.input j hj) (pos_at_lt positions j) fr.nonce
  have fe := frame_of_regs fr k1 m1
  obtain ⟨u, r2, fu, pu, du, cu⟩ := body_and_tail phases s trapdoor positions _ j hj fe p1
    ((k1 .x21 (by decide) (by decide)).trans dest) x6 x7
    (fun z => (k1 .x11 (by decide) (by decide)).trans (carry z))
  exact ⟨u, r1.next r2, fu, pu, du, cu⟩

/-- The state at word 15 when the records begin. -/
structure L2Start (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) : Prop where
  pc : state.pc=address 15
  heap : state.getReg .x9=BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8=BitVec.ofNat 64 indicesBase
  nonce : state.getReg .x22=BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21=BitVec.ofNat 64 proofBase
  leaves : state.getReg .x19=BitVec.ofNat 64 4194304
  slots : state.getReg .x24=BitVec.ofNat 64 groupSlots
  endIndex : state.getReg .x17=BitVec.ofNat 64 (indicesBase+8*positions.card)
  marks : state.getReg .x26=BitVec.ofNat 64 Opening.markBase
  one : state.getReg .x23=1#64
  capHeap : state.getReg .x25=BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27=256#64
  proofBegin : state.getReg .x20=BitVec.ofNat 64 proofBase
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  pointer : ∀ prior (present : prior<positions.card),
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (pointerAddress (sortedIndex positions prior present).val)) =
      BitVec.ofNat 64 (quadAddress (sortedIndex positions prior present).val)
  marked : RecordMarks positions state 0

/-- The first record: words 15..18, the entry stub, the phase-0 body and its tail. -/
theorem first_record (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState)
    (positive : 0<positions.card) (start : L2Start s trapdoor positions begin) :
    ∃ u, RunsOpeningBlock begin u (6+(bodyLen 0+7)) ∧ L2Frame s trapdoor positions u 1 ∧
      u.pc=address (if 1=positions.card then exitWord 0 else hdrWord 1) ∧
      u.getReg .x21=BitVec.ofNat 64 (destOf 1) ∧
      (1%4 ≠ 0 → u.getReg .x11=carryAt (s.initialState .opening (trapdoor, positions)) positions 1) := by
  have w0 := index_word s layout trapdoor positions begin start.input 0 positive
  simp only [Nat.mul_zero, Nat.add_zero] at w0
  obtain ⟨r1, p1, x6, x7, x18, m1, k1⟩ := first_step begin (posAt positions 0).val start.pc start.index w0
    (pos_at_lt positions 0) start.nonce start.slots
  let e := walkRows begin firstRows
  have k (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x18) : e.getReg r=begin.getReg r := k1 r a b c
  have fe : L2Frame s trapdoor positions e 0 :=
    ⟨(k .x9 (by decide) (by decide) (by decide)).trans start.heap,
     by rw [k .x8 (by decide) (by decide) (by decide), start.index]; rfl,
     (k .x22 (by decide) (by decide) (by decide)).trans start.nonce,
     (k .x19 (by decide) (by decide) (by decide)).trans start.leaves,
     (k .x24 (by decide) (by decide) (by decide)).trans start.slots, x18,
     (k .x17 (by decide) (by decide) (by decide)).trans start.endIndex,
     (k .x26 (by decide) (by decide) (by decide)).trans start.marks,
     (k .x23 (by decide) (by decide) (by decide)).trans start.one,
     (k .x25 (by decide) (by decide) (by decide)).trans start.capHeap,
     (k .x27 (by decide) (by decide) (by decide)).trans start.capLeaves,
     (k .x20 (by decide) (by decide) (by decide)).trans start.proofBegin,
     fun a lo hi al => (mem_reads e begin m1 _).trans (start.input a lo hi al), start.pointer,
     fun node bounded => by unfold machineMarks; rw [mem_reads e begin m1]; exact start.marked node bounded,
     fun i hi => absurd hi (by omega)⟩
  obtain ⟨u, r2, fu, pu, du, cu⟩ := body_and_tail phases s trapdoor positions e 0 positive fe p1
    (by rw [k .x21 (by decide) (by decide) (by decide), start.dest]; rfl) x6 x7 (fun z => absurd rfl z)
  exact ⟨u, r1.next r2, fu, pu, du, cu⟩

end TwoPermutationPrototype.GroupedOpening.Layout2
