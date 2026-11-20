import CommitGolfCandidate.TwoPermutationPackedCapFrontier
import CommitGolfCandidate.TwoPermutationPackedCapFrontierPrefix
import CommitGolfCandidate.TwoPermutationPackedCopy
import CommitGolfCandidate.K3C4CapMask
import CommitGolfCandidate.K3C4CapEighth
import RiscvZkvm.Rv64.Logic.ByteOps

/-! # The packed frontier read (T238)

From word 294 (`FrontierReady`): head 294, 295, 296 `jal <631>`, 631 `bne x30,x0,<692>` (`frontierHead`).
Normal node (x30 ≠ 0, `first % 8 ≠ 7`): 692..694 + 297 (`normalGuard`), copy 30 B 298..327 (FieldSite.boundary),
328 `jal <695>`, mask 695..698 (`maskAfter _ .x7 28`), 699 `jal <329>`, 329 `addi x21,x21,30` -> 330. 45 steps.
Last node (x30 = 0): 632..633 (`eighthGuard`), then `eighthRead` (copy 28 B 634..661, gather 662..687,
688 `sw x31,28(x7)`, 689 `addi x21,x21,28`, 690 `addi x30,x0,7`, 691 `jal <330>`). 64 steps. Short: 8 / 6 steps to 364. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed ProjectedHalfword
open TwoPermutationPrototype.Checker (capRootAt)
open TwoPermutationPrototype.Sampling (pad238)
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

attribute [local irreducible] execute

private def slotAddress (node : Nat) : Nat := 8*(2048+4*node)

/-! ### Register and memory facts that hold for every state -/

private theorem head_mem (s : MachineState) : (frontierHead s).mem = s.mem := by
  simp [frontierHead, frontierHeadCode, execInstrBr, signExtend13, signExtend21]
  split <;> rfl

private theorem normal_guard_mem (s : MachineState) : (normalGuard s).mem = s.mem := by
  simp [normalGuard, normalGuardCode, execInstrBr, signExtend12, signExtend13, signExtend21]
  split <;> rfl

private theorem eighth_guard_mem (s : MachineState) : (eighthGuard s).mem = s.mem := by
  simp [eighthGuard, eighthGuardCode, execInstrBr, signExtend12, signExtend13]
  split <;> rfl

private theorem mask_register (s : MachineState) (r : Reg) (o : BitVec 12) (q : Reg) (keep : q ≠ .x31) :
    (maskAfter s r o).getReg q = s.getReg q := by
  simp only [maskAfter, execInstrBr, MachineState.setWord32, MachineState.getReg_setPC, arm_getReg_set_mem,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm keep)]

private theorem finish_register (s : MachineState) (q : Reg) (keep : q ≠ .x21) :
    (frontierFinish s).getReg q = s.getReg q := by
  unfold frontierFinish
  rw [MachineState.getReg_setPC, Opening.getReg_setReg, ite_eq_right (by simp [Ne.symm keep])]

private theorem finish_x21 (s : MachineState) : (frontierFinish s).getReg .x21 = s.getReg .x21+30#64 := by
  unfold frontierFinish
  rw [MachineState.getReg_setPC, Opening.getReg_setReg, ite_eq_left (by decide : Reg.x21 = .x21 ∧ Reg.x21 ≠ .x0)]

private theorem read_buffer_of_mem {a b : MachineState} (same : a.mem = b.mem) : readBuffer a = readBuffer b := by
  funext address count
  unfold readBuffer
  simp only [MachineState.getByte, MachineState.getMem, same]

private theorem memory_view_of_mem {a b : MachineState} (same : a.mem = b.mem) : memoryView a = memoryView b := by
  funext word
  simp only [memoryView, MachineState.getMem, same]

private theorem packed_node_of_mem {a b : MachineState} (same : a.mem = b.mem) (base k : Nat) :
    packedNodeAt a base k = packedNodeAt b base k := by
  unfold packedNodeAt packedSpareAt
  rw [read_buffer_of_mem same]

/-! ### The node's slot and the proof pointer -/

private theorem slot_register (s : MachineState) (node : Nat)
    (nodeReg : s.getReg .x6 = BitVec.ofNat 64 node) (capReg : s.getReg .x25 = 16384#64) :
    s.getReg .x25 + (s.getReg .x6 <<< 5) = BitVec.ofNat 64 (slotAddress node) := by
  rw [nodeReg, capReg, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 node*BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  unfold slotAddress
  omega

private theorem head_slot {s : MachineState} {node start first : Nat} (ready : FrontierReady s node start first) :
    (frontierHead s).getReg .x7 = BitVec.ofNat 64 (slotAddress node) :=
  (frontier_head_post s ready.pc).2.1.trans (slot_register s node ready.nodeReg ready.capReg)

private theorem countdown_zero {s : MachineState} {node start first : Nat}
    (ready : FrontierReady s node start first) : s.getReg .x30 = 0#64 ↔ first % 8 = 7 := by
  rw [ready.countdown]
  have small : first % 8 < 8 := Nat.mod_lt _ (by decide)
  constructor
  · intro zero
    have value := congrArg BitVec.toNat zero
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at value
    change 7 - first % 8 = 0 at value
    omega
  · intro last
    rw [last]

private theorem pointer_step (start first width : Nat) (bytes : capSlotBytes first = width) :
    BitVec.ofNat 64 (start+capPackedBytes first) + BitVec.ofNat 64 width =
      BitVec.ofNat 64 (start+capPackedBytes (first+1)) := by
  rw [← BitVec.ofNat_add, cap_packed_bytes_succ, bytes]
  congr 1
  omega

private theorem normal_width {first : Nat} (normal : first % 8 ≠ 7) : capSlotBytes first = 30 := by
  unfold capSlotBytes
  rw [if_neg normal]

private theorem eighth_width {first : Nat} (last : first % 8 = 7) : capSlotBytes first = 28 := by
  unfold capSlotBytes
  rw [if_pos last]

/-! ### The normal node: copy 30 bytes, mask bits 238.., advance the pointer -/

private def normalCode : CopyCode where
  image := packedImage
  start := 298
  count := 15
  source := .x21
  dest := .x7
  destOffset := 0
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun i hi s pc => field_fetch_load .boundary i hi s pc
  store := fun i hi s pc => field_fetch_store .boundary i hi s pc

/-- From word 298: the copy, `jal <695>`, the mask, `jal <329>`, `addi x21,x21,30`. -/
def normalTail (s : MachineState) : MachineState :=
  frontierFinish ((maskAfter ((copyField normalCode s).setPC (BitVec.ofNat 64 (4096+4*695))) .x7 28).setPC
    (BitVec.ofNat 64 (4096+4*329)))

/-- One normal (30-byte) frontier node from word 294. -/
def normalRead (s : MachineState) : MachineState := normalTail (normalGuard (frontierHead s))

private theorem normal_tail_register (s : MachineState) (q : Reg) (a : q ≠ .x21) (b : q ≠ .x31) :
    (normalTail s).getReg q = s.getReg q := by
  unfold normalTail
  rw [finish_register _ _ a, MachineState.getReg_setPC, mask_register _ _ _ _ b, MachineState.getReg_setPC,
    copy_field_register _ _ _ b]

private structure NormalTailFacts (s : MachineState) (P slot : Nat) : Prop where
  hop : GroupHop s (normalTail s) 37
  pc : (normalTail s).pc = 0x1528
  proof : (normalTail s).getReg .x21 = s.getReg .x21 + 30#64
  digest : readBuffer (normalTail s) slot 32 = (0 : BitVec 18) ++ (readBuffer s P 30).extractLsb' 0 238
  frame : ∀ word < 2^61, 8*word+8 ≤ slot ∨ slot+32 ≤ 8*word → memoryView (normalTail s) word = memoryView s word

private theorem pad238_read (t : MachineState) (a : Nat) :
    pad238 (readBuffer t a 32) = (0 : BitVec 18) ++ (readBuffer t a 30).extractLsb' 0 238 := by
  have slice := read_buffer_slice t a 32 0 30 (by decide)
  unfold pad238
  apply congrArg (fun v : BitVec 238 => (0 : BitVec 18) ++ v)
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have small : i < 8*30 := by omega
  have bit := congrArg (fun v : BitVec (8*30) => v.getLsbD i) slice
  simp only [BitVec.getLsbD_extractLsb', Nat.mul_zero, Nat.zero_add, Nat.add_zero, small, hi, decide_true,
    Bool.true_and] at bit ⊢
  exact bit

attribute [local irreducible] copyField maskAfter

private theorem normal_tail_facts (s : MachineState) (P slot : Nat)
    (ready : CopyReady normalCode s P slot 0) (dst : s.getReg .x7 = BitVec.ofNat 64 slot)
    (aligned : slot % 8 = 0) (below : slot+32 ≤ P) (fits : P+30 ≤ MEMORY_BYTES) :
    NormalTailFacts s P slot := by
  have memory64 : MEMORY_BYTES < 2^64 := by decide
  let copied := copyField normalCode s
  let jumped := copied.setPC (BitVec.ofNat 64 (4096+4*695))
  let masked := maskAfter jumped .x7 28
  let back := masked.setPC (BitVec.ofNat 64 (4096+4*329))
  have copyPC : copied.pc = BitVec.ofNat 64 (4096+4*328) := copy_field_pc normalCode s P slot ready
  have copiedMem : copied.mem = (copyLoopMemory false 15 s (BitVec.ofNat 64 P) (BitVec.ofNat 64 slot)).mem :=
    copy_field_memory normalCode s P slot ready
  have copyDst : copied.getReg .x7 = BitVec.ofNat 64 slot := (copy_field_register _ _ .x7 (by decide)).trans dst
  have address : jumped.getReg .x7 + signExtend12 28 = BitVec.ofNat 64 (slot+24+4) := by
    rw [MachineState.getReg_setPC, copyDst, show signExtend12 28 = BitVec.ofNat 64 28 by decide, ← BitVec.ofNat_add]
  have post := mask_post jumped .x7 28 (slot+24) address (by omega) (by decide)
  have maskedPC : masked.pc = BitVec.ofNat 64 (4096+4*699) := by
    rw [post.pc]
    rfl
  have copyHop : GroupHop s copied 30 := fun fuel => copy_field_execute normalCode s P slot ready fuel false
  have jumpHop : GroupHop copied jumped 1 := cap_jal_hop copied 328 695 1468 (by decide) copyPC rfl (by decide)
  have maskHop : GroupHop jumped masked 4 :=
    execute_mask jumped 695 .x7 28 (slot+24) (by decide) rfl rfl rfl rfl rfl address (by omega) (by omega)
      (by decide)
  have backHop : GroupHop masked back 1 := cap_jal_hop masked 699 329 2095672 (by decide) maskedPC rfl (by decide)
  have finishHop : GroupHop back (frontierFinish back) 1 := fun fuel => execute_frontier_finish back rfl fuel
  -- memory: the copy writes the slot's bytes 0..30, the mask the slot's top doubleword
  obtain ⟨bytes, frame⟩ := forward_memory 15 s P slot (by omega) (by omega) (by omega) ready.srcAligned ready.dstAligned
  have copiedByte (i : Nat) (inside : i < 30) :
      copied.getByte (BitVec.ofNat 64 (slot+i)) = s.getByte (BitVec.ofNat 64 (P+i)) := by
    simpa only [MachineState.getByte, MachineState.getMem, copiedMem] using bytes i inside
  have prefix30 : readBuffer jumped slot 30 = readBuffer s P 30 := by
    have loaded := read_serialized_slice jumped (readBuffer s P 30) slot 0 30 (by
      intro j inside
      rw [Nat.zero_add, read_buffer_byte s P 30 j inside]
      exact copiedByte j inside)
    simpa only [Nat.mul_zero, BitVec.extractLsb'_eq_self] using loaded
  have maskedRead : readBuffer masked slot 32 = pad238 (readBuffer jumped slot 32) :=
    masked_slot_digest jumped .x7 slot (readBuffer jumped slot 32) aligned (by omega) address (by decide)
      (fun k inside => (read_digest_word jumped slot k aligned inside).symm)
  have sameMem : (normalTail s).mem = masked.mem := rfl
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · exact (((copyHop.thenDo jumpHop).thenDo maskHop).thenDo backHop).thenDo finishHop
  · change (frontierFinish back).getReg .x21 = _
    rw [finish_x21, MachineState.getReg_setPC, mask_register _ _ _ _ (by decide), MachineState.getReg_setPC,
      copy_field_register _ _ _ (by decide)]
  · rw [read_buffer_of_mem sameMem, maskedRead, pad238_read, prefix30]
  · intro word bounded outside
    rw [memory_view_of_mem sameMem]
    have maskFrame := masked_slot_frame jumped .x7 slot address aligned (by decide) word (by omega) (by omega)
      (by omega)
    rw [maskFrame]
    change memoryView copied word = memoryView s word
    apply word_eq_of_byte_frame
    intro i small
    have untouched : ∀ j < 2*15, BitVec.ofNat 64 (8*word+i) ≠ BitVec.ofNat 64 (slot+j) := by
      intro j hj same
      have eq := Opening.nat_address_injective (by omega) (by omega) same
      omega
    simpa only [MachineState.getByte, MachineState.getMem, copiedMem] using frame _ untouched

/-! ### The kernel -/

/-- After one frontier node read from word 294 (dispatch on the countdown `x30`). -/
noncomputable def packedFrontierAfter (s : MachineState) : MachineState :=
  if s.getReg .x30 = 0#64 then eighthRead (eighthGuard (frontierHead s)) else normalRead s

/-- The rejecting state at word 364 when the read is short. -/
def packedFrontierRejected (s : MachineState) : MachineState :=
  if s.getReg .x30 = 0#64 then eighthGuard (frontierHead s) else normalGuard (frontierHead s)

private theorem after_normal {s : MachineState} (normal : s.getReg .x30 ≠ 0#64) :
    packedFrontierAfter s = normalRead s := by
  unfold packedFrontierAfter
  rw [if_neg normal]

private theorem after_eighth {s : MachineState} (last : s.getReg .x30 = 0#64) :
    packedFrontierAfter s = eighthRead (eighthGuard (frontierHead s)) := by
  unfold packedFrontierAfter
  rw [if_pos last]

private theorem rejected_normal {s : MachineState} (normal : s.getReg .x30 ≠ 0#64) :
    packedFrontierRejected s = normalGuard (frontierHead s) := by
  unfold packedFrontierRejected
  rw [if_neg normal]

private theorem rejected_eighth {s : MachineState} (last : s.getReg .x30 = 0#64) :
    packedFrontierRejected s = eighthGuard (frontierHead s) := by
  unfold packedFrontierRejected
  rw [if_pos last]

/-- Everything a ready normal read needs, from `FrontierReady` and a passing bound. -/
private structure NormalCase (s : MachineState) (node start first : Nat) : Prop where
  normal : first % 8 ≠ 7
  count : s.getReg .x30 ≠ 0#64
  headPC : (frontierHead s).pc = 0x1ad0
  guardPC : (normalGuard (frontierHead s)).pc = 0x14a8
  facts : NormalTailFacts (normalGuard (frontierHead s)) (start+capPackedBytes first) (slotAddress node)

private theorem normal_case {s : MachineState} {node start first : Nat} (ready : FrontierReady s node start first)
    (normal : first % 8 ≠ 7) (fits : ¬ FrontierShort s start first) : NormalCase s node start first := by
  have count : s.getReg .x30 ≠ 0#64 := fun zero => normal ((countdown_zero ready).mp zero)
  let h := frontierHead s
  let g := normalGuard h
  have headPC : h.pc = 0x1ad0 := by
    rw [(frontier_head_post s ready.pc).1, if_neg count]
  have hRegs (r : Reg) (keep : r ≠ .x7) : h.getReg r = s.getReg r := frontier_head_register s r keep
  have guardPost := normal_guard_post h headPC
  have notShort : ¬ h.getReg .x22 < h.getReg .x21+30#64 := by
    rw [hRegs _ (by decide), hRegs _ (by decide), ready.proofReg]
    change ¬ s.getReg .x22 < BitVec.ofNat 64 (start+capPackedBytes first) + BitVec.ofNat 64 30
    rw [pointer_step start first 30 (normal_width normal)]
    exact fits
  have guardPC : g.pc = 0x14a8 := by rw [guardPost.1, if_neg notShort]
  have gReg (r : Reg) (a : r ≠ .x7) (b : r ≠ .x30) (c : r ≠ .x28) : g.getReg r = s.getReg r :=
    (normal_guard_register h r b c).trans (hRegs r a)
  have gSlot : g.getReg .x7 = BitVec.ofNat 64 (slotAddress node) :=
    (normal_guard_register h .x7 (by decide) (by decide)).trans (head_slot ready)
  have gProof : g.getReg .x21 = BitVec.ofNat 64 (start+capPackedBytes first) :=
    (gReg .x21 (by decide) (by decide) (by decide)).trans ready.proofReg
  have bound := ready.below
  have roomAll := ready.room
  have growth : capPackedBytes (first+1) = capPackedBytes first + 30 := by
    rw [cap_packed_bytes_succ, normal_width normal]
  have even : (start+capPackedBytes first) % 2 = 0 := by
    have := cap_packed_bytes_even first
    have := ready.even
    omega
  have copyReady : CopyReady normalCode g (start+capPackedBytes first) (slotAddress node) 0 := by
    refine ⟨?_, gProof, ?_, ?_, ?_, even, ?_⟩
    · rw [guardPC]; rfl
    · exact (BitVec.add_zero _).trans gSlot
    · change start+capPackedBytes first+2*15 ≤ MEMORY_BYTES
      omega
    · change slotAddress node+2*15 ≤ MEMORY_BYTES
      have : 32768 ≤ MEMORY_BYTES := by decide
      unfold slotAddress; omega
    · change slotAddress node % 2 = 0
      unfold slotAddress; omega
  have facts := normal_tail_facts g (start+capPackedBytes first) (slotAddress node) copyReady gSlot
    (by unfold slotAddress; omega) (by have := ready.above; unfold slotAddress; omega) (by omega)
  exact ⟨normal, count, headPC, guardPC, facts⟩

/-- Everything a ready last-of-group read needs. -/
private structure EighthCase (s : MachineState) (node start first : Nat) : Prop where
  last : first % 8 = 7
  count : s.getReg .x30 = 0#64
  headPC : (frontierHead s).pc = 0x19e0
  guardPC : (eighthGuard (frontierHead s)).pc = 0x19e8
  slot : (eighthGuard (frontierHead s)).getReg .x7 = BitVec.ofNat 64 (slotAddress node)
  proof : (eighthGuard (frontierHead s)).getReg .x21 = BitVec.ofNat 64 (start+capPackedBytes first)
  mem : (eighthGuard (frontierHead s)).mem = s.mem
  regs : ∀ r, r ≠ .x7 → r ≠ .x28 → (eighthGuard (frontierHead s)).getReg r = s.getReg r

private theorem eighth_case {s : MachineState} {node start first : Nat} (ready : FrontierReady s node start first)
    (last : first % 8 = 7) (fits : ¬ FrontierShort s start first) : EighthCase s node start first := by
  have count : s.getReg .x30 = 0#64 := (countdown_zero ready).mpr last
  let h := frontierHead s
  have headPC : h.pc = 0x19e0 := by
    rw [(frontier_head_post s ready.pc).1, if_pos count]
  have hRegs (r : Reg) (keep : r ≠ .x7) : h.getReg r = s.getReg r := frontier_head_register s r keep
  have guardPost := eighth_guard_post h headPC
  have notShort : ¬ h.getReg .x22 < h.getReg .x21+28#64 := by
    rw [hRegs _ (by decide), hRegs _ (by decide), ready.proofReg]
    change ¬ s.getReg .x22 < BitVec.ofNat 64 (start+capPackedBytes first) + BitVec.ofNat 64 28
    rw [pointer_step start first 28 (eighth_width last)]
    exact fits
  refine ⟨last, count, headPC, ?_, ?_, ?_, ?_, ?_⟩
  · rw [guardPost.1, if_neg notShort]
  · exact (eighth_guard_register h .x7 (by decide)).trans (head_slot ready)
  · exact (eighth_guard_register h .x21 (by decide)).trans ((hRegs .x21 (by decide)).trans ready.proofReg)
  · exact guardPost.2.2.trans (head_mem s)
  · intro r a b
    exact (eighth_guard_register h r b).trans (hRegs r a)

private theorem eighth_inputs {s : MachineState} {node start first : Nat} (ready : FrontierReady s node start first)
    (last : first % 8 = 7) :
    slotAddress node % 8 = 0 ∧ slotAddress node+32 ≤ 32768 ∧ 32768+210 ≤ start+capPackedBytes first ∧
      (start+capPackedBytes first) % 2 = 0 ∧ start+capPackedBytes first+28 ≤ MEMORY_BYTES ∧
      start+capPackedBytes first-210 = start+238*(first/8) := by
  have bound := ready.below
  have above := ready.above
  have roomAll := ready.room
  have growth : capPackedBytes (first+1) = capPackedBytes first + 28 := by
    rw [cap_packed_bytes_succ, eighth_width last]
  have block := cap_packed_bytes_block first
  have evenBytes := cap_packed_bytes_even first
  have evenStart := ready.even
  refine ⟨by unfold slotAddress; omega, by unfold slotAddress; omega, by omega, by omega, by omega, by omega⟩

/-- The packed frontier read kernel (T238). -/
noncomputable def actualFrontier : FrontierKernel where
  after := packedFrontierAfter
  rejected := packedFrontierRejected
  run := by
    intro s node start first ready fits fuel
    by_cases last : first % 8 = 7
    · have c := eighth_case ready last fits
      obtain ⟨aligned, slotRoom, above, even, room, base⟩ := eighth_inputs ready last
      have facts := eighth_read_facts (eighthGuard (frontierHead s)) (start+capPackedBytes first) (slotAddress node)
        c.guardPC c.proof c.slot aligned slotRoom above even room
      have headHop : GroupHop s (frontierHead s) 4 := fun fuel => execute_frontier_head s ready.pc fuel
      have guardHop : GroupHop (frontierHead s) (eighthGuard (frontierHead s)) 2 :=
        fun fuel => execute_eighth_guard (frontierHead s) c.headPC fuel
      have whole := (headHop.thenDo guardHop).thenDo facts.1
      rw [after_eighth c.count, show frontierSteps first = 64 by unfold frontierSteps; rw [if_pos last]]
      exact whole fuel
    · have c := normal_case ready last fits
      have headHop : GroupHop s (frontierHead s) 4 := fun fuel => execute_frontier_head s ready.pc fuel
      have guardHop : GroupHop (frontierHead s) (normalGuard (frontierHead s)) 4 :=
        fun fuel => execute_normal_guard (frontierHead s) c.headPC fuel
      have whole := (headHop.thenDo guardHop).thenDo c.facts.hop
      rw [after_normal c.count, show frontierSteps first = 45 by unfold frontierSteps; rw [if_neg last]]
      exact whole fuel
  digest := by
    intro s node start first ready fits
    unfold capRootAt capFrontierValue
    by_cases last : first % 8 = 7
    · have c := eighth_case ready last fits
      obtain ⟨aligned, slotRoom, above, even, room, base⟩ := eighth_inputs ready last
      have facts := eighth_read_facts (eighthGuard (frontierHead s)) (start+capPackedBytes first) (slotAddress node)
        c.guardPC c.proof c.slot aligned slotRoom above even room
      rw [after_eighth c.count, last, ← base, packed_node_of_mem c.mem.symm]
      exact facts.2.2.2.2.2.1
    · have c := normal_case ready last fits
      rw [after_normal c.count]
      change readBuffer (normalTail (normalGuard (frontierHead s))) (slotAddress node) 32 = _
      rw [c.facts.digest, read_buffer_of_mem ((normal_guard_mem _).trans (head_mem s))]
      unfold packedNodeAt
      rw [if_neg last]
      have address : start+238*(first/8)+30*(first%8) = start+capPackedBytes first := by
        unfold capPackedBytes; omega
      rw [address]
  register := by
    intro s r a b c d e
    by_cases last : s.getReg .x30 = 0#64
    · rw [after_eighth last, eighth_read_register _ _ b c d e, eighth_guard_register _ _ c,
        frontier_head_register _ _ a]
    · rw [after_normal last]
      unfold normalRead
      rw [normal_tail_register _ _ b e, normal_guard_register _ _ d c, frontier_head_register _ _ a]
  pointer := by
    intro s node start first ready fits
    by_cases last : first % 8 = 7
    · have c := eighth_case ready last fits
      obtain ⟨aligned, slotRoom, above, even, room, base⟩ := eighth_inputs ready last
      have facts := eighth_read_facts (eighthGuard (frontierHead s)) (start+capPackedBytes first) (slotAddress node)
        c.guardPC c.proof c.slot aligned slotRoom above even room
      rw [after_eighth c.count]
      refine ⟨facts.2.1, ?_, ?_⟩
      · rw [facts.2.2.1, cap_packed_bytes_succ, eighth_width last]
        exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [facts.2.2.2.1, show (first+1) % 8 = 0 by omega]
    · have c := normal_case ready last fits
      rw [after_normal c.count]
      refine ⟨c.facts.pc, ?_, ?_⟩
      · change (normalTail (normalGuard (frontierHead s))).getReg .x21 = _
        rw [c.facts.proof, normal_guard_register _ _ (by decide) (by decide), frontier_head_register _ _ (by decide),
          ready.proofReg]
        exact pointer_step start first 30 (normal_width last)
      · change (normalTail (normalGuard (frontierHead s))).getReg .x30 = _
        rw [normal_tail_register _ _ (by decide) (by decide), (normal_guard_post _ c.headPC).2.1,
          frontier_head_register _ _ (by decide), ready.countdown]
        have small : first % 8 < 7 := by have := Nat.mod_lt first (by decide : 0 < 8); omega
        rw [show (first+1) % 8 = first % 8 + 1 by omega]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        change (2^64 - 1 + (7 - first % 8) % 2^64) % 2^64 = (7 - (first % 8 + 1)) % 2^64
        rw [Nat.mod_eq_of_lt (by omega : 7 - first % 8 < 2^64)]
        omega
  frame := by
    intro s node start first ready fits word bounded outside
    by_cases last : first % 8 = 7
    · have c := eighth_case ready last fits
      obtain ⟨aligned, slotRoom, above, even, room, base⟩ := eighth_inputs ready last
      have facts := eighth_read_facts (eighthGuard (frontierHead s)) (start+capPackedBytes first) (slotAddress node)
        c.guardPC c.proof c.slot aligned slotRoom above even room
      rw [after_eighth c.count, facts.2.2.2.2.2.2 word bounded (by unfold slotAddress; omega),
        memory_view_of_mem c.mem]
    · have c := normal_case ready last fits
      rw [after_normal c.count]
      change memoryView (normalTail (normalGuard (frontierHead s))) word = _
      rw [c.facts.frame word bounded (by unfold slotAddress; omega),
        memory_view_of_mem ((normal_guard_mem _).trans (head_mem s))]
  shortRun := by
    intro s node start first ready short fuel
    by_cases last : first % 8 = 7
    · have count : s.getReg .x30 = 0#64 := (countdown_zero ready).mpr last
      have headPC : (frontierHead s).pc = 0x19e0 := by
        rw [(frontier_head_post s ready.pc).1, if_pos count]
      have headHop : GroupHop s (frontierHead s) 4 := fun fuel => execute_frontier_head s ready.pc fuel
      have guardHop : GroupHop (frontierHead s) (eighthGuard (frontierHead s)) 2 :=
        fun fuel => execute_eighth_guard (frontierHead s) headPC fuel
      rw [rejected_eighth count, show frontierShortSteps first = 6 by unfold frontierShortSteps; rw [if_pos last]]
      exact (headHop.thenDo guardHop) fuel
    · have count : s.getReg .x30 ≠ 0#64 := fun zero => last ((countdown_zero ready).mp zero)
      have headPC : (frontierHead s).pc = 0x1ad0 := by
        rw [(frontier_head_post s ready.pc).1, if_neg count]
      have headHop : GroupHop s (frontierHead s) 4 := fun fuel => execute_frontier_head s ready.pc fuel
      have guardHop : GroupHop (frontierHead s) (normalGuard (frontierHead s)) 4 :=
        fun fuel => execute_normal_guard (frontierHead s) headPC fuel
      rw [rejected_normal count, show frontierShortSteps first = 8 by unfold frontierShortSteps; rw [if_neg last]]
      exact (headHop.thenDo guardHop) fuel
  shortPC := by
    intro s node start first ready short
    unfold FrontierShort at short
    by_cases last : first % 8 = 7
    · have count : s.getReg .x30 = 0#64 := (countdown_zero ready).mpr last
      have headPC : (frontierHead s).pc = 0x19e0 := by
        rw [(frontier_head_post s ready.pc).1, if_pos count]
      have hit : (frontierHead s).getReg .x22 < (frontierHead s).getReg .x21+28#64 := by
        rw [frontier_head_register _ _ (by decide), frontier_head_register _ _ (by decide), ready.proofReg]
        change s.getReg .x22 < BitVec.ofNat 64 (start+capPackedBytes first) + BitVec.ofNat 64 28
        rw [pointer_step start first 28 (eighth_width last)]
        exact short
      rw [rejected_eighth count, (eighth_guard_post _ headPC).1, if_pos hit]
    · have count : s.getReg .x30 ≠ 0#64 := fun zero => last ((countdown_zero ready).mp zero)
      have headPC : (frontierHead s).pc = 0x1ad0 := by
        rw [(frontier_head_post s ready.pc).1, if_neg count]
      have hit : (frontierHead s).getReg .x22 < (frontierHead s).getReg .x21+30#64 := by
        rw [frontier_head_register _ _ (by decide), frontier_head_register _ _ (by decide), ready.proofReg]
        change s.getReg .x22 < BitVec.ofNat 64 (start+capPackedBytes first) + BitVec.ofNat 64 30
        rw [pointer_step start first 30 (normal_width last)]
        exact short
      rw [rejected_normal count, (normal_guard_post _ headPC).1, if_pos hit]
  shortRegister := by
    intro s r a b c
    by_cases last : s.getReg .x30 = 0#64
    · rw [rejected_eighth last, eighth_guard_register _ _ b, frontier_head_register _ _ a]
    · rw [rejected_normal last, normal_guard_register _ _ c b, frontier_head_register _ _ a]
  shortMemory := by
    intro s
    by_cases last : s.getReg .x30 = 0#64
    · rw [rejected_eighth last, eighth_guard_mem, head_mem]
    · rw [rejected_normal last, normal_guard_mem, head_mem]

end TwoPermutationPrototype.Packed.Checker
