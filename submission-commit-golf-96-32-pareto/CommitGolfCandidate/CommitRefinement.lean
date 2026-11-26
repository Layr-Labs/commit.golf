import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.Model

/-! Memory refinement of the 17-instruction in-place leaf lane and 32-leaf unrolled block
to the reference position-tagged 128-bit salted leaf digest. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Commitment's final root copy matches opening's four-word digest copy. -/
theorem commit_root_copy_as_opening (state : MachineState) :
    (commitRootCopyState state).mem =
      (openingCopyState ((state.setReg .x23 (state.getReg .x9 + 32)).setReg .x25
        (state.getReg .x26))).mem := by
  rw [commit_root_copy_expansion, opening_copy_expansion]
  simp (config := { decide := true }) [List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC,
    MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

theorem commit_root_copy_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x9 + 32 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x26 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source + 32 ≤ 2^64) (destinationBound : destination + 32 ≤ 2^64)
    (separate : source + 32 ≤ destination ∨ destination + 32 ≤ source) :
    readBuffer (commitRootCopyState state) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_root_copy_as_opening state)]
  rw [opening_copy_digest _ source destination
    (by rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]; exact sourcePointer)
    (by rw [MachineState.getReg_setReg_eq (by decide)]; exact destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate]
  rfl

theorem commit_root_copy_preserves_digest (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x26 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (readBound : address + 32 ≤ 2^64)
    (separate : address + 32 ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (commitRootCopyState state) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_root_copy_as_opening state)]
  rw [opening_copy_preserves_digest _ destination address
    (by rw [MachineState.getReg_setReg_eq (by decide)]; exact destinationPointer)
    aligned destinationBound readBound separate]
  rfl

theorem commit_root_copy_preserves_salt (state : MachineState) (destination address : Nat)
    (destinationPointer : state.getReg .x26 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (readBound : address + 16 ≤ 2^64)
    (separate : address + 16 ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (commitRootCopyState state) address 16 = readBuffer state address 16 := by
  rw [read_buffer_memory_congr _ _ (commit_root_copy_as_opening state)]
  apply read_salt_congr _ _ _ aligned
  intro i hi
  apply opening_copy_memory_outside
  intro j
  rw [MachineState.getReg_setReg_eq (by decide), destinationPointer, ← BitVec.ofNat_add]
  intro eq
  have h := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address + 8 * i < 2^64),
    Nat.mod_eq_of_lt (by have := j.isLt; omega : destination + 8 * j.val < 2^64)] at h
  have := j.isLt
  rcases separate with before | after <;> omega

/-! ### Memory effect of `leafPrepState` (16B salt + 8B tag) -/

private theorem mem_getReg' (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem commit_getMem_setMem (s : MachineState) (a v q : Word) :
    (s.setMem a v).getMem q = if q = a then v else s.getMem q := by
  by_cases h : q = a
  · subst h; simp [MachineState.getMem_setMem_eq]
  · simp only [if_neg h]
    first | exact MachineState.getMem_setMem_ne h | exact MachineState.getMem_setMem_ne h.symm

/-- Exact memory after the 6-instruction prep: three aligned word writes at `x10`, `x10+8`, `x10+16`. -/
theorem leaf_prep_getMem (state : MachineState) (j : Nat) (hj : j < 32)
    (slot saltBase : Nat)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (slotBound : slot + 24 ≤ 2^64) (saltBound : saltBase + 16 * j + 16 ≤ 2^64)
    (disjoint : saltBase + 16 * j + 16 ≤ slot ∨ slot + 24 ≤ saltBase + 16 * j)
    (addr : Word) :
    (leafPrepState state j).getMem addr =
      if addr = BitVec.ofNat 64 (slot + 16) then BitVec.ofNat 64 slot
      else if addr = BitVec.ofNat 64 (slot + 8) then state.getMem (BitVec.ofNat 64 (saltBase + 16 * j + 8))
      else if addr = BitVec.ofNat 64 slot then state.getMem (BitVec.ofNat 64 (saltBase + 16 * j))
      else state.getMem addr := by
  have s0 := signExtend12_salt0 ⟨j, hj⟩
  have s1 := signExtend12_salt1 ⟨j, hj⟩
  have neqSalt1Slot0 : BitVec.ofNat 64 (saltBase + 16 * j + 8) ≠ BitVec.ofNat 64 slot := by
    intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : saltBase + 16 * j + 8 < 2^64),
      Nat.mod_eq_of_lt (by omega : slot < 2^64)] at hn
    rcases disjoint with h1 | h2 <;> omega
  have hse0 : signExtend12 (0 : BitVec 12) = 0#64 := rfl
  have hse8 : signExtend12 (8 : BitVec 12) = 8#64 := rfl
  have hse16 : signExtend12 (16 : BitVec 12) = 16#64 := rfl
  have hadd0 (x : Word) : x + 0#64 = x := BitVec.add_zero x
  have h1 : BitVec.ofNat 64 saltBase + BitVec.ofNat 64 (16 * j) = BitVec.ofNat 64 (saltBase + 16 * j) := by
    rw [← BitVec.ofNat_add]
  have h2 : BitVec.ofNat 64 saltBase + BitVec.ofNat 64 (16 * j + 8) = BitVec.ofNat 64 (saltBase + 16 * j + 8) := by
    rw [← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have h3 : BitVec.ofNat 64 slot + 8#64 = BitVec.ofNat 64 (slot + 8) := by
    change BitVec.ofNat 64 slot + BitVec.ofNat 64 8 = _; rw [← BitVec.ofNat_add]
  have h4 : BitVec.ofNat 64 slot + 16#64 = BitVec.ofNat 64 (slot + 16) := by
    change BitVec.ofNat 64 slot + BitVec.ofNat 64 16 = _; rw [← BitVec.ofNat_add]
  dsimp only [leafPrepState, leafPrepPrefix, leafPrepInstrs, List.take, List.foldl, execInstrBr]
  simp only [MachineState.getMem_setPC, MachineState.getMem_setReg, MachineState.getReg_setPC,
    mem_getReg', hse0, hse8, hse16,
    MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x18),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    slotPtr, saltPtr, s0, s1, h1, h2, h3, h4, hadd0]
  simp only [commit_getMem_setMem, MachineState.getMem_setPC, MachineState.getMem_setReg,
    neqSalt1Slot0, ↓reduceIte]

theorem leaf_prep_salt_tag (state : MachineState) (j : Nat) (hj : j < 32)
    (slot saltBase : Nat)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (slotAligned : slot % 8 = 0) (saltAligned : saltBase % 8 = 0)
    (slotBound : slot + 24 ≤ 2^64) (saltBound : saltBase + 16 * j + 16 ≤ 2^64)
    (disjoint : saltBase + 16 * j + 16 ≤ slot ∨ slot + 24 ≤ saltBase + 16 * j) :
    readBuffer (leafPrepState state j) slot 16 = readBuffer state (saltBase + 16 * j) 16 ∧
    readBuffer (leafPrepState state j) (slot + 16) 8 = BitVec.ofNat 64 slot := by
  have gm := leaf_prep_getMem state j hj slot saltBase slotPtr saltPtr slotBound saltBound disjoint
  have ne01 : BitVec.ofNat 64 slot ≠ BitVec.ofNat 64 (slot + 8) := by
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : slot < 2^64),
      Nat.mod_eq_of_lt (by omega : slot + 8 < 2^64)] at this; omega
  have ne02 : BitVec.ofNat 64 slot ≠ BitVec.ofNat 64 (slot + 16) := by
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : slot < 2^64),
      Nat.mod_eq_of_lt (by omega : slot + 16 < 2^64)] at this; omega
  have ne12 : BitVec.ofNat 64 (slot + 8) ≠ BitVec.ofNat 64 (slot + 16) := by
    intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : slot + 8 < 2^64),
      Nat.mod_eq_of_lt (by omega : slot + 16 < 2^64)] at this; omega
  constructor
  · rw [read_salt_words _ _ slotAligned, read_salt_words _ _ (by omega), gm, gm]
    simp only [ne01, ne02, ne12, ↓reduceIte, Nat.add_assoc]
  · rw [read_word_eq _ _ (by omega), gm, if_pos rfl]

/-- `leafPrepState` preserves any aligned byte range disjoint from `[slot, slot + 24)`. -/
theorem leaf_prep_outside (state : MachineState) (j : Nat) (hj : j < 32)
    (slot saltBase : Nat)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (slotAligned : slot % 8 = 0)
    (slotBound : slot + 24 ≤ 2^64) (saltBound : saltBase + 16 * j + 16 ≤ 2^64)
    (disjoint : saltBase + 16 * j + 16 ≤ slot ∨ slot + 24 ≤ saltBase + 16 * j)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ slot ∨ slot + 24 ≤ address) :
    readBuffer (leafPrepState state j) address count = readBuffer state address count := by
  have gm := leaf_prep_getMem state j hj slot saltBase slotPtr saltPtr slotBound saltBound disjoint
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hbyte : (leafPrepState state j).getByte (BitVec.ofNat 64 (address + i)) =
      state.getByte (BitVec.ofNat 64 (address + i)) := by
    have hsplit : address + i = 8 * ((address + i) / 8) + (address + i) % 8 := by omega
    rw [hsplit, aligned_byte (leafPrepState state j) ((address + i) / 8) ((address + i) % 8) (by omega),
      aligned_byte state ((address + i) / 8) ((address + i) % 8) (by omega)]
    congr 1
    have hdiv : ((address + i) % 8) / 8 = 0 := Nat.div_eq_of_lt (Nat.mod_lt _ (by decide))
    rw [hdiv, Nat.mul_zero, Nat.add_zero, gm]
    have neq (off : Nat) (ho : off = 0 ∨ off = 8 ∨ off = 16) :
        BitVec.ofNat 64 (8 * ((address + i) / 8)) ≠ BitVec.ofNat 64 (slot + off) := by
      intro eq
      have hn := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * ((address + i) / 8) < 2^64),
        Nat.mod_eq_of_lt (by rcases ho with rfl | rfl | rfl <;> omega : slot + off < 2^64)] at hn
      rcases separate with before | after <;> rcases ho with rfl | rfl | rfl <;> omega
    rw [if_neg (neq 16 (Or.inr (Or.inr rfl))), if_neg (neq 8 (Or.inr (Or.inl rfl))),
      if_neg (by simpa using neq 0 (Or.inl rfl))]
  rw [hbyte]

/-! ### Fixed-oracle evaluation of one lane and one 32-leaf block -/

def leafLaneEval (oracle : Oracle) (state : MachineState) (j : Nat) : MachineState :=
  let p0 := leafPrepState state j
  let a0 := oracle.compression (readBuffer p0 (state.getReg .x10).toNat 96)
  let s1 := leafCall0State state j a0
  let a1 := oracle.compression (readBuffer s1 (state.getReg .x10 + 56).toNat 96)
  let s2 := leafCall1State s1 a1
  let a2 := oracle.compression (readBuffer s2 (s1.getReg .x10 + 120).toNat 96)
  let s3 := leafCall2State s2 a2
  let a3 := oracle.compression (readBuffer s3 (s2.getReg .x10 + 128).toNat 96)
  leafAdvanceState (leafCall3State s3 j a3)

theorem leaf_lane_evaluation (oracle : Oracle) (state : MachineState) (j : Nat) :
    checkEvaluation oracle (leafLaneRun state j) = (leafLaneEval oracle state j, 4) := by
  simp only [leafLaneRun, leafLaneEval, bind_assoc, pure_bind, check_evaluation_public_bind,
    check_evaluation_pure]
  rfl

theorem leaf_lane_eval_support (oracle : Oracle) (state : MachineState) (j : Nat) :
    leafLaneEval oracle state j ∈ support (leafLaneRun state j) := by
  have h := check_evaluation_support oracle (leafLaneRun state j)
  rwa [leaf_lane_evaluation] at h

theorem leaf_lane_eval_registers (oracle : Oracle) (state : MachineState) (j : Nat) :
    (leafLaneEval oracle state j).getReg .x10 = state.getReg .x10 + 256 ∧
    (leafLaneEval oracle state j).pc = state.pc + 68 ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 →
      (leafLaneEval oracle state j).getReg reg = state.getReg reg :=
  leaf_lane_registers state _ j (leaf_lane_eval_support oracle state j)

private theorem leaf_advance_mem (s : MachineState) : (leafAdvanceState s).mem = s.mem := rfl
private theorem leaf_call3_mem (s : MachineState) (j : Nat) (a3 : BitVec 256) :
    (leafCall3State s j a3).mem = (writeBits s (s.getReg .x23 + BitVec.ofNat 64 (heapOffset j)) a3).mem :=
  write_bits_memory_congr _ _ _ a3 rfl
private theorem leaf_call2_mem (s : MachineState) (a2 : BitVec 256) :
    (leafCall2State s a2).mem = (writeBits s (s.getReg .x10 + 128) a2).mem :=
  write_bits_memory_congr _ _ _ a2 rfl
private theorem leaf_call1_mem (s : MachineState) (a1 : BitVec 256) :
    (leafCall1State s a1).mem = (writeBits s (s.getReg .x10 + 120) a1).mem :=
  write_bits_memory_congr _ _ _ a1 rfl
private theorem leaf_call0_mem (s : MachineState) (j : Nat) (a0 : BitVec 256) :
    (leafCall0State s j a0).mem = (writeBits (leafPrepState s j) (s.getReg .x10 + 56) a0).mem := rfl
private theorem commit_block_next_mem (s : MachineState) : (commitBlockNextState s).mem = s.mem := rfl

/-- One 17-instruction lane preserves every byte range disjoint from `[slot, slot + 216)`
and `[heap + heapOffset j, heap + heapOffset j + 32)`. -/
theorem leaf_lane_eval_outside (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 32)
    (slot saltBase heap : Nat)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0)
    (slotBound : slot + 280 ≤ MEMORY_BYTES)
    (saltBound : saltBase + 16 * j + 16 ≤ MEMORY_BYTES)
    (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (saltDisjoint : saltBase + 16 * j + 16 ≤ slot ∨ slot + 24 ≤ saltBase + 16 * j)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outsideSlot : address + count ≤ slot ∨ slot + 216 ≤ address)
    (outsideHeap : address + count ≤ heap + heapOffset j ∨ heap + heapOffset j + 32 ≤ address) :
    readBuffer (leafLaneEval oracle state j) address count = readBuffer state address count := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have hOff : heapOffset j + 32 ≤ 1536 := by
    have := heap_offset_bound j 16 (by omega); omega
  let p0 := leafPrepState state j
  let a0 : BitVec 256 := oracle.compression (readBuffer p0 (state.getReg .x10).toNat 96)
  let s1 := leafCall0State state j a0
  let a1 : BitVec 256 := oracle.compression (readBuffer s1 (state.getReg .x10 + 56).toNat 96)
  let s2 := leafCall1State s1 a1
  let a2 : BitVec 256 := oracle.compression (readBuffer s2 (s1.getReg .x10 + 120).toNat 96)
  let s3 := leafCall2State s2 a2
  let a3 : BitVec 256 := oracle.compression (readBuffer s3 (s2.getReg .x10 + 128).toNat 96)
  have heval : leafLaneEval oracle state j = leafAdvanceState (leafCall3State s3 j a3) := rfl
  have s1r10 : s1.getReg .x10 = BitVec.ofNat 64 slot := by
    dsimp only [s1]
    rw [leafCall0State, writeBits_register, leafPrepState,
      leaf_prep_prefix_reg state j 6 (by decide) .x10 (by decide) (by decide), slotPtr]
  have s2r10 : s2.getReg .x10 = BitVec.ofNat 64 (slot + 56) := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide),
      s1r10, bitvec64_ofNat_add_lit]
  have s3r23 : s3.getReg .x23 = BitVec.ofNat 64 heap := by
    dsimp only [s3, s2, s1]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      leafCall0State, writeBits_register, leafPrepState,
      leaf_prep_prefix_reg state j 6 (by decide) .x23 (by decide) (by decide), heapPtr]
  rw [heval, read_buffer_memory_congr _ _ (leaf_advance_mem _),
    read_buffer_memory_congr _ _ (leaf_call3_mem s3 j a3),
    s3r23, ← BitVec.ofNat_add,
    write_bits_read_outside _ _ (heap + heapOffset j) address count (by omega) readBound outsideHeap]
  dsimp only [s3]
  rw [read_buffer_memory_congr _ _ (leaf_call2_mem s2 a2),
    s2r10, bitvec64_ofNat_add_lit, show slot + 56 + 128 = slot + 184 by omega,
    write_bits_read_outside _ _ (slot + 184) address count (by omega) readBound
      (by rcases outsideSlot with h | h <;> omega)]
  dsimp only [s2]
  rw [read_buffer_memory_congr _ _ (leaf_call1_mem s1 a1),
    s1r10, bitvec64_ofNat_add_lit,
    write_bits_read_outside _ _ (slot + 120) address count (by omega) readBound
      (by rcases outsideSlot with h | h <;> omega)]
  dsimp only [s1]
  rw [read_buffer_memory_congr _ _ (leaf_call0_mem state j a0),
    slotPtr, bitvec64_ofNat_add_lit,
    write_bits_read_outside _ _ (slot + 56) address count (by omega) readBound
      (by rcases outsideSlot with h | h <;> omega)]
  exact leaf_prep_outside state j hj slot saltBase slotPtr saltPtr slotAligned
    (by omega) (by omega) saltDisjoint address count readBound
    (by rcases outsideSlot with h | h <;> omega)

theorem leaf_digest_unfold (compress : Compression) (index : Index) (salt : Salt) (value : Entry) :
    leafDigest compress index salt value =
      absorb compress (absorb compress (absorb compress
        (compress (leafInitInput index salt value))
        (value.extractLsb' 512 512))
        (value.extractLsb' 1024 512))
        (value.extractLsb' 1536 512) := rfl

/-- One 17-instruction lane writes `leafDigest oracle.compression index salt value` at
`heap + heapOffset j` when `slot = 4072 + 256 * index.val`. -/
theorem leaf_lane_eval_digest (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 32)
    (index : Index) (saltBase heap : Nat) (value : Entry)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 (4072 + 256 * index.val))
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltAligned : saltBase % 8 = 0)
    (saltBound : saltBase + 16 * j + 16 ≤ MEMORY_BYTES)
    (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (saltDisjoint : 4072 + 256 * index.val + 24 ≤ saltBase + 16 * j)
    (headData : readBuffer state (4096 + 256 * index.val) 72 = value.extractLsb' 0 576)
    (block1Data : readBuffer state (4096 + 256 * index.val + 64) 64 = value.extractLsb' 512 512)
    (block2Data : readBuffer state (4096 + 256 * index.val + 128) 64 = value.extractLsb' 1024 512)
    (block3Data : readBuffer state (4096 + 256 * index.val + 192) 64 = value.extractLsb' 1536 512) :
    readBuffer (leafLaneEval oracle state j) (heap + heapOffset j) 32 =
      leafDigest oracle.compression index (readBuffer state (saltBase + 16 * j) 16) value := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have hi : index.val < 2^24 := index.isLt
  let slot := 4072 + 256 * index.val
  have hslotAl : slot % 8 = 0 := by omega
  have hslotB : slot + 280 ≤ MEMORY_BYTES := by omega
  have hOff : heapOffset j + 32 ≤ 1536 := by have := heap_offset_bound j 16 (by omega); omega
  unfold leafLaneEval
  dsimp only
  rw [read_buffer_memory_congr _ _ (leaf_advance_mem _)]
  -- Call 0 input
  have prep := leaf_prep_salt_tag state j hj slot saltBase slotPtr saltPtr hslotAl saltAligned
    (by omega) (by omega) (Or.inr saltDisjoint)
  have prepHead : readBuffer (leafPrepState state j) (slot + 24) 72 = value.extractLsb' 0 576 := by
    rw [leaf_prep_outside state j hj slot saltBase slotPtr saltPtr hslotAl
      (by omega) (by omega) (Or.inr saltDisjoint) (slot + 24) 72 (by omega) (Or.inr (by omega))]
    simpa [slot, show 4072 + 256 * index.val + 24 = 4096 + 256 * index.val by omega] using headData
  have slotNat : (state.getReg .x10).toNat = slot := by
    rw [slotPtr]; exact word_small_toNat slot (by omega)
  have q0eq : readBuffer (leafPrepState state j) (state.getReg .x10).toNat 96 =
      leafInitInput index (readBuffer state (saltBase + 16 * j) 16) value := by
    rw [slotNat, read_init_query, prep.1, prep.2, prepHead]
    rfl
  let d0 : BitVec 256 := oracle.compression (leafInitInput index (readBuffer state (saltBase + 16 * j) 16) value)
  have ha0 : oracle.compression (readBuffer (leafPrepState state j) (state.getReg .x10).toNat 96) = d0 :=
    congrArg oracle.compression q0eq
  rw [ha0]
  -- After Call 0 (s1): d0 at slot + 56, block1 at slot + 88 unchanged
  let s1 := leafCall0State state j d0
  have hs1 : leafCall0State state j d0 = s1 := rfl
  rw [hs1]
  have s1r10 : s1.getReg .x10 = BitVec.ofNat 64 slot := by
    dsimp only [s1]
    rw [leafCall0State, writeBits_register, leafPrepState,
      leaf_prep_prefix_reg state j 6 (by decide) .x10 (by decide) (by decide), slotPtr]
  have s1_d0 : readBuffer s1 (slot + 56) 32 = d0 := by
    dsimp only [s1]
    rw [read_buffer_memory_congr _ _ (leaf_call0_mem state j d0), slotPtr, bitvec64_ofNat_add_lit]
    simpa using write_bits_digest (leafPrepState state j) (slot + 56) 0 d0 (by decide) (by decide)
  have s1_outside (addr cnt : Nat) (rb : addr + cnt ≤ 2^64) (sep : slot + 88 ≤ addr) :
      readBuffer s1 addr cnt = readBuffer state addr cnt := by
    dsimp only [s1]
    rw [read_buffer_memory_congr _ _ (leaf_call0_mem state j d0), slotPtr, bitvec64_ofNat_add_lit,
      write_bits_read_outside _ _ (slot + 56) addr cnt (by omega) rb (Or.inr (by omega))]
    exact leaf_prep_outside state j hj slot saltBase slotPtr saltPtr hslotAl
      (by omega) (by omega) (Or.inr saltDisjoint) addr cnt rb (Or.inr (by omega))
  have off56 : (state.getReg .x10 + 56).toNat = slot + 56 := by
    rw [slotPtr]; exact pointer_offset_nat slot 56 (by omega)
  have q1eq : readBuffer s1 (state.getReg .x10 + 56).toNat 96 =
      leafInput d0 (value.extractLsb' 512 512) := by
    rw [off56, read_leaf_query, s1_d0, show slot + 56 + 32 = slot + 88 by omega,
      s1_outside (slot + 88) 64 (by omega) (by omega),
      show slot + 88 = 4096 + 256 * index.val + 64 by dsimp only [slot]; omega, block1Data]
    rfl
  let d1 : BitVec 256 := absorb oracle.compression d0 (value.extractLsb' 512 512)
  have ha1 : oracle.compression (readBuffer s1 (state.getReg .x10 + 56).toNat 96) = d1 :=
    congrArg oracle.compression q1eq
  rw [ha1]
  -- After Call 1 (s2): d1 at slot + 120, block2 at slot + 152 unchanged
  let s2 := leafCall1State s1 d1
  have hs2 : leafCall1State s1 d1 = s2 := rfl
  rw [hs2]
  have s2r10 : s2.getReg .x10 = BitVec.ofNat 64 (slot + 56) := by
    dsimp only [s2]
    rw [leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide),
      s1r10, bitvec64_ofNat_add_lit]
  have s2_d1 : readBuffer s2 (slot + 120) 32 = d1 := by
    dsimp only [s2]
    rw [read_buffer_memory_congr _ _ (leaf_call1_mem s1 d1), s1r10, bitvec64_ofNat_add_lit]
    simpa using write_bits_digest s1 (slot + 120) 0 d1 (by decide) (by decide)
  have s2_outside (addr cnt : Nat) (rb : addr + cnt ≤ 2^64) (sep : slot + 152 ≤ addr) :
      readBuffer s2 addr cnt = readBuffer state addr cnt := by
    dsimp only [s2]
    rw [read_buffer_memory_congr _ _ (leaf_call1_mem s1 d1), s1r10, bitvec64_ofNat_add_lit,
      write_bits_read_outside _ _ (slot + 120) addr cnt (by omega) rb (Or.inr (by omega))]
    exact s1_outside addr cnt rb (by omega)
  have off120 : (s1.getReg .x10 + 120).toNat = slot + 120 := by
    rw [s1r10]; exact pointer_offset_nat slot 120 (by omega)
  have q2eq : readBuffer s2 (s1.getReg .x10 + 120).toNat 96 =
      leafInput d1 (value.extractLsb' 1024 512) := by
    rw [off120, read_leaf_query, s2_d1, show slot + 120 + 32 = slot + 152 by omega,
      s2_outside (slot + 152) 64 (by omega) (by omega),
      show slot + 152 = 4096 + 256 * index.val + 128 by dsimp only [slot]; omega, block2Data]
    rfl
  let d2 : BitVec 256 := absorb oracle.compression d1 (value.extractLsb' 1024 512)
  have ha2 : oracle.compression (readBuffer s2 (s1.getReg .x10 + 120).toNat 96) = d2 :=
    congrArg oracle.compression q2eq
  rw [ha2]
  -- After Call 2 (s3): d2 at slot + 184, block3 at slot + 216 unchanged
  let s3 := leafCall2State s2 d2
  have hs3 : leafCall2State s2 d2 = s3 := rfl
  rw [hs3]
  have s3r23 : s3.getReg .x23 = BitVec.ofNat 64 heap := by
    dsimp only [s3, s2, s1]
    rw [leafCall2State, writeBits_register, leafCall2Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      leafCall1State, writeBits_register, leafCall1Setup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_ne _ _ _ _ (by decide),
      leafCall0State, writeBits_register, leafPrepState,
      leaf_prep_prefix_reg state j 6 (by decide) .x23 (by decide) (by decide), heapPtr]
  have s3_d2 : readBuffer s3 (slot + 184) 32 = d2 := by
    dsimp only [s3]
    rw [read_buffer_memory_congr _ _ (leaf_call2_mem s2 d2),
      s2r10, bitvec64_ofNat_add_lit, show slot + 56 + 128 = slot + 184 by omega]
    simpa using write_bits_digest s2 (slot + 184) 0 d2 (by decide) (by decide)
  have s3_outside (addr cnt : Nat) (rb : addr + cnt ≤ 2^64) (sep : slot + 216 ≤ addr) :
      readBuffer s3 addr cnt = readBuffer state addr cnt := by
    dsimp only [s3]
    rw [read_buffer_memory_congr _ _ (leaf_call2_mem s2 d2),
      s2r10, bitvec64_ofNat_add_lit, show slot + 56 + 128 = slot + 184 by omega,
      write_bits_read_outside _ _ (slot + 184) addr cnt (by omega) rb (Or.inr (by omega))]
    exact s2_outside addr cnt rb (by omega)
  have off184 : (s2.getReg .x10 + 128).toNat = slot + 184 := by
    rw [s2r10]
    have h := pointer_offset_nat (slot + 56) 128 (by omega)
    change (BitVec.ofNat 64 (slot + 56) + BitVec.ofNat 64 128).toNat = _
    rw [h]
  have q3eq : readBuffer s3 (s2.getReg .x10 + 128).toNat 96 =
      leafInput d2 (value.extractLsb' 1536 512) := by
    rw [off184, read_leaf_query, s3_d2, show slot + 184 + 32 = slot + 216 by omega,
      s3_outside (slot + 216) 64 (by omega) (by omega),
      show slot + 216 = 4096 + 256 * index.val + 192 by dsimp only [slot]; omega, block3Data]
    rfl
  let d3 : BitVec 256 := absorb oracle.compression d2 (value.extractLsb' 1536 512)
  have ha3 : oracle.compression (readBuffer s3 (s2.getReg .x10 + 128).toNat 96) = d3 :=
    congrArg oracle.compression q3eq
  rw [ha3, read_buffer_memory_congr _ _ (leaf_call3_mem s3 j d3), s3r23, ← BitVec.ofNat_add]
  simpa [d3, d2, d1, d0, leaf_digest_unfold] using
    write_bits_digest s3 (heap + heapOffset j) 0 d3 (by decide) (by decide)

/-! ### Full 32-leaf block refinement -/

theorem leaf_block_lanes_eval_succ (oracle : Oracle) (state : MachineState) (start count : Nat) :
    checkEvaluation oracle (leafBlockLanes state start (count + 1)) =
      let rest := checkEvaluation oracle (leafBlockLanes (leafLaneEval oracle state start) (start + 1) count)
      (rest.1, 4 + rest.2) := by
  rw [leafBlockLanes, check_evaluation_bind, leaf_lane_evaluation]

theorem commit_block_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (commitBlockRun state)).1 =
      commitBlockNextState (checkEvaluation oracle (leafBlockLanes state 0 32)).1 := by
  rw [commitBlockRun, check_evaluation_bind]
  simp only [check_evaluation_pure]

/-- Layout hypotheses for one 32-leaf block. -/
structure BlockLayout (state : MachineState) (slot saltBase heap : Nat) : Prop where
  slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot
  saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase
  heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap
  slotAligned : slot % 8 = 0
  saltAligned : saltBase % 8 = 0
  heapAligned : heap % 8 = 0
  heapAfter : slot + 24 + 8192 ≤ heap
  saltsAfter : heap + 1536 ≤ saltBase
  saltBound : saltBase + 512 ≤ MEMORY_BYTES

/-- `count` consecutive lanes starting at `start` preserve any byte range outside
`[slot, slot + 256 * count)` and outside all written heap slots `[heap + heapOffset j, +32)`. -/
theorem leaf_block_lanes_outside (oracle : Oracle) (state : MachineState)
    (start count slot saltBase heap : Nat) (bounded : start + count ≤ 32)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 slot)
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0)
    (heapAfter : slot + 24 + 256 * count ≤ heap)
    (saltsAfter : heap + 1536 ≤ saltBase)
    (saltBound : saltBase + 512 ≤ MEMORY_BYTES)
    (address bytes : Nat) (readBound : address + bytes ≤ 2^64)
    (outsideSlot : address + bytes ≤ slot ∨ slot + 256 * count ≤ address)
    (outsideHeap : ∀ j, start ≤ j → j < start + count →
      address + bytes ≤ heap + heapOffset j ∨ heap + heapOffset j + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (leafBlockLanes state start count)).1 address bytes =
      readBuffer state address bytes := by
  induction count generalizing state start slot with
  | zero => rw [leafBlockLanes, check_evaluation_pure]
  | succ count ih =>
    have regs := leaf_lane_eval_registers oracle state start
    have nextSlot : (leafLaneEval oracle state start).getReg .x10 = BitVec.ofNat 64 (slot + 256) := by
      rw [regs.1, slotPtr, bitvec64_ofNat_add_lit]
    have nextSalt : (leafLaneEval oracle state start).getReg .x18 = BitVec.ofNat 64 saltBase :=
      (regs.2.2 .x18 (by decide) (by decide) (by decide)).trans saltPtr
    have nextHeap : (leafLaneEval oracle state start).getReg .x23 = BitVec.ofNat 64 heap :=
      (regs.2.2 .x23 (by decide) (by decide) (by decide)).trans heapPtr
    rw [leaf_block_lanes_eval_succ]
    dsimp only
    rw [ih _ (start + 1) (slot + 256) (by omega) nextSlot nextSalt nextHeap (by omega)
      (by omega) (by rcases outsideSlot with h | h <;> omega)
      (fun j hlo hhi => outsideHeap j (by omega) (by omega))]
    exact leaf_lane_eval_outside oracle state start (by omega) slot saltBase heap
      slotPtr saltPtr heapPtr slotAligned (by omega) (by omega) (by omega)
      (Or.inr (by omega)) address bytes readBound
      (by rcases outsideSlot with h | h <;> omega)
      (outsideHeap start (by omega) (by omega))

/-- One 32-leaf block preserves every byte range outside `[slot, slot + 8192)` and
outside all 32 written heap slots (hence preserves all pair gaps `[heap+96p+64, +32)`,
all salts, and all subsequent message blocks). -/
theorem commit_block_preserves (oracle : Oracle) (state : MachineState)
    (slot saltBase heap address bytes : Nat) (layout : BlockLayout state slot saltBase heap)
    (readBound : address + bytes ≤ 2^64)
    (outsideSlot : address + bytes ≤ slot ∨ slot + 8192 ≤ address)
    (outsideHeap : ∀ j < 32,
      address + bytes ≤ heap + heapOffset j ∨ heap + heapOffset j + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitBlockRun state)).1 address bytes =
      readBuffer state address bytes := by
  rw [commit_block_evaluation, read_buffer_memory_congr _ _ (commit_block_next_mem _)]
  exact leaf_block_lanes_outside oracle state 0 32 slot saltBase heap (by decide)
    layout.slotPtr layout.saltPtr layout.heapPtr layout.slotAligned
    layout.heapAfter layout.saltsAfter layout.saltBound
    address bytes readBound outsideSlot (fun j _ hj => outsideHeap j hj)

/-- `count` consecutive lanes starting at `start` write each leaf's reference digest into
`heap + heapOffset j`. -/
theorem leaf_block_lanes_digests (oracle : Oracle) (state : MachineState)
    (start count baseIdx saltBase heap : Nat) (bounded : start + count ≤ 32)
    (idxBound : baseIdx + count ≤ LENGTH)
    (message : Nat → Entry)
    (slotPtr : state.getReg .x10 = BitVec.ofNat 64 (4072 + 256 * baseIdx))
    (saltPtr : state.getReg .x18 = BitVec.ofNat 64 saltBase)
    (heapPtr : state.getReg .x23 = BitVec.ofNat 64 heap)
    (saltAligned : saltBase % 8 = 0)
    (heapAfter : 4072 + 256 * baseIdx + 24 + 256 * count ≤ heap)
    (saltsAfter : heap + 1536 ≤ saltBase)
    (saltBound : saltBase + 512 ≤ MEMORY_BYTES)
    (headData : ∀ k < count,
      readBuffer state (4096 + 256 * (baseIdx + k)) 72 = (message k).extractLsb' 0 576)
    (blockData : ∀ k < count, ∀ b, 1 ≤ b → b < 4 →
      readBuffer state (4096 + 256 * (baseIdx + k) + 64 * b) 64 = (message k).extractLsb' (512 * b) 512) :
    ∀ k (hk : k < count),
      readBuffer (checkEvaluation oracle (leafBlockLanes state start count)).1
        (heap + heapOffset (start + k)) 32 =
        leafDigest oracle.compression ⟨baseIdx + k, by omega⟩
          (readBuffer state (saltBase + 16 * (start + k)) 16) (message k) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction count generalizing state start baseIdx message with
  | zero => intro k hk; omega
  | succ count ih =>
    let idx0 : Index := ⟨baseIdx, by omega⟩
    have regs := leaf_lane_eval_registers oracle state start
    have nextSlot : (leafLaneEval oracle state start).getReg .x10 =
        BitVec.ofNat 64 (4072 + 256 * (baseIdx + 1)) := by
      rw [regs.1, slotPtr]
      exact ofNat64_add_eq _ 256 _ (by clear * -; omega)
    have nextSalt : (leafLaneEval oracle state start).getReg .x18 = BitVec.ofNat 64 saltBase :=
      (regs.2.2 .x18 (by decide) (by decide) (by decide)).trans saltPtr
    have nextHeap : (leafLaneEval oracle state start).getReg .x23 = BitVec.ofNat 64 heap :=
      (regs.2.2 .x23 (by decide) (by decide) (by decide)).trans heapPtr
    have lane0 := leaf_lane_eval_digest oracle state start (by omega) idx0 saltBase heap (message 0)
      slotPtr saltPtr heapPtr saltAligned (by omega) (by omega) (by dsimp only [idx0]; omega)
      (by simpa [idx0] using headData 0 (by omega))
      (by simpa [idx0] using blockData 0 (by omega) 1 (by decide) (by decide))
      (by simpa [idx0] using blockData 0 (by omega) 2 (by decide) (by decide))
      (by simpa [idx0] using blockData 0 (by omega) 3 (by decide) (by decide))
    have nextHead (k : Nat) (hk : k < count) :
        readBuffer (leafLaneEval oracle state start) (4096 + 256 * (baseIdx + 1 + k)) 72 =
          (message (k + 1)).extractLsb' 0 576 := by
      rw [leaf_lane_eval_outside oracle state start (by omega) (4072 + 256 * baseIdx) saltBase heap
        slotPtr saltPtr heapPtr (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) _ 72 (by omega) (Or.inr (by omega))
        (Or.inl (by have := heap_offset_bound start 16 (by omega); omega))]
      convert headData (k + 1) (by omega) using 2; omega
    have nextBlock (k : Nat) (hk : k < count) (b : Nat) (hb1 : 1 ≤ b) (hb4 : b < 4) :
        readBuffer (leafLaneEval oracle state start) (4096 + 256 * (baseIdx + 1 + k) + 64 * b) 64 =
          (message (k + 1)).extractLsb' (512 * b) 512 := by
      rw [leaf_lane_eval_outside oracle state start (by omega) (4072 + 256 * baseIdx) saltBase heap
        slotPtr saltPtr heapPtr (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) _ 64 (by omega) (Or.inr (by omega))
        (Or.inl (by have := heap_offset_bound start 16 (by omega); omega))]
      convert blockData (k + 1) (by omega) b hb1 hb4 using 2; omega
    intro k hk
    rw [leaf_block_lanes_eval_succ]
    dsimp only
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      have hOffS := heap_offset_bound start 16 (by omega)
      rw [leaf_block_lanes_outside oracle _ (start + 1) count (4072 + 256 * (baseIdx + 1)) saltBase heap
        (by omega) nextSlot nextSalt nextHeap (by omega) (by omega) saltsAfter saltBound
        (heap + heapOffset start) 32 (by omega) (Or.inr (by omega))
        (fun j hlo _ => by
          have := heap_offset_disjoint start j (by omega)
          rcases this with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
      exact lane0
    | succ k =>
      have hrec := ih (leafLaneEval oracle state start) (start + 1) (baseIdx + 1)
        (by omega) (by omega) (fun i => message (i + 1))
        nextSlot nextSalt nextHeap (by omega) nextHead nextBlock k (by omega)
      have saltPres : readBuffer (leafLaneEval oracle state start) (saltBase + 16 * (start + 1 + k)) 16 =
          readBuffer state (saltBase + 16 * (start + (k + 1))) 16 := by
        rw [show start + 1 + k = start + (k + 1) by omega]
        exact leaf_lane_eval_outside oracle state start (by omega) (4072 + 256 * baseIdx) saltBase heap
          slotPtr saltPtr heapPtr (by omega) (by omega) (by omega) (by omega)
          (Or.inr (by omega)) _ 16 (by omega) (Or.inr (by omega))
          (Or.inr (by have := heap_offset_bound start 16 (by omega); omega))
      rw [saltPres] at hrec
      have hidx : (⟨baseIdx + 1 + k, by omega⟩ : Index) = ⟨baseIdx + (k + 1), by omega⟩ := by
        apply Fin.ext; dsimp; omega
      rw [hidx] at hrec
      simpa only [show start + 1 + k = start + (k + 1) by omega] using hrec

/-- One 32-leaf block writes all 32 reference leaf digests into `heap + heapOffset j`. -/
theorem commit_block_digests (oracle : Oracle) (state : MachineState)
    (baseIdx saltBase heap : Nat) (idxBound : baseIdx + 32 ≤ LENGTH)
    (layout : BlockLayout state (4072 + 256 * baseIdx) saltBase heap)
    (message : Nat → Entry)
    (headData : ∀ k < 32,
      readBuffer state (4096 + 256 * (baseIdx + k)) 72 = (message k).extractLsb' 0 576)
    (blockData : ∀ k < 32, ∀ b, 1 ≤ b → b < 4 →
      readBuffer state (4096 + 256 * (baseIdx + k) + 64 * b) 64 = (message k).extractLsb' (512 * b) 512) :
    ∀ k (hk : k < 32),
      readBuffer (checkEvaluation oracle (commitBlockRun state)).1 (heap + heapOffset k) 32 =
        leafDigest oracle.compression ⟨baseIdx + k, by omega⟩
          (readBuffer state (saltBase + 16 * k) 16) (message k) := by
  intro k hk
  rw [commit_block_evaluation, read_buffer_memory_congr _ _ (commit_block_next_mem _)]
  simpa using leaf_block_lanes_digests oracle state 0 32 baseIdx saltBase heap (by decide)
    idxBound message layout.slotPtr layout.saltPtr layout.heapPtr layout.saltAligned
    layout.heapAfter layout.saltsAfter layout.saltBound headData blockData k hk

end CommitGolfCandidate
