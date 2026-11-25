import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading, the two in-place leaf chains and the heap writes of the actual
commitment pair iteration, refined to the reference salted leaf digests. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Source pointer of the commitment digest copy at instruction `start`. -/
def commitCopyFrom (state : MachineState) (start : Nat) : Word :=
  if start = 113 then state.getReg .x9 + 32
  else if start = 39 then state.getReg .x18 else state.getReg .x18 + 32

/-- Destination pointer of the commitment digest copy at instruction `start`. -/
def commitCopyTo (state : MachineState) (start : Nat) : Word :=
  if start = 113 then state.getReg .x26
  else if start = 59 then state.getReg .x8 + 256 else state.getReg .x8

/-- Commitment's three digest copies use the same load/store sequence as opening.
Only the source and destination pointers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 39 ∨ start = 59 ∨ start = 113) :
    (commitCopyState state start).mem =
      (openingCopyState ((state.setReg .x23 (commitCopyFrom state start)).setReg .x25
        (commitCopyTo state start))).mem := by
  rcases location with rfl | rfl | rfl <;>
    rw [commit_copy_expansion, opening_copy_expansion] <;>
    simp (config := { decide := true }) [commitCopyFrom, commitCopyTo, List.foldl, execInstrBr,
      signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

private theorem copy_from_register (state : MachineState) (start : Nat) :
    ((state.setReg .x23 (commitCopyFrom state start)).setReg .x25
      (commitCopyTo state start)).getReg .x23 = commitCopyFrom state start := by
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]

private theorem copy_to_register (state : MachineState) (start : Nat) :
    ((state.setReg .x23 (commitCopyFrom state start)).setReg .x25
      (commitCopyTo state start)).getReg .x25 = commitCopyTo state start :=
  MachineState.getReg_setReg_eq (by decide)

/-- Copy a complete digest at one of the three commitment copy sites. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (location : start = 39 ∨ start = 59 ∨ start = 113)
    (sourcePointer : commitCopyFrom state start = BitVec.ofNat 64 source)
    (destinationPointer : commitCopyTo state start = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (commitCopyState state start) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_digest _ source destination
    ((copy_from_register state start).trans sourcePointer)
    ((copy_to_register state start).trans destinationPointer) sourceAligned destinationAligned
    sourceBound destinationBound separate]
  rfl

/-- The commitment copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (location : start = 39 ∨ start = 59 ∨ start = 113)
    (destinationPointer : commitCopyTo state start = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_preserves_digest _ destination address
    ((copy_to_register state start).trans destinationPointer)
    aligned destinationBound readBound separate]
  rfl

/-- The commitment copy preserves every disjoint 64-byte block. -/
theorem commit_copy_preserves_block (state : MachineState) (start destination address : Nat)
    (location : start = 39 ∨ start = 59 ∨ start = 113)
    (destinationPointer : commitCopyTo state start = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+64 ≤ 2^64)
    (separate : address+64 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 64 = readBuffer state address 64 := by
  rw [read_compression_halves _ _ aligned, read_compression_halves _ _ aligned,
    commit_copy_preserves_digest state start destination address location destinationPointer
      aligned destinationBound (by omega) (by omega),
    commit_copy_preserves_digest state start destination (address+32) location destinationPointer
      (by omega) destinationBound (by omega) (by omega)]

/-- The 96-byte oracle input of in-place call `j` of lane `k`. -/
def chainInput (state : MachineState) (k j : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (chainSource state k j).toNat 96

/-- The reply of one in-place call under a fixed oracle. -/
def chainAnswer (oracle : Oracle) (state : MachineState) (k j : Nat) : BitVec 256 :=
  oracle.compression (chainInput state k j)

/-- One in-place call evaluated with a fixed oracle. -/
def chainStep (oracle : Oracle) (state : MachineState) (k j : Nat) : MachineState :=
  chainCallState state k j (chainAnswer oracle state k j)

/-- The four in-place calls of lane `k`. -/
def chainRun (oracle : Oracle) (state : MachineState) (k : Nat) : MachineState :=
  chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle state k 0) k 1) k 2) k 3

/-- A complete pair iteration under a fixed oracle: salt copy and four calls for each
lane, then advance. -/
theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      (commitPositionNextState (chainRun oracle (commitCopyState
        (chainRun oracle (commitCopyState state 39) 0) 59) 1), 8) := by
  simp only [commitPositionRun, laneRun, bind_assoc, pure_bind, check_evaluation_public_bind,
    check_evaluation_pure]
  rfl

theorem chain_step_register (oracle : Oracle) (state : MachineState) (k j : Nat) (hk : k < 2)
    (hj : j < 4) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainStep oracle state k j).getReg reg = state.getReg reg :=
  chain_call_register state k j hk hj _ reg n10 n12

theorem chain_run_register (oracle : Oracle) (state : MachineState) (k : Nat) (hk : k < 2)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainRun oracle state k).getReg reg = state.getReg reg := by
  unfold chainRun
  rw [chain_step_register _ _ k 3 hk (by decide) reg n10 n12,
    chain_step_register _ _ k 2 hk (by decide) reg n10 n12,
    chain_step_register _ _ k 1 hk (by decide) reg n10 n12,
    chain_step_register _ _ k 0 hk (by decide) reg n10 n12]

/-- Call `j` writes its reply at its output slot. -/
theorem chain_call_written (state : MachineState) (k j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state k j = BitVec.ofNat 64 out) :
    readBuffer (chainCallState state k j answer) out 32 = answer := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state k j answer), hout]
  have written := write_bits_digest state out 0 answer (by decide) (by decide)
  simpa using written

/-- Call `j` changes no byte outside its 32-byte output slot. -/
theorem chain_call_outside (state : MachineState) (k j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state k j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainCallState state k j answer) address count = readBuffer state address count := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state k j answer), hout]
  exact write_bits_read_outside state answer out address count (by simpa using outBound) readBound
    (by simpa using separate)

theorem chain_step_written (oracle : Oracle) (state : MachineState) (k j : Nat)
    (source out : Nat) (hsource : (chainSource state k j).toNat = source)
    (hout : chainOutput state k j = BitVec.ofNat 64 out) :
    readBuffer (chainStep oracle state k j) out 32 =
      absorb oracle.compression (readBuffer state source 32) (readBuffer state (source + 32) 64) := by
  unfold chainStep
  rw [chain_call_written state k j _ out hout]
  unfold chainAnswer chainInput
  rw [hsource, read_leaf_query]
  rfl

theorem chain_step_outside (oracle : Oracle) (state : MachineState) (k j : Nat)
    (out : Nat) (hout : chainOutput state k j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainStep oracle state k j) address count = readBuffer state address count :=
  chain_call_outside state k j _ out hout outBound address count readBound separate

/-- Lane `k`'s input and output addresses for a pair whose first salt slot is `slot`. -/
private theorem lane_addresses (s : MachineState) (k : Nat) (hk : k < 2) (slot heap : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot) (slotBound : slot + 544 ≤ MEMORY_BYTES)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) :
    (chainSource s k 0).toNat = slot + 256*k ∧
    (chainSource s k 1).toNat = slot + 256*k + 64 ∧
    (chainSource s k 2).toNat = slot + 256*k + 128 ∧
    (chainSource s k 3).toNat = slot + 256*k + 192 ∧
    chainOutput s k 0 = BitVec.ofNat 64 (slot + 256*k + 64) ∧
    chainOutput s k 1 = BitVec.ofNat 64 (slot + 256*k + 128) ∧
    chainOutput s k 2 = BitVec.ofNat 64 (slot + 256*k + 192) ∧
    chainOutput s k 3 = BitVec.ofNat 64 (heap + 32*k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, chain_output_heap_nat s k heap heapPointer⟩
  · have h := chain_source_nat s k 0 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 1 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 2 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 3 hk (by decide) slot slotPointer slotBound; omega
  · rw [chain_output_slot_nat s k 0 hk (by decide) slot slotPointer slotBound,
      show slot + 256*k + 64*0 + 64 = slot + 256*k + 64 by omega]
  · rw [chain_output_slot_nat s k 1 hk (by decide) slot slotPointer slotBound,
      show slot + 256*k + 64*1 + 64 = slot + 256*k + 128 by omega]
  · rw [chain_output_slot_nat s k 2 hk (by decide) slot slotPointer slotBound,
      show slot + 256*k + 64*2 + 64 = slot + 256*k + 192 by omega]

theorem leaf_digest_unfold (compress : Compression) (salt : Digest) (value : Entry) :
    leafDigest compress salt value =
      absorb compress (absorb compress (absorb compress (absorb compress salt
        (value.extractLsb' (512*0) 512)) (value.extractLsb' (512*1) 512))
        (value.extractLsb' (512*2) 512)) (value.extractLsb' (512*3) 512) := rfl

set_option maxHeartbeats 1600000 in
/-- Four in-place calls of lane `k`, starting from the lane's salt slot holding the salt
followed by the four message blocks, write the reference salted leaf digest into the
lane's heap slot. -/
theorem chain_run_digest (oracle : Oracle) (s0 : MachineState) (k : Nat) (hk : k < 2)
    (slot heap : Nat) (salt : Digest) (value : Entry)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 544 ≤ MEMORY_BYTES)
    (saltData : readBuffer s0 (slot + 256*k) 32 = salt)
    (data : ∀ block < 4,
      readBuffer s0 (slot + 256*k + 32 + 64*block) 64 = value.extractLsb' (512*block) 512) :
    readBuffer (chainRun oracle s0 k) (heap + 32*k) 32 = leafDigest oracle.compression salt value := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  generalize hL : slot + 256*k = L at saltData data
  have data0 : readBuffer s0 (L + 32) 64 = value.extractLsb' (512*0) 512 := by
    have h := data 0 (by decide); rwa [show L + 32 + 64*0 = L + 32 by omega] at h
  have data1 : readBuffer s0 (L + 64 + 32) 64 = value.extractLsb' (512*1) 512 := by
    have h := data 1 (by decide); rwa [show L + 32 + 64*1 = L + 64 + 32 by omega] at h
  have data2 : readBuffer s0 (L + 128 + 32) 64 = value.extractLsb' (512*2) 512 := by
    have h := data 2 (by decide); rwa [show L + 32 + 64*2 = L + 128 + 32 by omega] at h
  have data3 : readBuffer s0 (L + 192 + 32) 64 = value.extractLsb' (512*3) 512 := by
    have h := data 3 (by decide); rwa [show L + 32 + 64*3 = L + 192 + 32 by omega] at h
  have a0 := lane_addresses s0 k hk slot heap slotPointer slotBound heapPointer
  rw [hL] at a0
  have w0 := chain_step_written oracle s0 k 0 _ _ a0.1 a0.2.2.2.2.1
  have o0 := chain_step_outside oracle s0 k 0 _ a0.2.2.2.2.1 (by omega)
  have x8a := (chain_step_register oracle s0 k 0 hk (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 k 0 hk (by decide) .x23 (by decide) (by decide)).trans heapPointer
  have d0 : readBuffer (chainStep oracle s0 k 0) (L + 64) 32 =
      absorb oracle.compression salt (value.extractLsb' (512*0) 512) := by
    rw [w0, saltData, data0]
  unfold chainRun
  generalize chainStep oracle s0 k 0 = t1 at d0 o0 x8a x23a ⊢
  have a1 := lane_addresses t1 k hk slot heap x8a slotBound x23a
  rw [hL] at a1
  have w1 := chain_step_written oracle t1 k 1 _ _ a1.2.1 a1.2.2.2.2.2.1
  have o1 := chain_step_outside oracle t1 k 1 _ a1.2.2.2.2.2.1 (by omega)
  have x8b := (chain_step_register oracle t1 k 1 hk (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 k 1 hk (by decide) .x23 (by decide) (by decide)).trans x23a
  have d1 : readBuffer (chainStep oracle t1 k 1) (L + 128) 32 =
      absorb oracle.compression (absorb oracle.compression salt (value.extractLsb' (512*0) 512))
        (value.extractLsb' (512*1) 512) := by
    rw [w1, d0, o0 _ 64 (by omega) (Or.inr (by omega)), data1]
  generalize chainStep oracle t1 k 1 = t2 at d1 o1 x8b x23b ⊢
  have a2 := lane_addresses t2 k hk slot heap x8b slotBound x23b
  rw [hL] at a2
  have w2 := chain_step_written oracle t2 k 2 _ _ a2.2.2.1 a2.2.2.2.2.2.2.1
  have o2 := chain_step_outside oracle t2 k 2 _ a2.2.2.2.2.2.2.1 (by omega)
  have x8c := (chain_step_register oracle t2 k 2 hk (by decide) .x8 (by decide) (by decide)).trans x8b
  have x23c := (chain_step_register oracle t2 k 2 hk (by decide) .x23 (by decide) (by decide)).trans x23b
  have d2 : readBuffer (chainStep oracle t2 k 2) (L + 192) 32 =
      absorb oracle.compression (absorb oracle.compression (absorb oracle.compression salt
        (value.extractLsb' (512*0) 512)) (value.extractLsb' (512*1) 512))
        (value.extractLsb' (512*2) 512) := by
    rw [w2, d1, o1 _ 64 (by omega) (Or.inr (by omega)),
      o0 _ 64 (by omega) (Or.inr (by omega)), data2]
  generalize chainStep oracle t2 k 2 = t3 at d2 o2 x8c x23c ⊢
  have a3 := lane_addresses t3 k hk slot heap x8c slotBound x23c
  rw [hL] at a3
  have w3 := chain_step_written oracle t3 k 3 _ _ a3.2.2.2.1 a3.2.2.2.2.2.2.2
  have b3 : L + 192 + 32 + 64 ≤ 2^64 := by omega
  have s2 : L + 192 + 32 + 64 ≤ L + 192 ∨ L + 192 + 32 ≤ L + 192 + 32 := Or.inr (Nat.le_refl _)
  have s1 : L + 192 + 32 + 64 ≤ L + 128 ∨ L + 128 + 32 ≤ L + 192 + 32 := Or.inr (by omega)
  have s0 : L + 192 + 32 + 64 ≤ L + 64 ∨ L + 64 + 32 ≤ L + 192 + 32 := Or.inr (by omega)
  have e3 : readBuffer t3 (L + 192 + 32) 64 = value.extractLsb' (512*3) 512 :=
    ((o2 _ 64 b3 s2).trans ((o1 _ 64 b3 s1).trans (o0 _ 64 b3 s0))).trans data3
  rewrite [w3, d2, e3]
  exact (leaf_digest_unfold _ _ _).symm

set_option maxHeartbeats 1600000 in
/-- The four in-place calls of lane `k` preserve every byte range outside the lane's
chain region `[slot+256k+64, slot+256k+224)` and its heap output slot. -/
theorem chain_run_outside (oracle : Oracle) (s0 : MachineState) (k : Nat) (hk : k < 2)
    (slot heap : Nat)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 544 ≤ MEMORY_BYTES) (heapBound : heap + 32*k + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outsideSlot : address + count ≤ slot + 256*k + 64 ∨ slot + 256*k + 224 ≤ address)
    (outsideHeap : address + count ≤ heap + 32*k ∨ heap + 32*k + 32 ≤ address) :
    readBuffer (chainRun oracle s0 k) address count = readBuffer s0 address count := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have a0 := lane_addresses s0 k hk slot heap slotPointer slotBound heapPointer
  have o0 := chain_step_outside oracle s0 k 0 _ a0.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8a := (chain_step_register oracle s0 k 0 hk (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 k 0 hk (by decide) .x23 (by decide) (by decide)).trans heapPointer
  unfold chainRun
  generalize chainStep oracle s0 k 0 = t1 at o0 x8a x23a ⊢
  have a1 := lane_addresses t1 k hk slot heap x8a slotBound x23a
  have o1 := chain_step_outside oracle t1 k 1 _ a1.2.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8b := (chain_step_register oracle t1 k 1 hk (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 k 1 hk (by decide) .x23 (by decide) (by decide)).trans x23a
  generalize chainStep oracle t1 k 1 = t2 at o1 x8b x23b ⊢
  have a2 := lane_addresses t2 k hk slot heap x8b slotBound x23b
  have o2 := chain_step_outside oracle t2 k 2 _ a2.2.2.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8c := (chain_step_register oracle t2 k 2 hk (by decide) .x8 (by decide) (by decide)).trans x8b
  have x23c := (chain_step_register oracle t2 k 2 hk (by decide) .x23 (by decide) (by decide)).trans x23b
  generalize chainStep oracle t2 k 2 = t3 at o2 x8c x23c ⊢
  have a3 := lane_addresses t3 k hk slot heap x8c slotBound x23c
  have o3 := chain_step_outside oracle t3 k 3 _ a3.2.2.2.2.2.2.2 heapBound
    address count readBound outsideHeap
  rw [o3, o2, o1, o0]

/-- Registers of the salt copies. -/
theorem commit_salt_copy_register (state : MachineState) (start : Nat) (reg : Reg) (n6 : reg ≠ .x6) :
    (commitCopyState state start).getReg reg = state.getReg reg :=
  commit_copy_register state start reg n6

/-- The register state at the end of the pair iteration's inner part. -/
private theorem pair_inner_registers (oracle : Oracle) (state : MachineState) (reg : Reg)
    (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainRun oracle (commitCopyState state 39) 0).getReg reg = state.getReg reg ∧
    (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59).getReg reg = state.getReg reg := by
  have first : (chainRun oracle (commitCopyState state 39) 0).getReg reg = state.getReg reg := by
    rw [chain_run_register oracle _ 0 (by decide) reg n10 n12, commit_copy_register _ _ reg n6]
  exact ⟨first, (commit_copy_register _ _ reg n6).trans first⟩

theorem word_add_literal (w : Word) (a b : Nat) (h : w = BitVec.ofNat 64 a) :
    w + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [h, BitVec.ofNat_add]

/-- Hypotheses describing one pair iteration's memory before it runs. -/
structure PairLayout (state : MachineState) (slot saltAddress heap : Nat) : Prop where
  slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot
  saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress
  heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap
  slotAligned : slot % 8 = 0
  saltAligned : saltAddress % 8 = 0
  heapAligned : heap % 8 = 0
  slotBound : slot + 544 ≤ MEMORY_BYTES
  saltBound : saltAddress + 64 ≤ MEMORY_BYTES
  heapBound : heap + 64 ≤ MEMORY_BYTES
  saltSlot : saltAddress + 64 ≤ slot ∨ slot + 480 ≤ saltAddress
  heapSlot : heap + 64 ≤ slot ∨ slot + 544 ≤ heap
  saltHeap : saltAddress + 64 ≤ heap ∨ heap + 64 ≤ saltAddress

set_option maxHeartbeats 1600000 in
/-- One pair iteration preserves every digest outside `[slot, slot+480)` and the
heap output pair `[heap, heap+64)`. This includes all later message blocks, salts and
leaf digests, and the zero gap behind the heap pair. -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap address : Nat) (layout : PairLayout state slot saltAddress heap)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2^64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 480 ≤ address)
    (outsideHeap : address + 32 ≤ heap ∨ heap + 64 ≤ address) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 address 32 =
      readBuffer state address 32 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have slotBound := layout.slotBound
  have heapBd := layout.heapBound
  rw [commit_position_evaluation]
  have r8 := pair_inner_registers oracle state .x8 (by decide) (by decide) (by decide)
  have r23 := pair_inner_registers oracle state .x23 (by decide) (by decide) (by decide)
  have c8 := commit_copy_register state 39 .x8 (by decide)
  have c23 := commit_copy_register state 39 .x23 (by decide)
  change readBuffer (chainRun oracle (commitCopyState
    (chainRun oracle (commitCopyState state 39) 0) 59) 1) address 32 = _
  rw [chain_run_outside oracle _ 1 (by decide) slot heap (r8.2.trans layout.slotPointer)
      (r23.2.trans layout.heapPointer) slotBound (by omega) address 32 readBound
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega),
    commit_copy_preserves_digest _ 59 (slot + 256) address (Or.inr (Or.inl rfl))
      (by simp (config := { decide := true }) only [commitCopyTo, ↓reduceIte]
          exact word_add_literal _ slot 256 (r8.1.trans layout.slotPointer))
      aligned (by omega) readBound (by rcases outsideSlot with h | h <;> omega),
    chain_run_outside oracle _ 0 (by decide) slot heap (c8.trans layout.slotPointer)
      (c23.trans layout.heapPointer) slotBound (by omega) address 32 readBound
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega),
    commit_copy_preserves_digest _ 39 slot address (Or.inl rfl)
      (by simp (config := { decide := true }) only [commitCopyTo, ↓reduceIte]
          exact layout.slotPointer)
      aligned (by omega) readBound (by rcases outsideSlot with h | h <;> omega)]

set_option maxHeartbeats 3200000 in
/-- One pair iteration of the submitted commitment program stores, for each lane `k`,
the salted leaf digest of the lane's four message blocks in heap slot `heap + 32k`. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat) (layout : PairLayout state slot saltAddress heap)
    (value : Nat → Entry)
    (data : ∀ k < 2, ∀ block < 4,
      readBuffer state (slot + 256*k + 32 + 64*block) 64 = (value k).extractLsb' (512*block) 512) :
    ∀ k < 2, readBuffer (checkEvaluation oracle (commitPositionRun state)).1 (heap + 32*k) 32 =
      leafDigest oracle.compression (readBuffer state (saltAddress + 32*k) 32) (value k) := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have slotBound := layout.slotBound
  have sl := layout.saltSlot
  have hs := layout.heapSlot
  have sh := layout.saltHeap
  have sla := layout.slotAligned
  have saa := layout.saltAligned
  have hea := layout.heapAligned
  have saltBd := layout.saltBound
  have heapBd := layout.heapBound
  rw [commit_position_evaluation]
  have r8 := pair_inner_registers oracle state .x8 (by decide) (by decide) (by decide)
  have r18 := pair_inner_registers oracle state .x18 (by decide) (by decide) (by decide)
  have r23 := pair_inner_registers oracle state .x23 (by decide) (by decide) (by decide)
  have c8 := commit_copy_register state 39 .x8 (by decide)
  have c23 := commit_copy_register state 39 .x23 (by decide)
  have to39 : commitCopyTo state 39 = BitVec.ofNat 64 slot := by
    simp (config := { decide := true }) only [commitCopyTo, ↓reduceIte]
    exact layout.slotPointer
  have from39 : commitCopyFrom state 39 = BitVec.ofNat 64 saltAddress := by
    simp (config := { decide := true }) only [commitCopyFrom, ↓reduceIte]
    exact layout.saltPointer
  have to59 : commitCopyTo (chainRun oracle (commitCopyState state 39) 0) 59 =
      BitVec.ofNat 64 (slot + 256) := by
    simp (config := { decide := true }) only [commitCopyTo, ↓reduceIte]
    exact word_add_literal _ slot 256 (r8.1.trans layout.slotPointer)
  have from59 : commitCopyFrom (chainRun oracle (commitCopyState state 39) 0) 59 =
      BitVec.ofNat 64 (saltAddress + 32) := by
    simp (config := { decide := true }) only [commitCopyFrom, ↓reduceIte]
    exact word_add_literal _ saltAddress 32 (r18.1.trans layout.saltPointer)
  -- lane 0 sees the salt and its message blocks
  have s0salt : readBuffer (commitCopyState state 39) slot 32 = readBuffer state saltAddress 32 :=
    commit_copy_digest state 39 saltAddress slot (Or.inl rfl) from39 to39 saa sla
      (by omega) (by omega) (by omega)
  have s0data (index block : Nat) (hi : index < 2) (hb : block < 4) :
      readBuffer (commitCopyState state 39) (slot + 256*index + 32 + 64*block) 64 =
        (value index).extractLsb' (512*block) 512 := by
    rw [commit_copy_preserves_block state 39 slot _ (Or.inl rfl) to39 (by omega) (by omega)
      (by omega) (Or.inr (by omega))]
    exact data index hi block hb
  have lane0 := chain_run_digest oracle (commitCopyState state 39) 0 (by decide) slot heap
    (readBuffer state saltAddress 32) (value 0)
    (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound
    (by rw [show slot + 256*0 = slot by omega]; exact s0salt)
    (fun block hb => s0data 0 block (by decide) hb)
  -- lane 1 sees the second salt and its message blocks
  have firstSalt : readBuffer (chainRun oracle (commitCopyState state 39) 0) (saltAddress + 32) 32 =
      readBuffer state (saltAddress + 32) 32 := by
    rw [chain_run_outside oracle (commitCopyState state 39) 0 (by decide) slot heap
      (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound (by omega) _ 32
      (by omega) (by omega) (by omega)]
    exact commit_copy_preserves_digest state 39 slot _ (Or.inl rfl) to39 (by omega) (by omega)
      (by omega) (by omega)
  have t0salt : readBuffer (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59)
      (slot + 256) 32 = readBuffer state (saltAddress + 32) 32 := by
    rw [commit_copy_digest (chainRun oracle (commitCopyState state 39) 0) 59 (saltAddress + 32)
      (slot + 256) (Or.inr (Or.inl rfl)) from59 to59
      (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact firstSalt
  have t0data (block : Nat) (hb : block < 4) :
      readBuffer (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59)
        (slot + 256*1 + 32 + 64*block) 64 = (value 1).extractLsb' (512*block) 512 := by
    rw [commit_copy_preserves_block (chainRun oracle (commitCopyState state 39) 0) 59 (slot + 256) _
        (Or.inr (Or.inl rfl)) to59 (by omega) (by omega) (by omega) (Or.inr (by omega)),
      chain_run_outside oracle (commitCopyState state 39) 0 (by decide) slot heap
        (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound (by omega) _ 64
        (by omega) (Or.inr (by omega)) (by omega)]
    exact s0data 1 block (by decide) hb
  have lane1 := chain_run_digest oracle
    (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59) 1 (by decide) slot heap
    (readBuffer state (saltAddress + 32) 32) (value 1)
    (r8.2.trans layout.slotPointer) (r23.2.trans layout.heapPointer) slotBound
    (by rw [show slot + 256*1 = slot + 256 by omega]; exact t0salt) t0data
  intro k hk
  change readBuffer (chainRun oracle
    (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59) 1) (heap + 32*k) 32 = _
  interval_cases k
  · rw [chain_run_outside oracle (commitCopyState (chainRun oracle (commitCopyState state 39) 0) 59)
        1 (by decide) slot heap (r8.2.trans layout.slotPointer)
        (r23.2.trans layout.heapPointer) slotBound (by omega) _ 32 (by omega)
        (by omega) (by omega),
      commit_copy_preserves_digest (chainRun oracle (commitCopyState state 39) 0) 59 (slot + 256) _
        (Or.inr (Or.inl rfl)) to59 (by omega) (by omega) (by omega) (by omega)]
    simpa using lane0
  · simpa using lane1

end CommitGolfCandidate
