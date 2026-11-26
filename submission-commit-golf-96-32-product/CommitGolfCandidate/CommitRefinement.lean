import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.Model
import CommitGolfCandidate.Memory
import CommitGolfCandidate.Evaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading, the two in-place leaf chains and the heap writes of the actual
commitment pair iteration, refined to the reference salted leaf digests. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Registers and the program counter do not affect buffer reads. -/
theorem commit_read_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

/-- Disjoint, non-wrapping digest buffers have distinct word addresses. -/
theorem commit_separate_words (left right i j : Nat)
    (leftBound : left+32 ≤ 2^64) (rightBound : right+32 ≤ 2^64)
    (iBound : i < 4) (jBound : j < 4)
    (separate : left+32 ≤ right ∨ right+32 ≤ left) :
    BitVec.ofNat 64 (left+8*i) ≠ BitVec.ofNat 64 (right+8*j) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : left+8*i < 2^64),
    Nat.mod_eq_of_lt (by omega : right+8*j < 2^64)] at natural
  rcases separate with before | after <;> omega

/-- Source pointer of the commitment root copy. -/
def commitCopyFrom (state : MachineState) (_start : Nat) : Word := state.getReg .x21

/-- Destination pointer of the commitment root copy. -/
def commitCopyTo (state : MachineState) (_start : Nat) : Word := state.getReg .x26

/-- Copy a complete digest at the commitment root copy site. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (_location : start = 124)
    (sourcePointer : commitCopyFrom state start = BitVec.ofNat 64 source)
    (destinationPointer : commitCopyTo state start = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (commitCopyState state start) destination 32 = readBuffer state source 32 := by
  have sp : state.getReg .x21 = BitVec.ofNat 64 source := sourcePointer
  have dp : state.getReg .x26 = BitVec.ofNat 64 destination := destinationPointer
  apply (read_digest_eq_iff _ _ _ _ destinationAligned sourceAligned).mpr
  intro word inside
  have copied := commit_copy_memory state start (by
    intro i j
    rw [sp, dp, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact commit_separate_words source destination i.val j.val sourceBound destinationBound
      i.isLt j.isLt separate) ⟨word, inside⟩
  simpa only [sp, dp, ← BitVec.ofNat_add] using copied

/-- The root copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (_location : start = 124)
    (destinationPointer : commitCopyTo state start = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  have dp : state.getReg .x26 = BitVec.ofNat 64 destination := destinationPointer
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply commit_copy_memory_outside
  intro j
  rw [dp, ← BitVec.ofNat_add]
  exact commit_separate_words address destination i j.val readBound destinationBound hi j.isLt separate

/-- A 24-byte read is the low 192 bits of the 32-byte read at the same address. -/
theorem commit_read_salt_prefix (state : MachineState) (address : Nat) :
    readBuffer state address 24 = (readBuffer state address 32).extractLsb' 0 192 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  simp only [readBuffer, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2^192 ∣ 2^(8*32))]
  rw [show (32 : Nat) = 24 + 8 by rfl, Finset.sum_range_add]
  have tail : ∀ x ∈ Finset.range 8,
      (state.getByte (BitVec.ofNat 64 (address + (24 + x)))).toNat * 2 ^ (8 * (24 + x)) =
        2^192 * ((state.getByte (BitVec.ofNat 64 (address + (24 + x)))).toNat * 2 ^ (8 * x)) := by
    intro x _
    rw [show 8 * (24 + x) = 192 + 8 * x by omega, Nat.pow_add]
    ring
  rw [Finset.sum_congr rfl tail, ← Finset.mul_sum, Nat.add_mul_mod_self_left]

/-- Equal 32-byte reads have equal 24-byte prefixes. -/
theorem commit_read_salt_of_digest (left right : MachineState) (leftAddress rightAddress : Nat)
    (same : readBuffer left leftAddress 32 = readBuffer right rightAddress 32) :
    readBuffer left leftAddress 24 = readBuffer right rightAddress 24 := by
  rw [commit_read_salt_prefix, commit_read_salt_prefix, same]

private theorem commit_append_nat {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toNat = high.toNat * 2^lowWidth + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

/-- A 32-byte read whose first three words are a 24-byte read and whose fourth word is
zero is the leaf state of that salt. -/
theorem commit_read_salt_state (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0)
    (words : ∀ word < 3, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
      right.getMem (BitVec.ofNat 64 (rightAddress+8*word)))
    (zero : left.getMem (BitVec.ofNat 64 (leftAddress+24)) = 0) :
    readBuffer left leftAddress 32 = saltState (readBuffer right rightAddress 24) := by
  rw [commit_read_salt_prefix, read_digest_words _ _ leftAligned, read_digest_words _ _ rightAligned]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero] at w0 w1 w2
  rw [w0, w1, w2, zero]
  generalize right.getMem (BitVec.ofNat 64 (rightAddress + 24)) = a3
  generalize right.getMem (BitVec.ofNat 64 (rightAddress + 16)) = a2
  generalize right.getMem (BitVec.ofNat 64 (rightAddress + 8)) = a1
  generalize right.getMem (BitVec.ofNat 64 rightAddress) = a0
  apply BitVec.eq_of_toNat_eq
  simp only [saltState, commit_append_nat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_zero]
  have b0 := a0.isLt
  have b1 := a1.isLt
  have b2 := a2.isLt
  have b3 := a3.isLt
  generalize a0.toNat = w0 at *
  generalize a1.toNat = w1 at *
  generalize a2.toNat = w2 at *
  generalize a3.toNat = w3 at *
  norm_num at b0 b1 b2 b3 ⊢
  omega

/-- Salt copy of lane `k`: the lane's state slot holds the leaf state of the 24-byte salt. -/
theorem commit_salt_digest (state : MachineState) (k : Nat) (hk : k < 2) (source destination : Nat)
    (sourcePointer : state.getReg .x18 = BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x8 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source + 24*k + 32 ≤ 2^64) (destinationBound : destination + 256*k + 32 ≤ 2^64)
    (separate : source + 24*k + 32 ≤ destination + 256*k ∨ destination + 256*k + 32 ≤ source + 24*k) :
    readBuffer (commitSaltState state k) (destination + 256*k) 32 =
      saltState (readBuffer state (source + 24*k) 24) := by
  apply commit_read_salt_state _ _ _ _ (by omega) (by omega)
  · intro word inside
    have copied := commit_salt_memory state k hk (by
      intro i j
      rw [sourcePointer, destinationPointer, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
        ← Nat.add_assoc, ← Nat.add_assoc]
      exact commit_separate_words (source + 24*k) (destination + 256*k) i.val j.val sourceBound
        destinationBound (by omega) j.isLt separate) ⟨word, inside⟩
    simpa only [sourcePointer, destinationPointer, ← BitVec.ofNat_add, Nat.add_assoc] using copied
  · have z := commit_salt_memory_zero state k hk
    simpa only [destinationPointer, ← BitVec.ofNat_add, Nat.add_assoc] using z

/-- The salt copy preserves every digest disjoint from the lane's state slot. -/
theorem commit_salt_preserves_digest (state : MachineState) (k : Nat) (hk : k < 2)
    (destination address : Nat)
    (destinationPointer : state.getReg .x8 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 256*k + 32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination + 256*k ∨ destination + 256*k + 32 ≤ address) :
    readBuffer (commitSaltState state k) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ aligned
  intro i hi
  apply commit_salt_memory_outside state k hk
  intro j
  rw [destinationPointer, ← BitVec.ofNat_add, ← Nat.add_assoc]
  exact commit_separate_words address (destination + 256*k) i j.val readBound destinationBound hi
    j.isLt separate

/-- The salt copy preserves every disjoint 64-byte block. -/
theorem commit_salt_preserves_block (state : MachineState) (k : Nat) (hk : k < 2)
    (destination address : Nat)
    (destinationPointer : state.getReg .x8 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 256*k + 32 ≤ 2^64) (readBound : address+64 ≤ 2^64)
    (separate : address+64 ≤ destination + 256*k ∨ destination + 256*k + 32 ≤ address) :
    readBuffer (commitSaltState state k) address 64 = readBuffer state address 64 := by
  rw [read_compression_halves _ _ aligned, read_compression_halves _ _ aligned,
    commit_salt_preserves_digest state k hk destination address destinationPointer
      aligned destinationBound (by omega) (by omega),
    commit_salt_preserves_digest state k hk destination (address+32) destinationPointer
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
      (commitPositionNextState (chainRun oracle (commitSaltState
        (chainRun oracle (commitSaltState state 0) 0) 1) 1), 8) := by
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
  rw [commit_read_congr _ _ (chain_call_memory state k j answer), hout]
  have written := write_bits_digest state out 0 answer (by decide) (by decide)
  simpa using written

/-- Call `j` changes no byte outside its 32-byte output slot. -/
theorem chain_call_outside (state : MachineState) (k j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state k j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainCallState state k j answer) address count = readBuffer state address count := by
  rw [commit_read_congr _ _ (chain_call_memory state k j answer), hout]
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

/-- The register state at the end of the pair iteration's inner part. -/
private theorem pair_inner_registers (oracle : Oracle) (state : MachineState) (reg : Reg)
    (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainRun oracle (commitSaltState state 0) 0).getReg reg = state.getReg reg ∧
    (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1).getReg reg = state.getReg reg := by
  have first : (chainRun oracle (commitSaltState state 0) 0).getReg reg = state.getReg reg := by
    rw [chain_run_register oracle _ 0 (by decide) reg n10 n12, commit_salt_register _ _ reg n6]
  exact ⟨first, (commit_salt_register _ _ reg n6).trans first⟩

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
  saltBound : saltAddress + 56 ≤ MEMORY_BYTES
  heapBound : heap + 64 ≤ MEMORY_BYTES
  saltSlot : saltAddress + 56 ≤ slot ∨ slot + 480 ≤ saltAddress
  heapSlot : heap + 64 ≤ slot ∨ slot + 544 ≤ heap
  saltHeap : saltAddress + 56 ≤ heap ∨ heap + 64 ≤ saltAddress

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
  have c8 := commit_salt_register state 0 .x8 (by decide)
  have c23 := commit_salt_register state 0 .x23 (by decide)
  change readBuffer (chainRun oracle (commitSaltState
    (chainRun oracle (commitSaltState state 0) 0) 1) 1) address 32 = _
  rw [chain_run_outside oracle _ 1 (by decide) slot heap (r8.2.trans layout.slotPointer)
      (r23.2.trans layout.heapPointer) slotBound (by omega) address 32 readBound
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega),
    commit_salt_preserves_digest _ 1 (by decide) slot address (r8.1.trans layout.slotPointer)
      aligned (by omega) readBound (by rcases outsideSlot with h | h <;> omega),
    chain_run_outside oracle _ 0 (by decide) slot heap (c8.trans layout.slotPointer)
      (c23.trans layout.heapPointer) slotBound (by omega) address 32 readBound
      (by rcases outsideSlot with h | h <;> omega) (by rcases outsideHeap with h | h <;> omega),
    commit_salt_preserves_digest _ 0 (by decide) slot address layout.slotPointer
      aligned (by omega) readBound (by rcases outsideSlot with h | h <;> omega)]

set_option maxHeartbeats 3200000 in
/-- One pair iteration of the submitted commitment program stores, for each lane `k`,
the salted leaf digest of the lane's four message blocks in heap slot `heap + 32k`;
the lane's initial state is `saltState` of its packed 24-byte salt at `saltAddress + 24k`. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat) (layout : PairLayout state slot saltAddress heap)
    (value : Nat → Entry)
    (data : ∀ k < 2, ∀ block < 4,
      readBuffer state (slot + 256*k + 32 + 64*block) 64 = (value k).extractLsb' (512*block) 512) :
    ∀ k < 2, readBuffer (checkEvaluation oracle (commitPositionRun state)).1 (heap + 32*k) 32 =
      leafDigest oracle.compression (saltState (readBuffer state (saltAddress + 24*k) 24)) (value k) := by
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
  have c8 := commit_salt_register state 0 .x8 (by decide)
  have c23 := commit_salt_register state 0 .x23 (by decide)
  -- lane 0 sees its salt state and its message blocks
  have s0salt : readBuffer (commitSaltState state 0) slot 32 =
      saltState (readBuffer state saltAddress 24) := by
    have h := commit_salt_digest state 0 (by decide) saltAddress slot layout.saltPointer
      layout.slotPointer saa sla (by omega) (by omega) (by omega)
    simpa using h
  have s0data (index block : Nat) (hi : index < 2) (hb : block < 4) :
      readBuffer (commitSaltState state 0) (slot + 256*index + 32 + 64*block) 64 =
        (value index).extractLsb' (512*block) 512 := by
    rw [commit_salt_preserves_block state 0 (by decide) slot _ layout.slotPointer (by omega)
      (by omega) (by omega) (Or.inr (by omega))]
    exact data index hi block hb
  have lane0 := chain_run_digest oracle (commitSaltState state 0) 0 (by decide) slot heap
    (saltState (readBuffer state saltAddress 24)) (value 0)
    (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound
    (by rw [show slot + 256*0 = slot by omega]; exact s0salt)
    (fun block hb => s0data 0 block (by decide) hb)
  -- lane 1 sees the second salt state and its message blocks
  have firstSalt : readBuffer (chainRun oracle (commitSaltState state 0) 0) (saltAddress + 24) 24 =
      readBuffer state (saltAddress + 24) 24 := by
    apply commit_read_salt_of_digest
    rw [chain_run_outside oracle (commitSaltState state 0) 0 (by decide) slot heap
      (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound (by omega) _ 32
      (by omega) (by omega) (by omega)]
    exact commit_salt_preserves_digest state 0 (by decide) slot _ layout.slotPointer (by omega)
      (by omega) (by omega) (by omega)
  have t0salt : readBuffer (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1)
      (slot + 256) 32 = saltState (readBuffer state (saltAddress + 24) 24) := by
    have h := commit_salt_digest (chainRun oracle (commitSaltState state 0) 0) 1 (by decide)
      saltAddress slot (r18.1.trans layout.saltPointer) (r8.1.trans layout.slotPointer)
      saa sla (by omega) (by omega) (by omega)
    simp only [Nat.mul_one] at h
    rw [h, firstSalt]
  have t0data (block : Nat) (hb : block < 4) :
      readBuffer (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1)
        (slot + 256*1 + 32 + 64*block) 64 = (value 1).extractLsb' (512*block) 512 := by
    rw [commit_salt_preserves_block (chainRun oracle (commitSaltState state 0) 0) 1 (by decide) slot _
        (r8.1.trans layout.slotPointer) (by omega) (by omega) (by omega) (Or.inr (by omega)),
      chain_run_outside oracle (commitSaltState state 0) 0 (by decide) slot heap
        (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound (by omega) _ 64
        (by omega) (Or.inr (by omega)) (by omega)]
    exact s0data 1 block (by decide) hb
  have lane1 := chain_run_digest oracle
    (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1) 1 (by decide) slot heap
    (saltState (readBuffer state (saltAddress + 24) 24)) (value 1)
    (r8.2.trans layout.slotPointer) (r23.2.trans layout.heapPointer) slotBound
    (by rw [show slot + 256*1 = slot + 256 by omega]; exact t0salt) t0data
  intro k hk
  change readBuffer (chainRun oracle
    (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1) 1) (heap + 32*k) 32 = _
  interval_cases k
  · rw [chain_run_outside oracle (commitSaltState (chainRun oracle (commitSaltState state 0) 0) 1)
        1 (by decide) slot heap (r8.2.trans layout.slotPointer)
        (r23.2.trans layout.heapPointer) slotBound (by omega) _ 32 (by omega)
        (by omega) (by omega),
      commit_salt_preserves_digest (chainRun oracle (commitSaltState state 0) 0) 1 (by decide) slot _
        (r8.1.trans layout.slotPointer) (by omega) (by omega) (by omega) (by omega)]
    simpa using lane0
  · simpa using lane1

end CommitGolfCandidate
