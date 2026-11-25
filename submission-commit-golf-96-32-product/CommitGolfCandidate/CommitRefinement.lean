import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading, the 32 in-place leaf chains (four 8-leaf chunks) and the heap writes
of one commitment iteration, refined to the reference salted leaf digests. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Source pointer of a commitment digest copy. -/
def commitCopyFrom (state : MachineState) (src : Reg) (srcOff : Nat) : Word :=
  state.getReg src + BitVec.ofNat 64 srcOff

/-- Destination pointer of a commitment digest copy. -/
def commitCopyTo (state : MachineState) (dst : Reg) (dstOff : Nat) : Word :=
  state.getReg dst + BitVec.ofNat 64 dstOff

private theorem setReg_mem (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).mem = s.mem := by cases r <;> rfl

private theorem copy_step_mem (s1 s2 : MachineState) (r1 d1 r2 d2 : Reg)
    (o1 o2 o3 o4 : BitVec 12)
    (hmem : s1.mem = s2.mem) (hd1 : d1 ≠ .x6) (hd2 : d2 ≠ .x6)
    (hsrc : s1.getReg r1 + signExtend12 o1 = s2.getReg r2 + signExtend12 o3)
    (hdst : s1.getReg d1 + signExtend12 o2 = s2.getReg d2 + signExtend12 o4) :
    let s1' := execInstrBr (execInstrBr s1 (.LD .x6 r1 o1)) (.SD d1 .x6 o2)
    let s2' := execInstrBr (execInstrBr s2 (.LD .x6 r2 o3)) (.SD d2 .x6 o4)
    s1'.mem = s2'.mem ∧
    (∀ reg, reg ≠ .x6 → s1'.getReg reg = s1.getReg reg) ∧
    (∀ reg, reg ≠ .x6 → s2'.getReg reg = s2.getReg reg) := by
  have hrm (s : MachineState) (a v : Word) (reg : Reg) :
      (s.setMem a v).getReg reg = s.getReg reg := by cases reg <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hd2)]
    simp only [MachineState.setPC, MachineState.setMem, MachineState.getMem, setReg_mem,
      hmem, hsrc, hdst]
  · intro reg hreg
    simp only [execInstrBr, MachineState.getReg_setPC, hrm,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hreg)]
  · intro reg hreg
    simp only [execInstrBr, MachineState.getReg_setPC, hrm,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hreg)]

/-- Any commitment digest copy uses the same load/store sequence as opening. -/
theorem commit_copy_memory_as_opening (state : MachineState) (src dst : Reg)
    (srcOff dstOff : Nat) (hsrc6 : src ≠ .x6) (hdst6 : dst ≠ .x6)
    (hsrcBound : srcOff + 24 < 2048) (hsrcAligned : srcOff % 8 = 0)
    (hdstBound : dstOff + 24 < 2048) (hdstAligned : dstOff % 8 = 0) :
    (commitCopyState state src dst srcOff dstOff).mem =
      (openingCopyState ((state.setReg .x23 (commitCopyFrom state src srcOff)).setReg .x25
        (commitCopyTo state dst dstOff))).mem := by
  let t0 := (state.setReg .x23 (commitCopyFrom state src srcOff)).setReg .x25
    (commitCopyTo state dst dstOff)
  have ht0mem : state.mem = t0.mem := by simp only [t0, setReg_mem]
  have ht0x23 : t0.getReg .x23 = state.getReg src + BitVec.ofNat 64 srcOff := by
    simp only [t0, commitCopyFrom, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x23),
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0)]
  have ht0x25 : t0.getReg .x25 = state.getReg dst + BitVec.ofNat 64 dstOff := by
    simp only [t0, commitCopyTo, MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0)]
  have hs (w : Nat) (hw : w < 4) :
      signExtend12 (BitVec.ofNat 12 (srcOff + 8 * w)) =
        BitVec.ofNat 64 srcOff + BitVec.ofNat 64 (8 * w) := by
    rw [signExtend12_ofNat_mul8 (srcOff + 8 * w) (by omega) (by omega), BitVec.ofNat_add]
  have hd (w : Nat) (hw : w < 4) :
      signExtend12 (BitVec.ofNat 12 (dstOff + 8 * w)) =
        BitVec.ofNat 64 dstOff + BitVec.ofNat 64 (8 * w) := by
    rw [signExtend12_ofNat_mul8 (dstOff + 8 * w) (by omega) (by omega), BitVec.ofNat_add]
  have step0 := copy_step_mem state t0 src dst .x23 .x25
    (BitVec.ofNat 12 srcOff) (BitVec.ofNat 12 dstOff) 0 0 ht0mem hdst6 (by decide)
    (by rw [ht0x23, signExtend12_0, signExtend12_ofNat_mul8 srcOff (by omega) hsrcAligned]; simp)
    (by rw [ht0x25, signExtend12_0, signExtend12_ofNat_mul8 dstOff (by omega) hdstAligned]; simp)
  let s1 := execInstrBr (execInstrBr state (.LD .x6 src (BitVec.ofNat 12 srcOff))) (.SD dst .x6 (BitVec.ofNat 12 dstOff))
  let t1 := execInstrBr (execInstrBr t0 (.LD .x6 .x23 0)) (.SD .x25 .x6 0)
  have step1 := copy_step_mem s1 t1 src dst .x23 .x25
    (BitVec.ofNat 12 (srcOff + 8)) (BitVec.ofNat 12 (dstOff + 8)) 8 8 step0.1 hdst6 (by decide)
    (by rw [step0.2.1 src hsrc6, step0.2.2 .x23 (by decide), ht0x23, signExtend12_8,
          show srcOff + 8 = srcOff + 8 * 1 by omega, hs 1 (by decide), BitVec.add_assoc]; rfl)
    (by rw [step0.2.1 dst hdst6, step0.2.2 .x25 (by decide), ht0x25, signExtend12_8,
          show dstOff + 8 = dstOff + 8 * 1 by omega, hd 1 (by decide), BitVec.add_assoc]; rfl)
  let s2 := execInstrBr (execInstrBr s1 (.LD .x6 src (BitVec.ofNat 12 (srcOff + 8)))) (.SD dst .x6 (BitVec.ofNat 12 (dstOff + 8)))
  let t2 := execInstrBr (execInstrBr t1 (.LD .x6 .x23 8)) (.SD .x25 .x6 8)
  have step2 := copy_step_mem s2 t2 src dst .x23 .x25
    (BitVec.ofNat 12 (srcOff + 16)) (BitVec.ofNat 12 (dstOff + 16)) 16 16 step1.1 hdst6 (by decide)
    (by rw [step1.2.1 src hsrc6, step0.2.1 src hsrc6, step1.2.2 .x23 (by decide),
          step0.2.2 .x23 (by decide), ht0x23, signExtend12_16,
          show srcOff + 16 = srcOff + 8 * 2 by omega, hs 2 (by decide), BitVec.add_assoc]; rfl)
    (by rw [step1.2.1 dst hdst6, step0.2.1 dst hdst6, step1.2.2 .x25 (by decide),
          step0.2.2 .x25 (by decide), ht0x25, signExtend12_16,
          show dstOff + 16 = dstOff + 8 * 2 by omega, hd 2 (by decide), BitVec.add_assoc]; rfl)
  let s3 := execInstrBr (execInstrBr s2 (.LD .x6 src (BitVec.ofNat 12 (srcOff + 16)))) (.SD dst .x6 (BitVec.ofNat 12 (dstOff + 16)))
  let t3 := execInstrBr (execInstrBr t2 (.LD .x6 .x23 16)) (.SD .x25 .x6 16)
  have step3 := copy_step_mem s3 t3 src dst .x23 .x25
    (BitVec.ofNat 12 (srcOff + 24)) (BitVec.ofNat 12 (dstOff + 24)) 24 24 step2.1 hdst6 (by decide)
    (by rw [step2.2.1 src hsrc6, step1.2.1 src hsrc6, step0.2.1 src hsrc6,
          step2.2.2 .x23 (by decide), step1.2.2 .x23 (by decide), step0.2.2 .x23 (by decide),
          ht0x23, signExtend12_24,
          show srcOff + 24 = srcOff + 8 * 3 by omega, hs 3 (by decide), BitVec.add_assoc]; rfl)
    (by rw [step2.2.1 dst hdst6, step1.2.1 dst hdst6, step0.2.1 dst hdst6,
          step2.2.2 .x25 (by decide), step1.2.2 .x25 (by decide), step0.2.2 .x25 (by decide),
          ht0x25, signExtend12_24,
          show dstOff + 24 = dstOff + 8 * 3 by omega, hd 3 (by decide), BitVec.add_assoc]; rfl)
  rw [commit_copy_expansion, opening_copy_expansion]
  exact step3.1

private theorem copy_from_register (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat) :
    ((state.setReg .x23 (commitCopyFrom state src srcOff)).setReg .x25
      (commitCopyTo state dst dstOff)).getReg .x23 = commitCopyFrom state src srcOff := by
  rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide), MachineState.getReg_setReg_eq (by decide)]

private theorem copy_to_register (state : MachineState) (src dst : Reg) (srcOff dstOff : Nat) :
    ((state.setReg .x23 (commitCopyFrom state src srcOff)).setReg .x25
      (commitCopyTo state dst dstOff)).getReg .x25 = commitCopyTo state dst dstOff :=
  MachineState.getReg_setReg_eq (by decide)

/-- Copy a complete digest at any commitment copy site. -/
theorem commit_copy_digest (state : MachineState) (src dst : Reg)
    (srcOff dstOff source destination : Nat)
    (hsrc6 : src ≠ .x6) (hdst6 : dst ≠ .x6)
    (hsrcBound : srcOff + 24 < 2048) (hsrcAligned : srcOff % 8 = 0)
    (hdstBound : dstOff + 24 < 2048) (hdstAligned : dstOff % 8 = 0)
    (sourcePointer : commitCopyFrom state src srcOff = BitVec.ofNat 64 source)
    (destinationPointer : commitCopyTo state dst dstOff = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source + 32 ≤ 2 ^ 64) (destinationBound : destination + 32 ≤ 2 ^ 64)
    (separate : source + 32 ≤ destination ∨ destination + 32 ≤ source) :
    readBuffer (commitCopyState state src dst srcOff dstOff) destination 32 =
      readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state src dst srcOff dstOff
    hsrc6 hdst6 hsrcBound hsrcAligned hdstBound hdstAligned)]
  rw [opening_copy_digest _ source destination
    ((copy_from_register state src dst srcOff dstOff).trans sourcePointer)
    ((copy_to_register state src dst srcOff dstOff).trans destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate]
  rfl

/-- Any commitment copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (src dst : Reg)
    (srcOff dstOff destination address : Nat)
    (hsrc6 : src ≠ .x6) (hdst6 : dst ≠ .x6)
    (hsrcBound : srcOff + 24 < 2048) (hsrcAligned : srcOff % 8 = 0)
    (hdstBound : dstOff + 24 < 2048) (hdstAligned : dstOff % 8 = 0)
    (destinationPointer : commitCopyTo state dst dstOff = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 32 ≤ 2 ^ 64) (readBound : address + 32 ≤ 2 ^ 64)
    (separate : address + 32 ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (commitCopyState state src dst srcOff dstOff) address 32 =
      readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state src dst srcOff dstOff
    hsrc6 hdst6 hsrcBound hsrcAligned hdstBound hdstAligned)]
  rw [opening_copy_preserves_digest _ destination address
    ((copy_to_register state src dst srcOff dstOff).trans destinationPointer)
    aligned destinationBound readBound separate]
  rfl

/-- Any commitment copy preserves every disjoint 64-byte block. -/
theorem commit_copy_preserves_block (state : MachineState) (src dst : Reg)
    (srcOff dstOff destination address : Nat)
    (hsrc6 : src ≠ .x6) (hdst6 : dst ≠ .x6)
    (hsrcBound : srcOff + 24 < 2048) (hsrcAligned : srcOff % 8 = 0)
    (hdstBound : dstOff + 24 < 2048) (hdstAligned : dstOff % 8 = 0)
    (destinationPointer : commitCopyTo state dst dstOff = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination + 32 ≤ 2 ^ 64) (readBound : address + 64 ≤ 2 ^ 64)
    (separate : address + 64 ≤ destination ∨ destination + 32 ≤ address) :
    readBuffer (commitCopyState state src dst srcOff dstOff) address 64 =
      readBuffer state address 64 := by
  rw [read_compression_halves _ _ aligned, read_compression_halves _ _ aligned,
    commit_copy_preserves_digest state src dst srcOff dstOff destination address
      hsrc6 hdst6 hsrcBound hsrcAligned hdstBound hdstAligned destinationPointer
      aligned destinationBound (by omega) (by omega),
    commit_copy_preserves_digest state src dst srcOff dstOff destination (address + 32)
      hsrc6 hdst6 hsrcBound hsrcAligned hdstBound hdstAligned destinationPointer
      (by omega) destinationBound (by omega) (by omega)]

/-- The 96-byte oracle input of in-place call `j` of lane `k`. -/
def chainInput (state : MachineState) (k j : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (chainSource state k j).toNat 96

/-- The reply of one in-place call under a fixed oracle. -/
def chainAnswer (oracle : Oracle) (state : MachineState) (k j : Nat) : BitVec 256 :=
  oracle.compression (chainInput state k j)

/-- One in-place call evaluated with a fixed oracle. -/
def chainStep (oracle : Oracle) (state : MachineState) (c k j : Nat) : MachineState :=
  chainCallState state c k j (chainAnswer oracle state k j)

/-- The four in-place calls of lane `k` in chunk `c`. -/
def chainRun (oracle : Oracle) (state : MachineState) (c k : Nat) : MachineState :=
  chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle state c k 0) c k 1) c k 2) c k 3

/-- One leaf evaluated under a fixed oracle: salt copy then four in-place calls. -/
def leafEval (oracle : Oracle) (state : MachineState) (c k : Nat) : MachineState :=
  chainRun oracle (commitCopyState state .x18 .x8 (256 * c + 32 * k) (256 * k)) c k

theorem leaf_run_evaluation (oracle : Oracle) (state : MachineState) (c k : Nat) :
    checkEvaluation oracle (leafRun state c k) = (leafEval oracle state c k, 4) := by
  simp only [leafRun, laneRun, bind_assoc, pure_bind, check_evaluation_public_bind,
    check_evaluation_pure]
  rfl

theorem chain_step_register (oracle : Oracle) (state : MachineState) (c k j : Nat)
    (hc : c < 4) (hk : k < 8) (hj : j < 4) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainStep oracle state c k j).getReg reg = state.getReg reg :=
  chain_call_register state c k j hc hk hj _ reg n10 n12

theorem chain_run_register (oracle : Oracle) (state : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8) (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainRun oracle state c k).getReg reg = state.getReg reg := by
  unfold chainRun
  rw [chain_step_register _ _ c k 3 hc hk (by decide) reg n10 n12,
    chain_step_register _ _ c k 2 hc hk (by decide) reg n10 n12,
    chain_step_register _ _ c k 1 hc hk (by decide) reg n10 n12,
    chain_step_register _ _ c k 0 hc hk (by decide) reg n10 n12]

theorem leaf_eval_register (oracle : Oracle) (state : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8) (reg : Reg)
    (n6 : reg ≠ .x6) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (leafEval oracle state c k).getReg reg = state.getReg reg :=
  (chain_run_register oracle _ c k hc hk reg n10 n12).trans
    (commit_copy_register state .x18 .x8 _ _ reg n6)

/-- Call `j` writes its reply at its output slot. -/
theorem chain_call_written (state : MachineState) (c k j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state c k j = BitVec.ofNat 64 out) :
    readBuffer (chainCallState state c k j answer) out 32 = answer := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state c k j answer), hout]
  have written := write_bits_digest state out 0 answer (by decide) (by decide)
  simpa using written

/-- Call `j` changes no byte outside its 32-byte output slot. -/
theorem chain_call_outside (state : MachineState) (c k j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state c k j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2 ^ 64)
    (address count : Nat) (readBound : address + count ≤ 2 ^ 64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainCallState state c k j answer) address count = readBuffer state address count := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state c k j answer), hout]
  exact write_bits_read_outside state answer out address count (by simpa using outBound) readBound
    (by simpa using separate)

theorem chain_step_written (oracle : Oracle) (state : MachineState) (c k j : Nat)
    (source out : Nat) (hsource : (chainSource state k j).toNat = source)
    (hout : chainOutput state c k j = BitVec.ofNat 64 out) :
    readBuffer (chainStep oracle state c k j) out 32 =
      absorb oracle.compression (readBuffer state source 32) (readBuffer state (source + 32) 64) := by
  unfold chainStep
  rw [chain_call_written state c k j _ out hout]
  unfold chainAnswer chainInput
  rw [hsource, read_leaf_query]
  rfl

theorem chain_step_outside (oracle : Oracle) (state : MachineState) (c k j : Nat)
    (out : Nat) (hout : chainOutput state c k j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2 ^ 64)
    (address count : Nat) (readBound : address + count ≤ 2 ^ 64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainStep oracle state c k j) address count = readBuffer state address count :=
  chain_call_outside state c k j _ out hout outBound address count readBound separate

private theorem lane_addresses (s : MachineState) (c k : Nat) (hk : k < 8) (slot heap : Nat)
    (slotPointer : s.getReg .x8 = BitVec.ofNat 64 slot) (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (heapPointer : s.getReg .x23 = BitVec.ofNat 64 heap) :
    (chainSource s k 0).toNat = slot + 256 * k ∧
    (chainSource s k 1).toNat = slot + 256 * k + 64 ∧
    (chainSource s k 2).toNat = slot + 256 * k + 128 ∧
    (chainSource s k 3).toNat = slot + 256 * k + 192 ∧
    chainOutput s c k 0 = BitVec.ofNat 64 (slot + 256 * k + 64) ∧
    chainOutput s c k 1 = BitVec.ofNat 64 (slot + 256 * k + 128) ∧
    chainOutput s c k 2 = BitVec.ofNat 64 (slot + 256 * k + 192) ∧
    chainOutput s c k 3 = BitVec.ofNat 64 (heap + 384 * c + heapOffset k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, chain_output_heap_nat s c k heap heapPointer⟩
  · have h := chain_source_nat s k 0 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 1 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 2 hk (by decide) slot slotPointer slotBound; omega
  · have h := chain_source_nat s k 3 hk (by decide) slot slotPointer slotBound; omega
  · rw [chain_output_slot_nat s c k 0 hk (by decide) slot slotPointer slotBound,
      show slot + 256 * k + 64 * 0 + 64 = slot + 256 * k + 64 by omega]
  · rw [chain_output_slot_nat s c k 1 hk (by decide) slot slotPointer slotBound,
      show slot + 256 * k + 64 * 1 + 64 = slot + 256 * k + 128 by omega]
  · rw [chain_output_slot_nat s c k 2 hk (by decide) slot slotPointer slotBound,
      show slot + 256 * k + 64 * 2 + 64 = slot + 256 * k + 192 by omega]

theorem leaf_digest_unfold (compress : Compression) (salt : Digest) (value : Entry) :
    leafDigest compress salt value =
      absorb compress (absorb compress (absorb compress (absorb compress salt
        (value.extractLsb' (512 * 0) 512)) (value.extractLsb' (512 * 1) 512))
        (value.extractLsb' (512 * 2) 512)) (value.extractLsb' (512 * 3) 512) := rfl

set_option maxHeartbeats 1600000 in
/-- Four in-place calls of lane `k` in chunk `c` write the reference salted leaf digest
into `heap + 384*c + heapOffset k`. -/
theorem chain_run_digest (oracle : Oracle) (s0 : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8) (slot heap : Nat) (salt : Digest) (value : Entry)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (saltData : readBuffer s0 (slot + 256 * k) 32 = salt)
    (data : ∀ block < 4,
      readBuffer s0 (slot + 256 * k + 32 + 64 * block) 64 = value.extractLsb' (512 * block) 512) :
    readBuffer (chainRun oracle s0 c k) (heap + 384 * c + heapOffset k) 32 =
      leafDigest oracle.compression salt value := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  generalize hL : slot + 256 * k = L at saltData data
  have data0 : readBuffer s0 (L + 32) 64 = value.extractLsb' (512 * 0) 512 := by
    have h := data 0 (by decide); rwa [show L + 32 + 64 * 0 = L + 32 by omega] at h
  have data1 : readBuffer s0 (L + 64 + 32) 64 = value.extractLsb' (512 * 1) 512 := by
    have h := data 1 (by decide); rwa [show L + 32 + 64 * 1 = L + 64 + 32 by omega] at h
  have data2 : readBuffer s0 (L + 128 + 32) 64 = value.extractLsb' (512 * 2) 512 := by
    have h := data 2 (by decide); rwa [show L + 32 + 64 * 2 = L + 128 + 32 by omega] at h
  have data3 : readBuffer s0 (L + 192 + 32) 64 = value.extractLsb' (512 * 3) 512 := by
    have h := data 3 (by decide); rwa [show L + 32 + 64 * 3 = L + 192 + 32 by omega] at h
  have a0 := lane_addresses s0 c k hk slot heap slotPointer slotBound heapPointer
  rw [hL] at a0
  have w0 := chain_step_written oracle s0 c k 0 _ _ a0.1 a0.2.2.2.2.1
  have o0 := chain_step_outside oracle s0 c k 0 _ a0.2.2.2.2.1 (by omega)
  have x8a := (chain_step_register oracle s0 c k 0 hc hk (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 c k 0 hc hk (by decide) .x23 (by decide) (by decide)).trans heapPointer
  have d0 : readBuffer (chainStep oracle s0 c k 0) (L + 64) 32 =
      absorb oracle.compression salt (value.extractLsb' (512 * 0) 512) := by
    rw [w0, saltData, data0]
  unfold chainRun
  generalize chainStep oracle s0 c k 0 = t1 at d0 o0 x8a x23a ⊢
  have a1 := lane_addresses t1 c k hk slot heap x8a slotBound x23a
  rw [hL] at a1
  have w1 := chain_step_written oracle t1 c k 1 _ _ a1.2.1 a1.2.2.2.2.2.1
  have o1 := chain_step_outside oracle t1 c k 1 _ a1.2.2.2.2.2.1 (by omega)
  have x8b := (chain_step_register oracle t1 c k 1 hc hk (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 c k 1 hc hk (by decide) .x23 (by decide) (by decide)).trans x23a
  have d1 : readBuffer (chainStep oracle t1 c k 1) (L + 128) 32 =
      absorb oracle.compression (absorb oracle.compression salt (value.extractLsb' (512 * 0) 512))
        (value.extractLsb' (512 * 1) 512) := by
    rw [w1, d0, o0 _ 64 (by omega) (Or.inr (by omega)), data1]
  generalize chainStep oracle t1 c k 1 = t2 at d1 o1 x8b x23b ⊢
  have a2 := lane_addresses t2 c k hk slot heap x8b slotBound x23b
  rw [hL] at a2
  have w2 := chain_step_written oracle t2 c k 2 _ _ a2.2.2.1 a2.2.2.2.2.2.2.1
  have o2 := chain_step_outside oracle t2 c k 2 _ a2.2.2.2.2.2.2.1 (by omega)
  have x8c := (chain_step_register oracle t2 c k 2 hc hk (by decide) .x8 (by decide) (by decide)).trans x8b
  have x23c := (chain_step_register oracle t2 c k 2 hc hk (by decide) .x23 (by decide) (by decide)).trans x23b
  have d2 : readBuffer (chainStep oracle t2 c k 2) (L + 192) 32 =
      absorb oracle.compression (absorb oracle.compression (absorb oracle.compression salt
        (value.extractLsb' (512 * 0) 512)) (value.extractLsb' (512 * 1) 512))
        (value.extractLsb' (512 * 2) 512) := by
    rw [w2, d1, o1 _ 64 (by omega) (Or.inr (by omega)),
      o0 _ 64 (by omega) (Or.inr (by omega)), data2]
  generalize chainStep oracle t2 c k 2 = t3 at d2 o2 x8c x23c ⊢
  have a3 := lane_addresses t3 c k hk slot heap x8c slotBound x23c
  rw [hL] at a3
  have w3 := chain_step_written oracle t3 c k 3 _ _ a3.2.2.2.1 a3.2.2.2.2.2.2.2
  have b3 : L + 192 + 32 + 64 ≤ 2 ^ 64 := by omega
  have s2 : L + 192 + 32 + 64 ≤ L + 192 ∨ L + 192 + 32 ≤ L + 192 + 32 := Or.inr (Nat.le_refl _)
  have s1 : L + 192 + 32 + 64 ≤ L + 128 ∨ L + 128 + 32 ≤ L + 192 + 32 := Or.inr (by omega)
  have s0 : L + 192 + 32 + 64 ≤ L + 64 ∨ L + 64 + 32 ≤ L + 192 + 32 := Or.inr (by omega)
  have e3 : readBuffer t3 (L + 192 + 32) 64 = value.extractLsb' (512 * 3) 512 :=
    ((o2 _ 64 b3 s2).trans ((o1 _ 64 b3 s1).trans (o0 _ 64 b3 s0))).trans data3
  rewrite [w3, d2, e3]
  exact (leaf_digest_unfold _ _ _).symm

set_option maxHeartbeats 1600000 in
/-- The four in-place calls of lane `k` in chunk `c` preserve every byte range outside
the lane's chain region `[slot + 256*k + 64, slot + 256*k + 224)` and its heap slot. -/
theorem chain_run_outside (oracle : Oracle) (s0 : MachineState) (c k : Nat)
    (hc : c < 4) (hk : k < 8) (slot heap : Nat)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 2080 ≤ MEMORY_BYTES)
    (heapBound : heap + 384 * c + heapOffset k + 32 ≤ 2 ^ 64)
    (address count : Nat) (readBound : address + count ≤ 2 ^ 64)
    (outsideSlot : address + count ≤ slot + 256 * k + 64 ∨ slot + 256 * k + 224 ≤ address)
    (outsideHeap : address + count ≤ heap + 384 * c + heapOffset k ∨
      heap + 384 * c + heapOffset k + 32 ≤ address) :
    readBuffer (chainRun oracle s0 c k) address count = readBuffer s0 address count := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have a0 := lane_addresses s0 c k hk slot heap slotPointer slotBound heapPointer
  have o0 := chain_step_outside oracle s0 c k 0 _ a0.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8a := (chain_step_register oracle s0 c k 0 hc hk (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 c k 0 hc hk (by decide) .x23 (by decide) (by decide)).trans heapPointer
  unfold chainRun
  generalize chainStep oracle s0 c k 0 = t1 at o0 x8a x23a ⊢
  have a1 := lane_addresses t1 c k hk slot heap x8a slotBound x23a
  have o1 := chain_step_outside oracle t1 c k 1 _ a1.2.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8b := (chain_step_register oracle t1 c k 1 hc hk (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 c k 1 hc hk (by decide) .x23 (by decide) (by decide)).trans x23a
  generalize chainStep oracle t1 c k 1 = t2 at o1 x8b x23b ⊢
  have a2 := lane_addresses t2 c k hk slot heap x8b slotBound x23b
  have o2 := chain_step_outside oracle t2 c k 2 _ a2.2.2.2.2.2.2.1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8c := (chain_step_register oracle t2 c k 2 hc hk (by decide) .x8 (by decide) (by decide)).trans x8b
  have x23c := (chain_step_register oracle t2 c k 2 hc hk (by decide) .x23 (by decide) (by decide)).trans x23b
  generalize chainStep oracle t2 c k 2 = t3 at o2 x8c x23c ⊢
  have a3 := lane_addresses t3 c k hk slot heap x8c slotBound x23c
  have o3 := chain_step_outside oracle t3 c k 3 _ a3.2.2.2.2.2.2.2 heapBound
    address count readBound outsideHeap
  rw [o3, o2, o1, o0]

theorem word_add_literal (w : Word) (a b : Nat) (h : w = BitVec.ofNat 64 a) :
    w + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [h, BitVec.ofNat_add]

theorem heap_offset_chunk (c k : Nat) : heapOffset (8 * c + k) = 384 * c + heapOffset k := by
  unfold heapOffset; omega

/-- Hypotheses describing one 8-leaf chunk's memory before it runs. -/
structure ChunkLayout (state : MachineState) (c slot saltAddress heap : Nat) : Prop where
  hc : c < 4
  slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot
  saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress
  heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap
  r29 : state.getReg .x29 = 2048
  slotAligned : slot % 8 = 0
  saltAligned : saltAddress % 8 = 0
  heapAligned : heap % 8 = 0
  slotBound : slot + 2080 ≤ MEMORY_BYTES
  saltBound : saltAddress + 1024 ≤ MEMORY_BYTES
  heapBound : heap + 1536 ≤ MEMORY_BYTES
  saltSlot : saltAddress + 1024 ≤ slot ∨ slot + 2016 ≤ saltAddress
  heapSlot : heap + 1536 ≤ slot ∨ slot + 2080 ≤ heap
  saltHeap : saltAddress + 1024 ≤ heap ∨ heap + 1536 ≤ saltAddress

/-- One leaf preserves every digest outside `[slot + 256*k, slot + 256*k + 224)` and its heap slot. -/
theorem leaf_eval_preserves_digest (oracle : Oracle) (state : MachineState)
    (c k slot saltAddress heap address : Nat) (hk : k < 8)
    (layout : ChunkLayout state c slot saltAddress heap)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2 ^ 64)
    (outsideSlot : address + 32 ≤ slot + 256 * k ∨ slot + 256 * k + 224 ≤ address)
    (outsideHeap : address + 32 ≤ heap + 384 * c + heapOffset k ∨
      heap + 384 * c + heapOffset k + 32 ≤ address) :
    readBuffer (leafEval oracle state c k) address 32 = readBuffer state address 32 := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have hc := layout.hc
  have slotBound := layout.slotBound
  have heapBound := layout.heapBound
  have hkOff : heapOffset k + 32 ≤ 384 := by unfold heapOffset; omega
  have c8 := commit_copy_register state .x18 .x8 (256 * c + 32 * k) (256 * k) .x8 (by decide)
  have c23 := commit_copy_register state .x18 .x8 (256 * c + 32 * k) (256 * k) .x23 (by decide)
  unfold leafEval
  rw [chain_run_outside oracle _ c k hc hk slot heap (c8.trans layout.slotPointer)
      (c23.trans layout.heapPointer) slotBound (by omega) address 32 readBound
      (by rcases outsideSlot with h | h <;> omega) outsideHeap,
    commit_copy_preserves_digest state .x18 .x8 (256 * c + 32 * k) (256 * k) (slot + 256 * k)
      address (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      (word_add_literal _ slot (256 * k) layout.slotPointer) aligned (by omega) readBound
      (by rcases outsideSlot with h | h <;> omega)]

/-- One leaf stores its reference salted digest into `heap + 384*c + heapOffset k`. -/
theorem leaf_eval_digest (oracle : Oracle) (state : MachineState)
    (c k slot saltAddress heap : Nat) (hk : k < 8)
    (layout : ChunkLayout state c slot saltAddress heap) (value : Entry)
    (data : ∀ block < 4,
      readBuffer state (slot + 256 * k + 32 + 64 * block) 64 = value.extractLsb' (512 * block) 512) :
    readBuffer (leafEval oracle state c k) (heap + 384 * c + heapOffset k) 32 =
      leafDigest oracle.compression (readBuffer state (saltAddress + 256 * c + 32 * k) 32) value := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have hc := layout.hc
  have slotBound := layout.slotBound
  have saltBound := layout.saltBound
  have sl := layout.saltSlot
  have sla := layout.slotAligned
  have saa := layout.saltAligned
  have c8 := commit_copy_register state .x18 .x8 (256 * c + 32 * k) (256 * k) .x8 (by decide)
  have c23 := commit_copy_register state .x18 .x8 (256 * c + 32 * k) (256 * k) .x23 (by decide)
  have toPtr : commitCopyTo state .x8 (256 * k) = BitVec.ofNat 64 (slot + 256 * k) :=
    word_add_literal _ slot (256 * k) layout.slotPointer
  have fromPtr : commitCopyFrom state .x18 (256 * c + 32 * k) =
      BitVec.ofNat 64 (saltAddress + 256 * c + 32 * k) := by
    rw [commitCopyFrom, word_add_literal _ saltAddress (256 * c + 32 * k) layout.saltPointer]
    congr 1; omega
  have s0salt : readBuffer (commitCopyState state .x18 .x8 (256 * c + 32 * k) (256 * k))
      (slot + 256 * k) 32 = readBuffer state (saltAddress + 256 * c + 32 * k) 32 :=
    commit_copy_digest state .x18 .x8 (256 * c + 32 * k) (256 * k)
      (saltAddress + 256 * c + 32 * k) (slot + 256 * k)
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      fromPtr toPtr (by omega) (by omega) (by omega) (by omega)
      (by rcases sl with h | h <;> omega)
  have s0data (block : Nat) (hb : block < 4) :
      readBuffer (commitCopyState state .x18 .x8 (256 * c + 32 * k) (256 * k))
        (slot + 256 * k + 32 + 64 * block) 64 = value.extractLsb' (512 * block) 512 := by
    rw [commit_copy_preserves_block state .x18 .x8 (256 * c + 32 * k) (256 * k) (slot + 256 * k)
      _ (by decide) (by decide) (by omega) (by omega) (by omega) (by omega) toPtr
      (by omega) (by omega) (by omega) (Or.inr (by omega))]
    exact data block hb
  exact chain_run_digest oracle _ c k hc hk slot heap
    (readBuffer state (saltAddress + 256 * c + 32 * k) 32) value
    (c8.trans layout.slotPointer) (c23.trans layout.heapPointer) slotBound s0salt s0data

/-- Consecutive leaves in chunk `c` preserve every digest outside their slot ranges and heap slots. -/
theorem chunk_leaves_from_preserves_digest (oracle : Oracle) (state : MachineState)
    (c start remaining slot saltAddress heap address : Nat) (hbound : start + remaining ≤ 8)
    (layout : ChunkLayout state c slot saltAddress heap)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2 ^ 64)
    (outsideSlot : address + 32 ≤ slot + 256 * start ∨ slot + 256 * (start + remaining) ≤ address)
    (outsideHeap : ∀ k, start ≤ k → k < start + remaining →
      address + 32 ≤ heap + 384 * c + heapOffset k ∨
      heap + 384 * c + heapOffset k + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (chunkLeavesFrom state c start remaining)).1 address 32 =
      readBuffer state address 32 := by
  induction remaining generalizing state start with
  | zero => rw [chunkLeavesFrom, check_evaluation_pure]
  | succ remaining ih =>
    rw [chunkLeavesFrom, check_evaluation_bind, leaf_run_evaluation]
    dsimp only
    let next := leafEval oracle state c start
    have nextLayout : ChunkLayout next c slot saltAddress heap :=
      ⟨layout.hc,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x8
         (by decide) (by decide) (by decide)).trans layout.slotPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x18
         (by decide) (by decide) (by decide)).trans layout.saltPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x23
         (by decide) (by decide) (by decide)).trans layout.heapPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x29
         (by decide) (by decide) (by decide)).trans layout.r29,
       layout.slotAligned, layout.saltAligned, layout.heapAligned,
       layout.slotBound, layout.saltBound, layout.heapBound,
       layout.saltSlot, layout.heapSlot, layout.saltHeap⟩
    rw [ih next (start + 1) (by omega) nextLayout
        (by rcases outsideSlot with h | h <;> omega)
        (fun k hk1 hk2 => outsideHeap k (by omega) (by omega))]
    exact leaf_eval_preserves_digest oracle state c start slot saltAddress heap address
      (by omega) layout aligned readBound (by rcases outsideSlot with h | h <;> omega)
      (outsideHeap start (by omega) (by omega))

/-- Consecutive leaves in chunk `c` compute and retain every salted leaf digest. -/
theorem chunk_leaves_from_digests (oracle : Oracle) (state : MachineState)
    (c start remaining slot saltAddress heap : Nat) (hbound : start + remaining ≤ 8)
    (layout : ChunkLayout state c slot saltAddress heap) (value : Nat → Entry)
    (data : ∀ k, start ≤ k → k < start + remaining → ∀ block < 4,
      readBuffer state (slot + 256 * k + 32 + 64 * block) 64 =
        (value k).extractLsb' (512 * block) 512) :
    ∀ k, start ≤ k → k < start + remaining →
      readBuffer (checkEvaluation oracle (chunkLeavesFrom state c start remaining)).1
        (heap + 384 * c + heapOffset k) 32 =
        leafDigest oracle.compression (readBuffer state (saltAddress + 256 * c + 32 * k) 32)
          (value k) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction remaining generalizing state start with
  | zero => intro k hk1 hk2; omega
  | succ remaining ih =>
    have hc := layout.hc
    have slotBound := layout.slotBound
    have saltBound := layout.saltBound
    have heapBound := layout.heapBound
    have sl := layout.saltSlot
    have hs := layout.heapSlot
    have sh := layout.saltHeap
    have sla := layout.slotAligned
    have saa := layout.saltAligned
    have hea := layout.heapAligned
    rw [chunkLeavesFrom, check_evaluation_bind, leaf_run_evaluation]
    dsimp only
    let next := leafEval oracle state c start
    have nextLayout : ChunkLayout next c slot saltAddress heap :=
      ⟨layout.hc,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x8
         (by decide) (by decide) (by decide)).trans layout.slotPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x18
         (by decide) (by decide) (by decide)).trans layout.saltPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x23
         (by decide) (by decide) (by decide)).trans layout.heapPointer,
       (leaf_eval_register oracle state c start layout.hc (by omega) .x29
         (by decide) (by decide) (by decide)).trans layout.r29,
       layout.slotAligned, layout.saltAligned, layout.heapAligned,
       layout.slotBound, layout.saltBound, layout.heapBound,
       layout.saltSlot, layout.heapSlot, layout.saltHeap⟩
    have nextData : ∀ k, start + 1 ≤ k → k < start + 1 + remaining → ∀ block < 4,
        readBuffer next (slot + 256 * k + 32 + 64 * block) 64 =
          (value k).extractLsb' (512 * block) 512 := by
      intro k hk1 hk2 block hb
      have hkOff : heapOffset start + 32 ≤ 384 := by unfold heapOffset; omega
      rw [read_compression_halves _ _ (by omega),
        leaf_eval_preserves_digest oracle state c start slot saltAddress heap
          (slot + 256 * k + 32 + 64 * block + 32) (by omega) layout (by omega) (by omega)
          (Or.inr (by omega)) (by rcases hs with h | h <;> omega),
        leaf_eval_preserves_digest oracle state c start slot saltAddress heap
          (slot + 256 * k + 32 + 64 * block) (by omega) layout (by omega) (by omega)
          (Or.inr (by omega)) (by rcases hs with h | h <;> omega),
        ← read_compression_halves _ _ (by omega)]
      exact data k (by omega) (by omega) block hb
    intro k hk1 hk2
    by_cases hcur : k = start
    · subst k
      have hkOff : heapOffset start + 32 ≤ 384 := by unfold heapOffset; omega
      have hkAlign : heapOffset start % 8 = 0 := heap_offset_aligned start
      rw [chunk_leaves_from_preserves_digest oracle next c (start + 1) remaining slot saltAddress
          heap (heap + 384 * c + heapOffset start) (by omega) nextLayout (by omega) (by omega)
          (by rcases hs with h | h <;> omega)
          (fun j hj1 _ => by
            have := heap_offset_disjoint start j (by omega)
            omega)]
      exact leaf_eval_digest oracle state c start slot saltAddress heap (by omega) layout
        (value start) (data start (by omega) (by omega))
    · have hkOff : heapOffset start + 32 ≤ 384 := by unfold heapOffset; omega
      have rest := ih next (start + 1) (by omega) nextLayout nextData k (by omega) (by omega)
      rw [rest, leaf_eval_preserves_digest oracle state c start slot saltAddress heap
        (saltAddress + 256 * c + 32 * k) (by omega) layout (by omega) (by omega)
        (by rcases sl with h | h <;> omega) (by rcases sh with h | h <;> omega)]

/-- Hypotheses describing one 32-leaf iteration's memory before it runs. -/
structure PairLayout (state : MachineState) (slot saltAddress heap : Nat) : Prop where
  slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot
  saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress
  heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap
  r29 : state.getReg .x29 = 2048
  slotAligned : slot % 8 = 0
  saltAligned : saltAddress % 8 = 0
  heapAligned : heap % 8 = 0
  slotBound : slot + 8224 ≤ MEMORY_BYTES
  saltBound : saltAddress + 1024 ≤ MEMORY_BYTES
  heapBound : heap + 1536 ≤ MEMORY_BYTES
  saltSlot : saltAddress + 1024 ≤ slot ∨ slot + 8192 ≤ saltAddress
  heapSlot : heap + 1536 ≤ slot ∨ slot + 8224 ≤ heap
  saltHeap : saltAddress + 1024 ≤ heap ∨ heap + 1536 ≤ saltAddress

attribute [local irreducible] checkEvaluation leafRun laneRun chunkLeavesFrom

private theorem chunk_advance_mem (s : MachineState) : (chunkAdvanceState s).mem = s.mem := by
  cases s; rfl

private theorem commit_position_next_mem (s : MachineState) :
    (commitPositionNextState s).mem = s.mem := by
  cases s; rfl

private theorem chunk_run_eval_mem (oracle : Oracle) (state : MachineState) (c : Nat) :
    (checkEvaluation oracle (chunkRun state c)).1.mem =
      (checkEvaluation oracle (chunkLeavesFrom state c 0 8)).1.mem := by
  rw [chunkRun, check_evaluation_bind]
  generalize checkEvaluation oracle (chunkLeavesFrom state c 0 8) = res
  rcases res with ⟨hashed, calls⟩
  simp only [check_evaluation_pure]
  exact chunk_advance_mem hashed

private theorem chunk_run_eval_regs (oracle : Oracle) (state : MachineState) (c : Nat) (hc : c < 4)
    (r29 : state.getReg .x29 = 2048) :
    (checkEvaluation oracle (chunkRun state c)).1.getReg .x8 = state.getReg .x8 + 2048 ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x8 → reg ≠ .x10 → reg ≠ .x12 →
      (checkEvaluation oracle (chunkRun state c)).1.getReg reg = state.getReg reg := by
  have regs := chunk_run_registers state _ c hc (check_evaluation_support oracle (chunkRun state c))
  exact ⟨by rw [regs.1, r29], regs.2⟩

theorem iter_chunks_from_preserves_digest (oracle : Oracle) (state : MachineState)
    (start remaining slot saltAddress heap address : Nat) (hbound : start + remaining ≤ 4)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (r29 : state.getReg .x29 = 2048)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (slotBound : slot + 32 + 2048 * remaining ≤ MEMORY_BYTES)
    (saltBound : saltAddress + 1024 ≤ MEMORY_BYTES)
    (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (saltSlot : saltAddress + 1024 ≤ slot ∨ slot + 2048 * remaining ≤ saltAddress)
    (heapSlot : heap + 1536 ≤ slot ∨ slot + 32 + 2048 * remaining ≤ heap)
    (saltHeap : saltAddress + 1024 ≤ heap ∨ heap + 1536 ≤ saltAddress)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2 ^ 64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 2048 * remaining ≤ address)
    (outsideHeap : ∀ i, 8 * start ≤ i → i < 8 * (start + remaining) →
      address + 32 ≤ heap + heapOffset i ∨ heap + heapOffset i + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (iterChunksFrom state start remaining)).1 address 32 =
      readBuffer state address 32 := by
  induction remaining generalizing state start slot with
  | zero => rw [iterChunksFrom, check_evaluation_pure]
  | succ remaining ih =>
    rw [iterChunksFrom, check_evaluation_bind]
    dsimp only
    let next := (checkEvaluation oracle (chunkRun state start)).1
    have regs := chunk_run_eval_regs oracle state start (by omega) r29
    have nextSlot : next.getReg .x8 = BitVec.ofNat 64 (slot + 2048) := by
      rw [regs.1]; exact word_add_literal _ slot 2048 slotPointer
    have chunkLayout : ChunkLayout state start slot saltAddress heap :=
      ⟨by omega, slotPointer, saltPointer, heapPointer, r29, slotAligned, saltAligned, heapAligned,
       by omega, saltBound, heapBound, by rcases saltSlot with h | h <;> omega,
       by rcases heapSlot with h | h <;> omega, saltHeap⟩
    rw [ih next (start + 1) (slot + 2048) (by omega) nextSlot
        ((regs.2 .x18 (by decide) (by decide) (by decide) (by decide)).trans saltPointer)
        ((regs.2 .x23 (by decide) (by decide) (by decide) (by decide)).trans heapPointer)
        ((regs.2 .x29 (by decide) (by decide) (by decide) (by decide)).trans r29)
        (by omega) (by omega) (by rcases saltSlot with h | h <;> omega)
        (by rcases heapSlot with h | h <;> omega)
        (by rcases outsideSlot with h | h <;> omega)
        (fun i hi1 hi2 => outsideHeap i (by omega) (by omega))]
    rw [read_buffer_memory_congr _ _ (chunk_run_eval_mem oracle state start)]
    exact chunk_leaves_from_preserves_digest oracle state start 0 8 slot saltAddress heap address
      (by decide) chunkLayout aligned readBound (by rcases outsideSlot with h | h <;> omega)
      (fun k _ hk => by
        have h := outsideHeap (8 * start + k) (by omega) (by omega)
        rw [heap_offset_chunk] at h
        simpa [Nat.add_assoc] using h)

theorem iter_chunks_from_digests (oracle : Oracle) (state : MachineState)
    (start remaining slot saltAddress heap : Nat) (hbound : start + remaining ≤ 4)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (r29 : state.getReg .x29 = 2048)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0) (heapAligned : heap % 8 = 0)
    (slotBound : slot + 32 + 2048 * remaining ≤ MEMORY_BYTES)
    (saltBound : saltAddress + 1024 ≤ MEMORY_BYTES)
    (heapBound : heap + 1536 ≤ MEMORY_BYTES)
    (saltSlot : saltAddress + 1024 ≤ slot ∨ slot + 2048 * remaining ≤ saltAddress)
    (heapSlot : heap + 1536 ≤ slot ∨ slot + 32 + 2048 * remaining ≤ heap)
    (saltHeap : saltAddress + 1024 ≤ heap ∨ heap + 1536 ≤ saltAddress)
    (value : Nat → Entry)
    (data : ∀ i < 8 * remaining, ∀ block < 4,
      readBuffer state (slot + 256 * i + 32 + 64 * block) 64 =
        (value (8 * start + i)).extractLsb' (512 * block) 512) :
    ∀ i, 8 * start ≤ i → i < 8 * (start + remaining) →
      readBuffer (checkEvaluation oracle (iterChunksFrom state start remaining)).1
        (heap + heapOffset i) 32 =
        leafDigest oracle.compression (readBuffer state (saltAddress + 32 * i) 32) (value i) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction remaining generalizing state start slot with
  | zero => intro i hi1 hi2; omega
  | succ remaining ih =>
    rw [iterChunksFrom, check_evaluation_bind]
    dsimp only
    let next := (checkEvaluation oracle (chunkRun state start)).1
    have regs := chunk_run_eval_regs oracle state start (by omega) r29
    have nextSlot : next.getReg .x8 = BitVec.ofNat 64 (slot + 2048) := by
      rw [regs.1]; exact word_add_literal _ slot 2048 slotPointer
    have chunkLayout : ChunkLayout state start slot saltAddress heap :=
      ⟨by omega, slotPointer, saltPointer, heapPointer, r29, slotAligned, saltAligned, heapAligned,
       by omega, saltBound, heapBound, by rcases saltSlot with h | h <;> omega,
       by rcases heapSlot with h | h <;> omega, saltHeap⟩
    have nextData : ∀ i < 8 * remaining, ∀ block < 4,
        readBuffer next (slot + 2048 + 256 * i + 32 + 64 * block) 64 =
          (value (8 * (start + 1) + i)).extractLsb' (512 * block) 512 := by
      intro i hi block hb
      rw [read_buffer_memory_congr _ _ (chunk_run_eval_mem oracle state start),
        read_compression_halves _ _ (by omega),
        chunk_leaves_from_preserves_digest oracle state start 0 8 slot saltAddress heap
          (slot + 2048 + 256 * i + 32 + 64 * block + 32) (by decide) chunkLayout
          (by omega) (by omega) (Or.inr (by omega))
          (fun k _ hk => by
            have hkOff : heapOffset k + 32 ≤ 384 := by unfold heapOffset; omega
            rcases heapSlot with h | h <;> omega),
        chunk_leaves_from_preserves_digest oracle state start 0 8 slot saltAddress heap
          (slot + 2048 + 256 * i + 32 + 64 * block) (by decide) chunkLayout
          (by omega) (by omega) (Or.inr (by omega))
          (fun k _ hk => by
            have hkOff : heapOffset k + 32 ≤ 384 := by unfold heapOffset; omega
            rcases heapSlot with h | h <;> omega),
        ← read_compression_halves _ _ (by omega)]
      rw [show slot + 2048 + 256 * i + 32 + 64 * block = slot + 256 * (i + 8) + 32 + 64 * block by omega,
        show 8 * (start + 1) + i = 8 * start + (i + 8) by omega]
      exact data (i + 8) (by omega) block hb
    intro i hi1 hi2
    by_cases hlow : i < 8 * (start + 1)
    · obtain ⟨k, rfl⟩ : ∃ k, i = 8 * start + k := ⟨i - 8 * start, by omega⟩
      have hk : k < 8 := by omega
      have hkOff : heapOffset (8 * start + k) + 32 ≤ 1536 := by unfold heapOffset; omega
      have hkAlign : heapOffset (8 * start + k) % 8 = 0 := heap_offset_aligned _
      rw [iter_chunks_from_preserves_digest oracle next (start + 1) remaining (slot + 2048)
          saltAddress heap (heap + heapOffset (8 * start + k)) (by omega) nextSlot
          ((regs.2 .x18 (by decide) (by decide) (by decide) (by decide)).trans saltPointer)
          ((regs.2 .x23 (by decide) (by decide) (by decide) (by decide)).trans heapPointer)
          ((regs.2 .x29 (by decide) (by decide) (by decide) (by decide)).trans r29)
          (by omega) saltAligned heapAligned (by omega) saltBound heapBound
          (by rcases saltSlot with h | h <;> omega) (by rcases heapSlot with h | h <;> omega)
          saltHeap (by omega) (by omega) (by rcases heapSlot with h | h <;> omega)
          (fun j hj1 _ => by
            have := heap_offset_disjoint (8 * start + k) j (by omega)
            omega)]
      rw [read_buffer_memory_congr _ _ (chunk_run_eval_mem oracle state start),
        heap_offset_chunk, ← Nat.add_assoc]
      have hchunk := chunk_leaves_from_digests oracle state start 0 8 slot saltAddress heap
        (by decide) chunkLayout (fun m => value (8 * start + m))
        (fun m _ hm block hb => data m (by omega) block hb) k (by omega) hk
      rw [hchunk, show saltAddress + 256 * start + 32 * k = saltAddress + 32 * (8 * start + k) by omega]
    · have rest := ih next (start + 1) (slot + 2048) (by omega) nextSlot
        ((regs.2 .x18 (by decide) (by decide) (by decide) (by decide)).trans saltPointer)
        ((regs.2 .x23 (by decide) (by decide) (by decide) (by decide)).trans heapPointer)
        ((regs.2 .x29 (by decide) (by decide) (by decide) (by decide)).trans r29)
        (by omega) (by omega) (by rcases saltSlot with h | h <;> omega)
        (by rcases heapSlot with h | h <;> omega) nextData i (by omega) (by omega)
      rw [rest, read_buffer_memory_congr _ _ (chunk_run_eval_mem oracle state start),
        chunk_leaves_from_preserves_digest oracle state start 0 8 slot saltAddress heap
          (saltAddress + 32 * i) (by decide) chunkLayout (by omega) (by omega)
          (by rcases saltSlot with h | h <;> omega)
          (fun k _ hk => by
            have hkOff : heapOffset k + 32 ≤ 384 := by unfold heapOffset; omega
            rcases saltHeap with h | h <;> omega)]

private theorem commit_position_eval_mem (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (commitPositionRun state)).1.mem =
      (checkEvaluation oracle (iterChunksFrom state 0 4)).1.mem := by
  rw [commitPositionRun, check_evaluation_bind]
  generalize checkEvaluation oracle (iterChunksFrom state 0 4) = res
  rcases res with ⟨chunks, calls⟩
  simp only [check_evaluation_pure]
  exact commit_position_next_mem chunks

/-- One 32-leaf iteration preserves every digest outside `[slot, slot + 8192)` and outside
its 32 written heap slots (in particular, all 16 zero gaps inside `[heap, heap + 1536)`). -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap address : Nat) (layout : PairLayout state slot saltAddress heap)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2 ^ 64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 8192 ≤ address)
    (outsideHeap : ∀ i < 32,
      address + 32 ≤ heap + heapOffset i ∨ heap + heapOffset i + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 address 32 =
      readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_position_eval_mem oracle state)]
  exact iter_chunks_from_preserves_digest oracle state 0 4 slot saltAddress heap address (by decide)
    layout.slotPointer layout.saltPointer layout.heapPointer layout.r29
    layout.slotAligned layout.saltAligned layout.heapAligned
    (by have := layout.slotBound; omega) layout.saltBound layout.heapBound
    (by rcases layout.saltSlot with h | h; exact Or.inl h; exact Or.inr (by omega))
    (by rcases layout.heapSlot with h | h; exact Or.inl h; exact Or.inr (by omega))
    layout.saltHeap aligned readBound
    (by rcases outsideSlot with h | h; exact Or.inl h; exact Or.inr (by omega))
    (fun i _ hi => outsideHeap i (by omega))

/-- One 32-leaf iteration stores, for each `i < 32`, the salted leaf digest of leaf `i`
in `heap + heapOffset i`. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat) (layout : PairLayout state slot saltAddress heap)
    (value : Nat → Entry)
    (data : ∀ i < 32, ∀ block < 4,
      readBuffer state (slot + 256 * i + 32 + 64 * block) 64 =
        (value i).extractLsb' (512 * block) 512) :
    ∀ i < 32, readBuffer (checkEvaluation oracle (commitPositionRun state)).1
        (heap + heapOffset i) 32 =
      leafDigest oracle.compression (readBuffer state (saltAddress + 32 * i) 32) (value i) := by
  intro i hi
  rw [read_buffer_memory_congr _ _ (commit_position_eval_mem oracle state)]
  exact iter_chunks_from_digests oracle state 0 4 slot saltAddress heap (by decide)
    layout.slotPointer layout.saltPointer layout.heapPointer layout.r29
    layout.slotAligned layout.saltAligned layout.heapAligned
    (by have := layout.slotBound; omega) layout.saltBound layout.heapBound
    (by rcases layout.saltSlot with h | h; exact Or.inl h; exact Or.inr (by omega))
    (by rcases layout.heapSlot with h | h; exact Or.inl h; exact Or.inr (by omega))
    layout.saltHeap value (fun m hm block hb => by simpa using data m (by omega) block hb)
    i (by omega) (by omega)

end CommitGolfCandidate
