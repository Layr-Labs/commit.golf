import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading, in-place leaf chain and heap write of the actual commitment leaf
iteration, refined to the reference salted leaf digest. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

set_option maxRecDepth 20000

/-- Commitment's two digest copies use the same load/store sequence as opening.
Only the source and destination registers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 43 ∨ start = 92) :
    (commitCopyState state start).mem =
      (openingCopyState
        ((state.setReg .x23 (if start = 43 then state.getReg .x18 else state.getReg .x9+32)).setReg .x25
          (if start = 43 then state.getReg .x8 else state.getReg .x26))).mem := by
  rcases location with rfl | rfl <;>
    rw [commit_copy_expansion, opening_copy_expansion] <;>
    simp [List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

/-- Copy a complete digest from one of the two commitment copy sites. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (location : start = 43 ∨ start = 92)
    (sourcePointer : (if start = 43 then state.getReg .x18 else state.getReg .x9+32) = BitVec.ofNat 64 source)
    (destinationPointer : (if start = 43 then state.getReg .x8 else state.getReg .x26) =
      BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (commitCopyState state start) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_digest _ source destination (by simpa [MachineState.getReg, MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer) sourceAligned destinationAligned
    sourceBound destinationBound separate]
  rfl

/-- The commitment copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (location : start = 43 ∨ start = 92)
    (destinationPointer : (if start = 43 then state.getReg .x8 else state.getReg .x26) =
      BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_preserves_digest _ destination address
    (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer)
    aligned destinationBound readBound separate]
  rfl

/-- The 64-byte oracle input of in-place call `j`. -/
def chainInput (state : MachineState) (j : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (32*j)).toNat 64

/-- One in-place call evaluated with a fixed oracle. -/
def chainAnswer (oracle : Oracle) (state : MachineState) (j : Nat) : BitVec 256 :=
  oracle.compression (chainInput state j)

/-- One in-place call evaluated with a fixed oracle. -/
def chainStep (oracle : Oracle) (state : MachineState) (j : Nat) : MachineState :=
  chainCallState state j (chainAnswer oracle state j)

/-- The eight in-place calls of one leaf. -/
def chainRun (oracle : Oracle) (state : MachineState) : MachineState :=
  (chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle state 0) 1) 2) 3) 4) 5) 6) 7)

/-- A complete leaf iteration under a fixed oracle: salt copy, eight calls, advance. -/
theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      (commitPositionNextState (chainRun oracle (commitCopyState state 43)), 8) := by
  rw [commitPositionRun]
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem chain_step_register (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 8)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainStep oracle state j).getReg reg = state.getReg reg :=
  chain_call_register state j hj _ reg n10 n12

theorem chain_output_slot (state : MachineState) (j : Nat) (hj : j < 7) (slot out : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot) (hout : out = slot + 32*(j+1)) :
    chainOutput state j = BitVec.ofNat 64 out := by
  unfold chainOutput
  rw [if_neg (by omega), slotPointer, ← BitVec.ofNat_add, hout,
    show slot + (32*j+32) = slot + 32*(j+1) by omega]

theorem chain_output_heap (state : MachineState) (heap : Nat)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap) :
    chainOutput state 7 = BitVec.ofNat 64 heap := by
  unfold chainOutput
  rw [if_pos rfl, heapPointer]

/-- Call `j` writes its reply at its output slot. -/
theorem chain_call_written (state : MachineState) (j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state j = BitVec.ofNat 64 out) :
    readBuffer (chainCallState state j answer) out 32 = answer := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state j answer), hout]
  have written := write_bits_digest state out 0 answer (by decide) (by decide)
  simpa using written

/-- Call `j` changes no byte outside its 32-byte output slot. -/
theorem chain_call_outside (state : MachineState) (j : Nat) (answer : BitVec 256)
    (out : Nat) (hout : chainOutput state j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainCallState state j answer) address count = readBuffer state address count := by
  rw [read_buffer_memory_congr _ _ (chain_call_memory state j answer), hout]
  exact write_bits_read_outside state answer out address count (by simpa using outBound) readBound
    (by simpa using separate)

/-- The compression read splits even for a symbolic byte address. Alignment of actual
machine calls is established separately by `chain_call_valid`. -/
theorem read_chain_halves (state : MachineState) (address : Nat) :
    readBuffer state address 64 =
      readBuffer state (address + 32) 32 ++ readBuffer state address 32 :=
  read_compression_halves_unaligned state address

/-- The 64-byte input of call `j` is its chaining value followed by its message block. -/
theorem chain_query_split (state : MachineState) (slot j : Nat) :
    readBuffer state (slot + 32*j) 64 =
      (readBuffer state (slot + 32 + 32*j) 32) ++ (readBuffer state (slot + 32*j) 32) := by
  rw [read_chain_halves, show slot + 32*j + 32 = slot + 32 + 32*j by omega]

theorem chain_input_split (state : MachineState) (j : Nat) (hj : j < 8)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) :
    chainInput state j =
      (readBuffer state (slot + 32 + 32*j) 32) ++ (readBuffer state (slot + 32*j) 32) := by
  unfold chainInput
  rw [chain_source_nat state j hj slot slotPointer slotBound]
  exact chain_query_split state slot j

theorem chain_step_written (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 8)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (out : Nat) (hout : chainOutput state j = BitVec.ofNat 64 out) :
    readBuffer (chainStep oracle state j) out 32 =
      combine oracle.compression (readBuffer state (slot + 32*j) 32)
        (readBuffer state (slot + 32 + 32*j) 32) := by
  unfold chainStep
  rw [chain_call_written state j _ out hout]
  unfold chainAnswer
  rw [chain_input_split state j hj slot slotPointer slotBound]
  rfl

theorem chain_step_outside (oracle : Oracle) (state : MachineState) (j : Nat)
    (out : Nat) (hout : chainOutput state j = BitVec.ofNat 64 out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (chainStep oracle state j) address count = readBuffer state address count :=
  chain_call_outside state j _ out hout outBound address count readBound separate

theorem chain_memory_bound (slot : Nat) (slotBound : slot + 288 ≤ MEMORY_BYTES) :
    slot + 288 ≤ 2^64 := by
  have : MEMORY_BYTES = 2^36 := rfl
  omega

/-- Eight in-place calls, starting from a slot holding the salt followed by the eight
message blocks, write the reference salted leaf digest into the heap slot. -/
theorem chain_run_digest (oracle : Oracle) (s0 : MachineState) (slot heap : Nat)
    (salt : Digest) (value : Entry)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (saltData : readBuffer s0 slot 32 = salt)
    (data : ∀ block < 8, readBuffer s0 (slot+32+32*block) 32 = value.extractLsb' (256*block) 256) :
    readBuffer (chainRun oracle s0) heap 32 = leafDigest oracle.compression salt value := by
  have big := chain_memory_bound slot slotBound
  -- call 0
  have p0 : chainOutput s0 0 = BitVec.ofNat 64 (slot + 32*1) :=
    chain_output_slot s0 0 (by decide) slot _ slotPointer (by omega)
  have w0 := chain_step_written oracle s0 0 (by decide) slot slotPointer slotBound _ p0
  have o0 := chain_step_outside oracle s0 0 _ p0 (by omega)
  have x81 := (chain_step_register oracle s0 0 (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x231 := (chain_step_register oracle s0 0 (by decide) .x23 (by decide) (by decide)).trans heapPointer
  have d0 : readBuffer (chainStep oracle s0 0) (slot + 32*1) 32 =
      (combine oracle.compression salt (value.extractLsb' (256*0) 256)) := by
    rw [w0, show slot + 32*0 = slot by omega, saltData, data 0 (by decide)]
  unfold chainRun
  generalize chainStep oracle s0 0 = s1 at d0 o0 x81 x231 ⊢
  -- call 1
  have p1 : chainOutput s1 1 = BitVec.ofNat 64 (slot + 32*2) :=
    chain_output_slot s1 1 (by decide) slot _ x81 (by omega)
  have w1 := chain_step_written oracle s1 1 (by decide) slot x81 slotBound _ p1
  have o1 := chain_step_outside oracle s1 1 _ p1 (by omega)
  have x82 := (chain_step_register oracle s1 1 (by decide) .x8 (by decide) (by decide)).trans x81
  have x232 := (chain_step_register oracle s1 1 (by decide) .x23 (by decide) (by decide)).trans x231
  have d1 : readBuffer (chainStep oracle s1 1) (slot + 32*2) 32 =
      (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) := by
    rw [w1, d0, o0 _ 32 (by omega) (Or.inr (by omega)), data 1 (by decide)]
  generalize chainStep oracle s1 1 = s2 at d1 o1 x82 x232 ⊢
  -- call 2
  have p2 : chainOutput s2 2 = BitVec.ofNat 64 (slot + 32*3) :=
    chain_output_slot s2 2 (by decide) slot _ x82 (by omega)
  have w2 := chain_step_written oracle s2 2 (by decide) slot x82 slotBound _ p2
  have o2 := chain_step_outside oracle s2 2 _ p2 (by omega)
  have x83 := (chain_step_register oracle s2 2 (by decide) .x8 (by decide) (by decide)).trans x82
  have x233 := (chain_step_register oracle s2 2 (by decide) .x23 (by decide) (by decide)).trans x232
  have d2 : readBuffer (chainStep oracle s2 2) (slot + 32*3) 32 =
      (combine oracle.compression (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) (value.extractLsb' (256*2) 256)) := by
    rw [w2, d1, o1 _ 32 (by omega) (Or.inr (by omega)), o0 _ 32 (by omega) (Or.inr (by omega)), data 2 (by decide)]
  generalize chainStep oracle s2 2 = s3 at d2 o2 x83 x233 ⊢
  -- call 3
  have p3 : chainOutput s3 3 = BitVec.ofNat 64 (slot + 32*4) :=
    chain_output_slot s3 3 (by decide) slot _ x83 (by omega)
  have w3 := chain_step_written oracle s3 3 (by decide) slot x83 slotBound _ p3
  have o3 := chain_step_outside oracle s3 3 _ p3 (by omega)
  have x84 := (chain_step_register oracle s3 3 (by decide) .x8 (by decide) (by decide)).trans x83
  have x234 := (chain_step_register oracle s3 3 (by decide) .x23 (by decide) (by decide)).trans x233
  have d3 : readBuffer (chainStep oracle s3 3) (slot + 32*4) 32 =
      (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) (value.extractLsb' (256*2) 256)) (value.extractLsb' (256*3) 256)) := by
    rw [w3, d2, o2 _ 32 (by omega) (Or.inr (by omega)), o1 _ 32 (by omega) (Or.inr (by omega)), o0 _ 32 (by omega) (Or.inr (by omega)), data 3 (by decide)]
  generalize chainStep oracle s3 3 = s4 at d3 o3 x84 x234 ⊢
  -- call 4
  have p4 : chainOutput s4 4 = BitVec.ofNat 64 (slot + 32*5) :=
    chain_output_slot s4 4 (by decide) slot _ x84 (by omega)
  have w4 := chain_step_written oracle s4 4 (by decide) slot x84 slotBound _ p4
  have o4 := chain_step_outside oracle s4 4 _ p4 (by omega)
  have x85 := (chain_step_register oracle s4 4 (by decide) .x8 (by decide) (by decide)).trans x84
  have x235 := (chain_step_register oracle s4 4 (by decide) .x23 (by decide) (by decide)).trans x234
  have d4 : readBuffer (chainStep oracle s4 4) (slot + 32*5) 32 =
      (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) (value.extractLsb' (256*2) 256)) (value.extractLsb' (256*3) 256)) (value.extractLsb' (256*4) 256)) := by
    rw [w4, d3, o3 _ 32 (by omega) (Or.inr (by omega)), o2 _ 32 (by omega) (Or.inr (by omega)), o1 _ 32 (by omega) (Or.inr (by omega)), o0 _ 32 (by omega) (Or.inr (by omega)), data 4 (by decide)]
  generalize chainStep oracle s4 4 = s5 at d4 o4 x85 x235 ⊢
  -- call 5
  have p5 : chainOutput s5 5 = BitVec.ofNat 64 (slot + 32*6) :=
    chain_output_slot s5 5 (by decide) slot _ x85 (by omega)
  have w5 := chain_step_written oracle s5 5 (by decide) slot x85 slotBound _ p5
  have o5 := chain_step_outside oracle s5 5 _ p5 (by omega)
  have x86 := (chain_step_register oracle s5 5 (by decide) .x8 (by decide) (by decide)).trans x85
  have x236 := (chain_step_register oracle s5 5 (by decide) .x23 (by decide) (by decide)).trans x235
  have d5 : readBuffer (chainStep oracle s5 5) (slot + 32*6) 32 =
      (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) (value.extractLsb' (256*2) 256)) (value.extractLsb' (256*3) 256)) (value.extractLsb' (256*4) 256)) (value.extractLsb' (256*5) 256)) := by
    rw [w5, d4, o4 _ 32 (by omega) (Or.inr (by omega)), o3 _ 32 (by omega) (Or.inr (by omega)), o2 _ 32 (by omega) (Or.inr (by omega)), o1 _ 32 (by omega) (Or.inr (by omega)), o0 _ 32 (by omega) (Or.inr (by omega)), data 5 (by decide)]
  generalize chainStep oracle s5 5 = s6 at d5 o5 x86 x236 ⊢
  -- call 6
  have p6 : chainOutput s6 6 = BitVec.ofNat 64 (slot + 32*7) :=
    chain_output_slot s6 6 (by decide) slot _ x86 (by omega)
  have w6 := chain_step_written oracle s6 6 (by decide) slot x86 slotBound _ p6
  have o6 := chain_step_outside oracle s6 6 _ p6 (by omega)
  have x87 := (chain_step_register oracle s6 6 (by decide) .x8 (by decide) (by decide)).trans x86
  have x237 := (chain_step_register oracle s6 6 (by decide) .x23 (by decide) (by decide)).trans x236
  have d6 : readBuffer (chainStep oracle s6 6) (slot + 32*7) 32 =
      (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression (combine oracle.compression salt (value.extractLsb' (256*0) 256)) (value.extractLsb' (256*1) 256)) (value.extractLsb' (256*2) 256)) (value.extractLsb' (256*3) 256)) (value.extractLsb' (256*4) 256)) (value.extractLsb' (256*5) 256)) (value.extractLsb' (256*6) 256)) := by
    rw [w6, d5, o5 _ 32 (by omega) (Or.inr (by omega)), o4 _ 32 (by omega) (Or.inr (by omega)), o3 _ 32 (by omega) (Or.inr (by omega)), o2 _ 32 (by omega) (Or.inr (by omega)), o1 _ 32 (by omega) (Or.inr (by omega)), o0 _ 32 (by omega) (Or.inr (by omega)), data 6 (by decide)]
  generalize chainStep oracle s6 6 = s7 at d6 o6 x87 x237 ⊢
  -- call 7
  have w7 := chain_step_written oracle s7 7 (by decide) slot x87 slotBound heap
    (chain_output_heap s7 heap x237)
  rw [w7, d6, o6 _ 32 (by omega) (Or.inr (by omega)),
    o5 _ 32 (by omega) (Or.inr (by omega)),
    o4 _ 32 (by omega) (Or.inr (by omega)),
    o3 _ 32 (by omega) (Or.inr (by omega)),
    o2 _ 32 (by omega) (Or.inr (by omega)),
    o1 _ 32 (by omega) (Or.inr (by omega)),
    o0 _ 32 (by omega) (Or.inr (by omega)), data 7 (by decide)]
  rfl

/-- The eight in-place calls preserve every byte range outside the chain region
`[slot+32, slot+256)` and the heap output slot. -/
theorem chain_run_outside (oracle : Oracle) (s0 : MachineState) (slot heap : Nat)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (heapBound : heap + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outsideSlot : address + count ≤ slot + 32 ∨ slot + 256 ≤ address)
    (outsideHeap : address + count ≤ heap ∨ heap + 32 ≤ address) :
    readBuffer (chainRun oracle s0) address count = readBuffer s0 address count := by
  have big := chain_memory_bound slot slotBound
  have p0 : chainOutput s0 0 = BitVec.ofNat 64 (slot + 32*1) :=
    chain_output_slot s0 0 (by decide) slot _ slotPointer (by omega)
  have o0 := chain_step_outside oracle s0 0 _ p0 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x81 := (chain_step_register oracle s0 0 (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x231 := (chain_step_register oracle s0 0 (by decide) .x23 (by decide) (by decide)).trans heapPointer
  unfold chainRun
  generalize chainStep oracle s0 0 = s1 at o0 x81 x231 ⊢
  have p1 : chainOutput s1 1 = BitVec.ofNat 64 (slot + 32*2) :=
    chain_output_slot s1 1 (by decide) slot _ x81 (by omega)
  have o1 := chain_step_outside oracle s1 1 _ p1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x82 := (chain_step_register oracle s1 1 (by decide) .x8 (by decide) (by decide)).trans x81
  have x232 := (chain_step_register oracle s1 1 (by decide) .x23 (by decide) (by decide)).trans x231
  generalize chainStep oracle s1 1 = s2 at o1 x82 x232 ⊢
  have p2 : chainOutput s2 2 = BitVec.ofNat 64 (slot + 32*3) :=
    chain_output_slot s2 2 (by decide) slot _ x82 (by omega)
  have o2 := chain_step_outside oracle s2 2 _ p2 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x83 := (chain_step_register oracle s2 2 (by decide) .x8 (by decide) (by decide)).trans x82
  have x233 := (chain_step_register oracle s2 2 (by decide) .x23 (by decide) (by decide)).trans x232
  generalize chainStep oracle s2 2 = s3 at o2 x83 x233 ⊢
  have p3 : chainOutput s3 3 = BitVec.ofNat 64 (slot + 32*4) :=
    chain_output_slot s3 3 (by decide) slot _ x83 (by omega)
  have o3 := chain_step_outside oracle s3 3 _ p3 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x84 := (chain_step_register oracle s3 3 (by decide) .x8 (by decide) (by decide)).trans x83
  have x234 := (chain_step_register oracle s3 3 (by decide) .x23 (by decide) (by decide)).trans x233
  generalize chainStep oracle s3 3 = s4 at o3 x84 x234 ⊢
  have p4 : chainOutput s4 4 = BitVec.ofNat 64 (slot + 32*5) :=
    chain_output_slot s4 4 (by decide) slot _ x84 (by omega)
  have o4 := chain_step_outside oracle s4 4 _ p4 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x85 := (chain_step_register oracle s4 4 (by decide) .x8 (by decide) (by decide)).trans x84
  have x235 := (chain_step_register oracle s4 4 (by decide) .x23 (by decide) (by decide)).trans x234
  generalize chainStep oracle s4 4 = s5 at o4 x85 x235 ⊢
  have p5 : chainOutput s5 5 = BitVec.ofNat 64 (slot + 32*6) :=
    chain_output_slot s5 5 (by decide) slot _ x85 (by omega)
  have o5 := chain_step_outside oracle s5 5 _ p5 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x86 := (chain_step_register oracle s5 5 (by decide) .x8 (by decide) (by decide)).trans x85
  have x236 := (chain_step_register oracle s5 5 (by decide) .x23 (by decide) (by decide)).trans x235
  generalize chainStep oracle s5 5 = s6 at o5 x86 x236 ⊢
  have p6 : chainOutput s6 6 = BitVec.ofNat 64 (slot + 32*7) :=
    chain_output_slot s6 6 (by decide) slot _ x86 (by omega)
  have o6 := chain_step_outside oracle s6 6 _ p6 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x87 := (chain_step_register oracle s6 6 (by decide) .x8 (by decide) (by decide)).trans x86
  have x237 := (chain_step_register oracle s6 6 (by decide) .x23 (by decide) (by decide)).trans x236
  generalize chainStep oracle s6 6 = s7 at o6 x87 x237 ⊢
  have o7 := chain_step_outside oracle s7 7 heap (chain_output_heap s7 heap x237) heapBound
    address count readBound outsideHeap
  rw [o7, o6, o5, o4, o3, o2, o1, o0]

/-- Registers of the salt copy. -/
theorem commit_salt_copy_register (state : MachineState) (reg : Reg) (n6 : reg ≠ .x6) :
    (commitCopyState state 43).getReg reg = state.getReg reg :=
  commit_copy_register state 43 reg n6

/-- The salt copy changes only the salt slot `[slot, slot+32)`. -/
theorem commit_salt_copy_preserves (state : MachineState) (slot address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot) (slotBound : slot + 32 ≤ 2^64)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2^64)
    (separate : address + 32 ≤ slot ∨ slot + 32 ≤ address) :
    readBuffer (commitCopyState state 43) address 32 = readBuffer state address 32 :=
  commit_copy_preserves_digest state 43 slot address (Or.inl rfl)
    (by rw [if_pos rfl]; exact slotPointer) aligned slotBound readBound separate

/-- One full iteration of the submitted commitment program stores the salted
leaf digest of the eight message blocks behind the salt slot. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat) (value : Entry)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (saltBound : saltAddress + 32 ≤ 2^64)
    (saltSeparate : saltAddress + 32 ≤ slot ∨ slot + 32 ≤ saltAddress)
    (data : ∀ block < 8, readBuffer state (slot+32+32*block) 32 = value.extractLsb' (256*block) 256) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 heap 32 =
      leafDigest oracle.compression (readBuffer state saltAddress 32) value := by
  have big := chain_memory_bound slot slotBound
  rw [commit_position_evaluation]
  change readBuffer (chainRun oracle (commitCopyState state 43)) heap 32 = _
  apply chain_run_digest oracle _ slot heap _ value
    ((commit_salt_copy_register state .x8 (by decide)).trans slotPointer)
    ((commit_salt_copy_register state .x23 (by decide)).trans heapPointer) slotBound
  · exact commit_copy_digest state 43 saltAddress slot (Or.inl rfl)
      (by rw [if_pos rfl]; exact saltPointer) (by rw [if_pos rfl]; exact slotPointer)
      saltAligned slotAligned saltBound (by omega) saltSeparate
  · intro block inside
    rw [commit_salt_copy_preserves state slot _ slotPointer (by omega) (by omega) (by omega) (Or.inr (by omega))]
    exact data block inside

/-- A leaf iteration preserves every digest outside `[slot, slot+256)` and the
heap output slot. This includes all later message blocks, salts and leaf digests. -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot heap address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (heapBound : heap + 32 ≤ 2^64)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2^64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 256 ≤ address)
    (outsideHeap : address + 32 ≤ heap ∨ heap + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 address 32 =
      readBuffer state address 32 := by
  have big := chain_memory_bound slot slotBound
  rw [commit_position_evaluation]
  change readBuffer (chainRun oracle (commitCopyState state 43)) address 32 = _
  rw [chain_run_outside oracle _ slot heap
    ((commit_salt_copy_register state .x8 (by decide)).trans slotPointer)
    ((commit_salt_copy_register state .x23 (by decide)).trans heapPointer) slotBound heapBound
    address 32 readBound (by rcases outsideSlot with h | h <;> omega) outsideHeap]
  exact commit_salt_copy_preserves state slot address slotPointer (by omega) aligned readBound
    (by rcases outsideSlot with h | h <;> omega)

end CommitGolfCandidate
