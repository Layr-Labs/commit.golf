import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.LeafRefinement

/-! Salt loading, in-place leaf chain and heap write of the actual commitment leaf
iteration, refined to the reference salted leaf digest. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Commitment's two digest copies use the same load/store sequence as opening.
Only the source and destination registers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 43 ∨ start = 80) :
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
    (location : start = 43 ∨ start = 80)
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
    (location : start = 43 ∨ start = 80)
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

/-- The 96-byte oracle input of in-place call `j`. -/
def chainInput (state : MachineState) (j : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (state.getReg .x8 + BitVec.ofNat 64 (64*j)).toNat 96

/-- One in-place call evaluated with a fixed oracle. -/
def chainAnswer (oracle : Oracle) (state : MachineState) (j : Nat) : BitVec 256 :=
  oracle.compression (chainInput state j)

/-- One in-place call evaluated with a fixed oracle. -/
def chainStep (oracle : Oracle) (state : MachineState) (j : Nat) : MachineState :=
  chainCallState state j (chainAnswer oracle state j)

/-- The four in-place calls of one leaf. -/
def chainRun (oracle : Oracle) (state : MachineState) : MachineState :=
  chainStep oracle (chainStep oracle (chainStep oracle (chainStep oracle state 0) 1) 2) 3

/-- A complete leaf iteration under a fixed oracle: salt copy, four calls, advance. -/
theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      (commitPositionNextState (chainRun oracle (commitCopyState state 43)), 4) := by
  rw [commitPositionRun]
  simp only [check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem chain_step_register (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 4)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (chainStep oracle state j).getReg reg = state.getReg reg :=
  chain_call_register state j hj _ reg n10 n12

theorem chain_output_slot (state : MachineState) (j : Nat) (hj : j < 3) (slot out : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot) (hout : out = slot + 64*(j+1)) :
    chainOutput state j = BitVec.ofNat 64 out := by
  unfold chainOutput
  rw [if_neg (by omega), slotPointer, ← BitVec.ofNat_add, hout,
    show slot + (64*j+64) = slot + 64*(j+1) by omega]

theorem chain_output_heap (state : MachineState) (heap : Nat)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap) :
    chainOutput state 3 = BitVec.ofNat 64 heap := by
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

/-- The 96-byte input of call `j` is its chaining value followed by its message block. -/
theorem chain_query_split (state : MachineState) (slot j : Nat) :
    readBuffer state (slot + 64*j) 96 =
      leafInput (readBuffer state (slot + 64*j) 32) (readBuffer state (slot + 32 + 64*j) 64) := by
  rw [read_leaf_query, show slot + 64*j + 32 = slot + 32 + 64*j by omega]
  rfl

theorem chain_input_split (state : MachineState) (j : Nat) (hj : j < 4)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) :
    chainInput state j =
      leafInput (readBuffer state (slot + 64*j) 32) (readBuffer state (slot + 32 + 64*j) 64) := by
  unfold chainInput
  rw [chain_source_nat state j hj slot slotPointer slotBound]
  exact chain_query_split state slot j

theorem chain_step_written (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 4)
    (slot : Nat) (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (out : Nat) (hout : chainOutput state j = BitVec.ofNat 64 out) :
    readBuffer (chainStep oracle state j) out 32 =
      absorb oracle.compression (readBuffer state (slot + 64*j) 32)
        (readBuffer state (slot + 32 + 64*j) 64) := by
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

/-- Four in-place calls, starting from a slot holding the salt followed by the four
message blocks, write the reference salted leaf digest into the heap slot. -/
theorem chain_run_digest (oracle : Oracle) (s0 : MachineState) (slot heap : Nat)
    (salt : Digest) (value : Entry)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES)
    (saltData : readBuffer s0 slot 32 = salt)
    (data : ∀ block < 4, readBuffer s0 (slot+32+64*block) 64 = value.extractLsb' (512*block) 512) :
    readBuffer (chainRun oracle s0) heap 32 = leafDigest oracle.compression salt value := by
  have big := chain_memory_bound slot slotBound
  -- call 0
  have p0 : chainOutput s0 0 = BitVec.ofNat 64 (slot + 64*1) :=
    chain_output_slot s0 0 (by decide) slot _ slotPointer (by omega)
  have w0 := chain_step_written oracle s0 0 (by decide) slot slotPointer slotBound _ p0
  have o0 := chain_step_outside oracle s0 0 _ p0 (by omega)
  have x8a := (chain_step_register oracle s0 0 (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 0 (by decide) .x23 (by decide) (by decide)).trans heapPointer
  have d0 : readBuffer (chainStep oracle s0 0) (slot + 64*1) 32 =
      absorb oracle.compression salt (value.extractLsb' (512*0) 512) := by
    rw [w0, show slot + 64*0 = slot by omega, saltData, data 0 (by decide)]
  unfold chainRun
  generalize chainStep oracle s0 0 = t1 at d0 o0 x8a x23a ⊢
  -- call 1
  have p1 : chainOutput t1 1 = BitVec.ofNat 64 (slot + 64*2) :=
    chain_output_slot t1 1 (by decide) slot _ x8a (by omega)
  have w1 := chain_step_written oracle t1 1 (by decide) slot x8a slotBound _ p1
  have o1 := chain_step_outside oracle t1 1 _ p1 (by omega)
  have x8b := (chain_step_register oracle t1 1 (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 1 (by decide) .x23 (by decide) (by decide)).trans x23a
  have d1 : readBuffer (chainStep oracle t1 1) (slot + 64*2) 32 =
      absorb oracle.compression (absorb oracle.compression salt (value.extractLsb' (512*0) 512))
        (value.extractLsb' (512*1) 512) := by
    rw [w1, d0, o0 _ 64 (by omega) (Or.inr (by omega)), data 1 (by decide)]
  generalize chainStep oracle t1 1 = t2 at d1 o1 x8b x23b ⊢
  -- call 2
  have p2 : chainOutput t2 2 = BitVec.ofNat 64 (slot + 64*3) :=
    chain_output_slot t2 2 (by decide) slot _ x8b (by omega)
  have w2 := chain_step_written oracle t2 2 (by decide) slot x8b slotBound _ p2
  have o2 := chain_step_outside oracle t2 2 _ p2 (by omega)
  have x8c := (chain_step_register oracle t2 2 (by decide) .x8 (by decide) (by decide)).trans x8b
  have x23c := (chain_step_register oracle t2 2 (by decide) .x23 (by decide) (by decide)).trans x23b
  have d2 : readBuffer (chainStep oracle t2 2) (slot + 64*3) 32 =
      absorb oracle.compression (absorb oracle.compression (absorb oracle.compression salt
        (value.extractLsb' (512*0) 512)) (value.extractLsb' (512*1) 512))
        (value.extractLsb' (512*2) 512) := by
    rw [w2, d1, o1 _ 64 (by omega) (Or.inr (by omega)),
      o0 _ 64 (by omega) (Or.inr (by omega)), data 2 (by decide)]
  generalize chainStep oracle t2 2 = t3 at d2 o2 x8c x23c ⊢
  -- call 3 writes the heap slot
  have w3 := chain_step_written oracle t3 3 (by decide) slot x8c slotBound heap
    (chain_output_heap t3 heap x23c)
  rw [w3, d2, o2 _ 64 (by omega) (Or.inr (by omega)),
    o1 _ 64 (by omega) (Or.inr (by omega)), o0 _ 64 (by omega) (Or.inr (by omega)), data 3 (by decide)]
  rfl

/-- The four in-place calls preserve every byte range outside the chain region
`[slot+64, slot+224)` and the heap output slot. -/
theorem chain_run_outside (oracle : Oracle) (s0 : MachineState) (slot heap : Nat)
    (slotPointer : s0.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : s0.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (heapBound : heap + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outsideSlot : address + count ≤ slot + 64 ∨ slot + 224 ≤ address)
    (outsideHeap : address + count ≤ heap ∨ heap + 32 ≤ address) :
    readBuffer (chainRun oracle s0) address count = readBuffer s0 address count := by
  have big := chain_memory_bound slot slotBound
  have p0 : chainOutput s0 0 = BitVec.ofNat 64 (slot + 64*1) :=
    chain_output_slot s0 0 (by decide) slot _ slotPointer (by omega)
  have o0 := chain_step_outside oracle s0 0 _ p0 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8a := (chain_step_register oracle s0 0 (by decide) .x8 (by decide) (by decide)).trans slotPointer
  have x23a := (chain_step_register oracle s0 0 (by decide) .x23 (by decide) (by decide)).trans heapPointer
  unfold chainRun
  generalize chainStep oracle s0 0 = t1 at o0 x8a x23a ⊢
  have p1 : chainOutput t1 1 = BitVec.ofNat 64 (slot + 64*2) :=
    chain_output_slot t1 1 (by decide) slot _ x8a (by omega)
  have o1 := chain_step_outside oracle t1 1 _ p1 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x8b := (chain_step_register oracle t1 1 (by decide) .x8 (by decide) (by decide)).trans x8a
  have x23b := (chain_step_register oracle t1 1 (by decide) .x23 (by decide) (by decide)).trans x23a
  generalize chainStep oracle t1 1 = t2 at o1 x8b x23b ⊢
  have p2 : chainOutput t2 2 = BitVec.ofNat 64 (slot + 64*3) :=
    chain_output_slot t2 2 (by decide) slot _ x8b (by omega)
  have o2 := chain_step_outside oracle t2 2 _ p2 (by omega) address count readBound
    (by rcases outsideSlot with h | h <;> omega)
  have x23c := (chain_step_register oracle t2 2 (by decide) .x23 (by decide) (by decide)).trans x23b
  generalize chainStep oracle t2 2 = t3 at o2 x23c ⊢
  have o3 := chain_step_outside oracle t3 3 heap (chain_output_heap t3 heap x23c) heapBound
    address count readBound outsideHeap
  rw [o3, o2, o1, o0]

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
leaf digest of the four message blocks behind the salt slot. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (slot saltAddress heap : Nat) (value : Entry)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotAligned : slot % 8 = 0) (saltAligned : saltAddress % 8 = 0)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (saltBound : saltAddress + 32 ≤ 2^64)
    (saltSeparate : saltAddress + 32 ≤ slot ∨ slot + 32 ≤ saltAddress)
    (data : ∀ block < 4, readBuffer state (slot+32+64*block) 64 = value.extractLsb' (512*block) 512) :
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
    rw [read_compression_halves _ _ (by omega),
      commit_salt_copy_preserves state slot _ slotPointer (by omega) (by omega) (by omega) (Or.inr (by omega)),
      commit_salt_copy_preserves state slot _ slotPointer (by omega) (by omega) (by omega) (Or.inr (by omega)),
      ← read_compression_halves _ _ (by omega)]
    exact data block inside

/-- A leaf iteration preserves every digest outside `[slot, slot+224)` and the
heap output slot. This includes all later message blocks, salts and leaf digests. -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (slot heap address : Nat)
    (slotPointer : state.getReg .x8 = BitVec.ofNat 64 slot)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 heap)
    (slotBound : slot + 288 ≤ MEMORY_BYTES) (heapBound : heap + 32 ≤ 2^64)
    (aligned : address % 8 = 0) (readBound : address + 32 ≤ 2^64)
    (outsideSlot : address + 32 ≤ slot ∨ slot + 224 ≤ address)
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
