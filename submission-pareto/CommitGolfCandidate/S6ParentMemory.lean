import CommitGolfCandidate.S3CommitRef
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HidingTree
import CommitGolfCandidate.S6CheckTrunc

/-! The parent sweep of `S3CommitRef` (`s6Parents`) as a function of memory, for a fixed oracle.

The setup aims x10 at the children of node 2^22 - 1 and x12 at its slot (node `n` sits at
`heap + 32 n`, `heap` = x9). Each parent writes the whole compression reply for its two children into
its slot and steps both pointers down by one node; branches and the
final jump change only the PC. After the 4,194,303 parents (node 2^22 - 1 down to node 1) every
internal node is the node compression (the whole reply) of its two children, the group digests at nodes
2^22 .. 2^23 - 1 are untouched, and nothing outside the internal slots `[heap + 32, heap + 2^27)`
has changed. Hence the heap is `referenceHeap (s6Compress compression) (2^22) groups`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Fixed-oracle evaluation of sequenced steps -/

private theorem eval_bind_state (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).1 =
      (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).1 := by
  rw [check_evaluation_bind]

private theorem eval_bind_calls (oracle : Oracle) {α β : Type} (computation : OracleComp World α)
    (continuation : α → OracleComp World β) :
    (checkEvaluation oracle (computation >>= continuation)).2 =
      (checkEvaluation oracle computation).2 +
        (checkEvaluation oracle (continuation (checkEvaluation oracle computation).1)).2 := by
  rw [check_evaluation_bind]

private theorem deterministic_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (continuation : α → OracleComp World β)
    (first : oracle.run computation = pure (checkEvaluation oracle computation))
    (second : ∀ value, oracle.run (continuation value) =
      pure (checkEvaluation oracle (continuation value))) :
    oracle.run (computation >>= continuation) =
      pure (checkEvaluation oracle (computation >>= continuation)) := by
  rw [oracle_run_bind, first, check_evaluation_bind]
  simp only [pure_bind, second]

private theorem deterministic_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (checkEvaluation oracle (pure value)) := by
  rw [oracle_run_pure, check_evaluation_pure]

private theorem read_mem_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

/-! ### Address arithmetic -/

/-- Adding the sign-extended immediate `-offset`. -/
theorem s6_parent_ofNat_sub (value offset : Nat) (low : offset ≤ value) (small : offset ≤ 4096) :
    BitVec.ofNat 64 value + BitVec.ofNat 64 (2 ^ 64 - offset) = BitVec.ofNat 64 (value - offset) := by
  rw [← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem s6_parent_sext_64 : signExtend12 (BitVec.ofNat 12 4032) = BitVec.ofNat 64 (2 ^ 64 - 64) := by
  decide

theorem s6_parent_sext_32 : signExtend12 (BitVec.ofNat 12 4064) = BitVec.ofNat 64 (2 ^ 64 - 32) := by
  decide

theorem s6_parent_lui : (((32768 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 =
    BitVec.ofNat 64 (2 ^ 27) := by
  decide

private theorem byte_offset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& (2^3-1) = address.toNat % 2^3
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem dword_decomposition (address : Word) :
    alignToDword address + BitVec.ofNat 64 (byteOffset address) = address := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (address &&& ~~~7#64) &&& (address &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  have combined : (address &&& ~~~7#64) ||| (address &&& 7#64) = address := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]

/-- The doubleword of an address starts at the address rounded down to a multiple of 8. -/
theorem s6_align_to_dword_toNat (address : Word) :
    (alignToDword address).toNat = address.toNat - address.toNat % 8 := by
  have numeric := congrArg BitVec.toNat (dword_decomposition address)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, byte_offset_mod] at numeric
  have below : (alignToDword address).toNat ≤ address.toNat := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  have small := address.isLt
  simp only [Nat.reducePow] at numeric small
  omega

/-! ### Word-level frames of the two memory writes of a parent -/

/-- A reply written at an aligned address changes no doubleword outside its own bytes. -/
theorem s6_write_bits_mem_outside {bits : Nat} (state : MachineState) (address : Nat)
    (answer : BitVec bits) (query : Word) (aligned : address % 8 = 0)
    (bounded : address + (bits + 7) / 8 ≤ 2 ^ 64)
    (outside : query.toNat < address ∨ address + (bits + 7) / 8 ≤ query.toNat) :
    (writeBits state (BitVec.ofNat 64 address) answer).getMem query = state.getMem query := by
  apply writeBits_memory_outside
  intro i inside equal
  have numeric := congrArg BitVec.toNat equal
  rw [s6_align_to_dword_toNat, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : address + i < 2 ^ 64)] at numeric
  omega

/-- Clearing bytes 30 and 31 of an aligned 32-byte slot changes no doubleword outside the slot. -/
theorem s6_clear_mem_outside (state : MachineState) (address : Nat) (query : Word)
    (aligned : address % 8 = 0) (bounded : address + 32 ≤ 2 ^ 64)
    (outside : query.toNat < address ∨ address + 32 ≤ query.toNat) :
    (state.setHalfword (BitVec.ofNat 64 (address + 30)) 0).getMem query = state.getMem query := by
  rw [show address + 30 = address + 24 + 6 by omega]
  apply clear_half_other state (address + 24) (by omega)
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address + 24 < 2 ^ 64)] at numeric
  omega

/-! ### One parent -/

/-- The state after one parent for the reply `answer`. -/
def s6ParentResult (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH) : MachineState :=
  s6ParentStep (s6ParentReply state answer)

theorem s6_parent_support (state next : MachineState) (reachable : next ∈ support (s6Parent state)) :
    ∃ answer, next = s6ParentResult state answer := by
  simp only [s6Parent, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨answer, _, rfl⟩ := reachable
  exact ⟨answer, rfl⟩

theorem s6_parent_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (s6Parent state) =
      (s6ParentResult state (oracle.compression (s6ParentInput state)), 1) := by
  rw [s6Parent, check_evaluation_public_bind]
  simp only [check_evaluation_pure]
  rfl

theorem s6_parent_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (s6Parent state) = pure (checkEvaluation oracle (s6Parent state)) := by
  unfold s6Parent
  rw [oracle_run_public_bind, check_evaluation_public_bind]
  simp only [oracle_run_pure, check_evaluation_pure, pure_bind]

theorem s6_parent_reply_register (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (reg : Reg) : (s6ParentReply state answer).getReg reg = state.getReg reg :=
  writeBits_register _ _ _ reg

theorem s6_parent_reply_pc (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH) :
    (s6ParentReply state answer).pc = state.pc + 4 := rfl

theorem s6_parent_step_register (state : MachineState) (reg : Reg) (h10 : reg ≠ .x10)
    (h12 : reg ≠ .x12) : (s6ParentStep state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h10 | exact absurd rfl h12 | rfl

theorem s6_parent_step_input (state : MachineState) :
    (s6ParentStep state).getReg .x10 = state.getReg .x10 + signExtend12 (BitVec.ofNat 12 4032) := rfl

theorem s6_parent_step_output (state : MachineState) :
    (s6ParentStep state).getReg .x12 = state.getReg .x12 + signExtend12 (BitVec.ofNat 12 4064) := rfl

theorem s6_parent_result_register (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (reg : Reg) (h10 : reg ≠ .x10) (h12 : reg ≠ .x12) :
    (s6ParentResult state answer).getReg reg = state.getReg reg := by
  rw [s6ParentResult, s6_parent_step_register _ _ h10 h12, s6_parent_reply_register]

/-- Pointers of the sweep at the parent of node `node`: its children at x10, its slot at x12. -/
structure S6SweepPointers (state : MachineState) (heap node : Nat) : Prop where
  base : state.getReg .x9 = BitVec.ofNat 64 heap
  input : state.getReg .x10 = BitVec.ofNat 64 (heap + 64 * node)
  output : state.getReg .x12 = BitVec.ofNat 64 (heap + 32 * node)

theorem s6_parent_result_pointers (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (heap node : Nat) (pointers : S6SweepPointers state heap (node + 1)) :
    S6SweepPointers (s6ParentResult state answer) heap node := by
  refine ⟨(s6_parent_result_register state answer .x9 (by decide) (by decide)).trans pointers.base,
    ?_, ?_⟩
  · rw [s6ParentResult, s6_parent_step_input, s6_parent_reply_register, pointers.input,
      s6_parent_sext_64, s6_parent_ofNat_sub _ _ (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [s6ParentResult, s6_parent_step_output, s6_parent_reply_register, pointers.output,
      s6_parent_sext_32, s6_parent_ofNat_sub _ _ (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)

/-- Memory after one parent: the reply at the slot. -/
theorem s6_parent_result_mem (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (slot : Nat) (output : state.getReg .x12 = BitVec.ofNat 64 slot) :
    (s6ParentResult state answer).mem = (writeBits state (BitVec.ofNat 64 slot) answer).mem := by
  have raw : (s6ParentResult state answer).mem = (s6ParentReply state answer).mem := rfl
  rw [raw]
  unfold s6ParentReply
  rw [output]

private theorem reply_width : (COMPRESSION_OUTPUT_LENGTH + 7) / 8 = 32 := by decide

/-- One parent changes no doubleword outside its slot. -/
theorem s6_parent_result_mem_outside (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (slot : Nat) (output : state.getReg .x12 = BitVec.ofNat 64 slot) (aligned : slot % 8 = 0)
    (bounded : slot + 32 ≤ 2 ^ 64) (query : Word)
    (outside : query.toNat < slot ∨ slot + 32 ≤ query.toNat) :
    (s6ParentResult state answer).getMem query = state.getMem query := by
  have written : (s6ParentResult state answer).getMem query =
      (writeBits state (BitVec.ofNat 64 slot) answer).getMem query := by
    simp only [MachineState.getMem, s6_parent_result_mem state answer slot output]
  rw [written]
  exact s6_write_bits_mem_outside state slot answer query aligned (by rw [reply_width]; omega)
    (by rw [reply_width]; omega)

private theorem extract_whole (answer : BitVec COMPRESSION_OUTPUT_LENGTH) :
    answer.extractLsb' (8 * 0) 256 = answer := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt answer.isLt

/-- The slot of one parent holds its whole reply (`s6Trunc` keeps every bit). -/
theorem s6_parent_result_digest (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (slot : Nat) (output : state.getReg .x12 = BitVec.ofNat 64 slot) (aligned : slot % 8 = 0)
    (bounded : slot + 32 < 2 ^ 64) :
    readBuffer (s6ParentResult state answer) slot 32 = s6Trunc answer := by
  rw [read_mem_congr _ _ (s6_parent_result_mem state answer slot output)]
  show _ = answer
  have written := write_bits_digest state slot 0 answer (by decide) (by decide)
  rw [Nat.add_zero] at written
  rw [written, extract_whole]

/-- Other aligned digests are unchanged by one parent. -/
theorem s6_parent_result_other (state : MachineState) (answer : BitVec COMPRESSION_OUTPUT_LENGTH)
    (slot : Nat) (output : state.getReg .x12 = BitVec.ofNat 64 slot) (aligned : slot % 8 = 0)
    (bounded : slot + 32 ≤ 2 ^ 64) (address : Nat) (addressAligned : address % 8 = 0)
    (addressBound : address + 32 ≤ 2 ^ 64) (apart : address + 32 ≤ slot ∨ slot + 32 ≤ address) :
    readBuffer (s6ParentResult state answer) address 32 = readBuffer state address 32 := by
  apply read_digest_congr _ _ _ addressAligned
  intro i small
  apply s6_parent_result_mem_outside state answer slot output aligned bounded
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The reply of a parent is the node compression of its two children. -/
theorem s6_parent_input_value (compress : Compression) (state : MachineState) (heap node : Nat)
    (input : state.getReg .x10 = BitVec.ofNat 64 (heap + 64 * node)) (aligned : heap % 8 = 0)
    (bounded : heap + 64 * node + 64 ≤ 2 ^ 64) :
    s6Trunc (compress (s6ParentInput state)) =
      combine (s6Compress compress) (readBuffer state (heap + 32 * (2 * node)) 32)
        (readBuffer state (heap + 32 * (2 * node + 1)) 32) := by
  show s6Trunc (compress (readBuffer state (state.getReg .x10).toNat 64)) =
    s6Trunc (compress (readBuffer state (heap + 32 * (2 * node + 1)) 32 ++
      readBuffer state (heap + 32 * (2 * node)) 32))
  rw [input, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    read_compression_halves state _ (by omega),
    show heap + 64 * node + 32 = heap + 32 * (2 * node + 1) by omega,
    show heap + 64 * node = heap + 32 * (2 * node) by omega]

/-! ### The sweep invariant -/

/-- After the parents of the nodes above `node`: pointers at `node`, every internal node above
`node` is the truncated compression of its children, and memory outside the slots written so far is
that of `start`. -/
structure S6SweepInvariant (compress : Compression) (start state : MachineState) (heap node : Nat) :
    Prop where
  pointers : S6SweepPointers state heap node
  frame : ∀ address : Word, address.toNat < heap + 32 * (node + 1) ∨ heap + 2 ^ 27 ≤ address.toNat →
    state.getMem address = start.getMem address
  parents : ∀ n, node < n → n < 2 ^ 22 →
    readBuffer state (heap + 32 * n) 32 =
      combine (s6Compress compress) (readBuffer state (heap + 32 * (2 * n)) 32)
        (readBuffer state (heap + 32 * (2 * n + 1)) 32)

/-- The invariant reads only registers x9, x10, x12 and memory. -/
theorem S6SweepInvariant.congr {compress : Compression} {start state : MachineState} {heap node : Nat}
    (invariant : S6SweepInvariant compress start state heap node) (other : MachineState)
    (memory : other.mem = state.mem) (registers : ∀ reg, other.getReg reg = state.getReg reg) :
    S6SweepInvariant compress start other heap node := by
  refine ⟨⟨(registers .x9).trans invariant.pointers.base, (registers .x10).trans invariant.pointers.input,
    (registers .x12).trans invariant.pointers.output⟩, ?_, ?_⟩
  · intro address outside
    rw [← invariant.frame address outside]
    simp only [MachineState.getMem, memory]
  · intro n above below
    simp only [read_mem_congr other state memory]
    exact invariant.parents n above below

/-- One parent extends the invariant by one node. -/
theorem s6_parent_invariant (compress : Compression) (start state : MachineState) (heap node : Nat)
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (inside : node + 1 < 2 ^ 22)
    (invariant : S6SweepInvariant compress start state heap (node + 1)) :
    S6SweepInvariant compress start (s6ParentResult state (compress (s6ParentInput state))) heap node := by
  have room : heap + 2 ^ 28 ≤ 2 ^ 36 := bound
  have output := invariant.pointers.output
  have slotAligned : (heap + 32 * (node + 1)) % 8 = 0 := by omega
  have slotBound : heap + 32 * (node + 1) + 32 ≤ 2 ^ 64 := by omega
  have other (address : Nat) (addressAligned : address % 8 = 0) (addressBound : address + 32 ≤ 2 ^ 64)
      (apart : address + 32 ≤ heap + 32 * (node + 1) ∨ heap + 32 * (node + 1) + 32 ≤ address) :=
    s6_parent_result_other state (compress (s6ParentInput state)) _ output slotAligned slotBound
      address addressAligned addressBound apart
  refine ⟨s6_parent_result_pointers state _ heap node invariant.pointers, ?_, ?_⟩
  · intro address outside
    rw [s6_parent_result_mem_outside state _ _ output slotAligned slotBound address (by omega)]
    exact invariant.frame address (by omega)
  · intro n above below
    by_cases current : n = node + 1
    · subst current
      rw [s6_parent_result_digest state _ _ output slotAligned (by omega),
        other (heap + 32 * (2 * (node + 1))) (by omega) (by omega) (by omega),
        other (heap + 32 * (2 * (node + 1) + 1)) (by omega) (by omega) (by omega)]
      exact s6_parent_input_value compress state heap (node + 1) invariant.pointers.input aligned
        (by omega)
    · rw [other (heap + 32 * n) (by omega) (by omega) (by omega),
        other (heap + 32 * (2 * n)) (by omega) (by omega) (by omega),
        other (heap + 32 * (2 * n + 1)) (by omega) (by omega) (by omega)]
      exact invariant.parents n (by omega) below

/-! ### Runs, passes, setup and exit -/

theorem s6_parent_run_invariant (oracle : Oracle) (start : MachineState) (heap : Nat)
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (count : Nat) :
    ∀ (state : MachineState) (node : Nat), node + count < 2 ^ 22 →
      S6SweepInvariant oracle.compression start state heap (node + count) →
      S6SweepInvariant oracle.compression start (checkEvaluation oracle (s6ParentRun state count)).1
        heap node := by
  induction count with
  | zero =>
    intro state node _ invariant
    simpa only [s6ParentRun, check_evaluation_pure, Nat.add_zero] using invariant
  | succ count ih =>
    intro state node inside invariant
    rw [s6ParentRun, eval_bind_state, s6_parent_evaluation]
    exact ih _ node (by omega) (s6_parent_invariant oracle.compression start state heap (node + count)
      aligned bound (by omega) (by rw [show node + count + 1 = node + (count + 1) by omega]; exact invariant))

theorem s6_parent_run_calls (oracle : Oracle) (count : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s6ParentRun state count)).2 = count := by
  induction count with
  | zero => intro state; simp only [s6ParentRun, check_evaluation_pure]
  | succ count ih =>
    intro state
    rw [s6ParentRun, eval_bind_calls, ih, s6_parent_evaluation]
    show 1 + count = count + 1
    omega

theorem s6_parent_run_deterministic (oracle : Oracle) (count : Nat) :
    ∀ state : MachineState,
      oracle.run (s6ParentRun state count) = pure (checkEvaluation oracle (s6ParentRun state count)) := by
  induction count with
  | zero => intro state; exact deterministic_pure oracle state
  | succ count ih =>
    intro state
    exact deterministic_bind oracle _ _ (s6_parent_deterministic oracle state) ih

theorem s6_bne_memory (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BNE left right offset)).mem = state.mem := by
  show (if state.getReg left != state.getReg right then state.setPC (state.pc + signExtend13 offset)
    else state.setPC (state.pc + 4)).mem = state.mem
  split <;> rfl

theorem s6_bne_register (state : MachineState) (left right : Reg) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE left right offset)).getReg reg = state.getReg reg := by
  show (if state.getReg left != state.getReg right then state.setPC (state.pc + signExtend13 offset)
    else state.setPC (state.pc + 4)).getReg reg = state.getReg reg
  split <;> exact MachineState.getReg_setPC

/-- Setting the PC keeps memory (stated for a variable PC, so no concrete PC is ever evaluated). -/
theorem s6_set_pc_mem (state : MachineState) (pc : Word) : (state.setPC pc).mem = state.mem := rfl

theorem s6_jal_zero (state : MachineState) (offset : BitVec 21) :
    execInstrBr state (.JAL .x0 offset) = state.setPC (state.pc + signExtend21 offset) := rfl

theorem s6_parent_branch_memory (state : MachineState) :
    (execInstrBr state s6ParentBranch).mem = state.mem :=
  s6_bne_memory state _ _ _

theorem s6_parent_branch_register (state : MachineState) (reg : Reg) :
    (execInstrBr state s6ParentBranch).getReg reg = state.getReg reg :=
  s6_bne_register state _ _ _ reg

theorem s6_parent_exit_memory (state : MachineState) :
    (execInstrBr state s6ParentExit).mem = state.mem := by
  rw [s6ParentExit, s6_jal_zero, s6_set_pc_mem]

theorem s6_parent_exit_register (state : MachineState) (reg : Reg) :
    (execInstrBr state s6ParentExit).getReg reg = state.getReg reg := by
  rw [s6ParentExit, s6_jal_zero]
  exact MachineState.getReg_setPC

theorem s6_parent_pass_state (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (s6ParentPass state count)).1 =
      execInstrBr (checkEvaluation oracle (s6ParentRun state count)).1 s6ParentBranch := by
  simp only [s6ParentPass, eval_bind_state, check_evaluation_pure]

theorem s6_parent_pass_calls (oracle : Oracle) (state : MachineState) (count : Nat) :
    (checkEvaluation oracle (s6ParentPass state count)).2 = count := by
  simp only [s6ParentPass, eval_bind_calls, check_evaluation_pure, s6_parent_run_calls, Nat.add_zero]

theorem s6_parent_pass_deterministic (oracle : Oracle) (state : MachineState) (count : Nat) :
    oracle.run (s6ParentPass state count) = pure (checkEvaluation oracle (s6ParentPass state count)) :=
  deterministic_bind oracle _ _ (s6_parent_run_deterministic oracle count state)
    fun _ => deterministic_pure oracle _

theorem s6_parent_pass_invariant (oracle : Oracle) (start state : MachineState) (heap node count : Nat)
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (inside : node + count < 2 ^ 22)
    (invariant : S6SweepInvariant oracle.compression start state heap (node + count)) :
    S6SweepInvariant oracle.compression start (checkEvaluation oracle (s6ParentPass state count)).1
      heap node := by
  rw [s6_parent_pass_state]
  exact (s6_parent_run_invariant oracle start heap aligned bound count state node inside invariant).congr
    _ (s6_parent_branch_memory _) (s6_parent_branch_register _)

theorem s6_parent_passes_invariant (oracle : Oracle) (start : MachineState) (heap : Nat)
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (passes : Nat) :
    ∀ (state : MachineState) (node : Nat), node + 256 * passes < 2 ^ 22 →
      S6SweepInvariant oracle.compression start state heap (node + 256 * passes) →
      S6SweepInvariant oracle.compression start
        (checkEvaluation oracle (s6ParentPasses state passes)).1 heap node := by
  induction passes with
  | zero =>
    intro state node _ invariant
    simpa only [s6ParentPasses, check_evaluation_pure, Nat.mul_zero, Nat.add_zero] using invariant
  | succ passes ih =>
    intro state node inside invariant
    rw [s6ParentPasses, eval_bind_state]
    apply ih _ node (by omega)
    apply s6_parent_pass_invariant oracle start state heap (node + 256 * passes) 256 aligned bound
      (by omega)
    rw [show node + 256 * passes + 256 = node + 256 * (passes + 1) by omega]
    exact invariant

theorem s6_parent_passes_calls (oracle : Oracle) (passes : Nat) :
    ∀ state : MachineState, (checkEvaluation oracle (s6ParentPasses state passes)).2 = 256 * passes := by
  induction passes with
  | zero => intro state; simp only [s6ParentPasses, check_evaluation_pure]
  | succ passes ih =>
    intro state
    rw [s6ParentPasses, eval_bind_calls, ih, s6_parent_pass_calls]
    omega

theorem s6_parent_passes_deterministic (oracle : Oracle) (passes : Nat) :
    ∀ state : MachineState,
      oracle.run (s6ParentPasses state passes) =
        pure (checkEvaluation oracle (s6ParentPasses state passes)) := by
  induction passes with
  | zero => intro state; exact deterministic_pure oracle state
  | succ passes ih =>
    intro state
    exact deterministic_bind oracle _ _ (s6_parent_pass_deterministic oracle state 256) ih

theorem s6_parent_setup_register (state : MachineState) (reg : Reg)
    (h7 : reg ≠ .x7) (h10 : reg ≠ .x10) (h11 : reg ≠ .x11) (h12 : reg ≠ .x12) (h13 : reg ≠ .x13) :
    (s6ParentSetup state).getReg reg = state.getReg reg := by
  cases reg <;> first | exact absurd rfl h7 | exact absurd rfl h10 | exact absurd rfl h11 |
    exact absurd rfl h12 | exact absurd rfl h13 | rfl

theorem s6_parent_setup_memory (state : MachineState) : (s6ParentSetup state).mem = state.mem := rfl

/-- Registers after the parent setup: the sweep starts at node 2^22 - 1. -/
theorem s6_parent_setup_pointers (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28)) :
    S6SweepPointers (s6ParentSetup state) heap (2 ^ 22 - 1) := by
  refine ⟨(s6_parent_setup_register state .x9 (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans base, ?_, ?_⟩
  · show state.getReg .x22 + signExtend12 (BitVec.ofNat 12 4032) = _
    rw [top, s6_parent_sext_64, s6_parent_ofNat_sub _ _ (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · show state.getReg .x9 + (((32768 : BitVec 20).zeroExtend 32 <<< 12 : BitVec 32)).signExtend 64 +
      signExtend12 (BitVec.ofNat 12 4064) = _
    rw [base, s6_parent_lui, s6_parent_sext_32, ← BitVec.ofNat_add,
      s6_parent_ofNat_sub _ _ (by omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by omega)

/-! ### The whole sweep -/

theorem s6_parents_evaluation_state (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s6Parents state)).1 =
      execInstrBr (checkEvaluation oracle (s6ParentPasses
        (checkEvaluation oracle (s6ParentPass (s6ParentSetup state) 255)).1 16383)).1 s6ParentExit := by
  simp only [s6Parents, eval_bind_state, check_evaluation_pure]

theorem s6_parents_queries (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (s6Parents state)).2 = 4194303 := by
  simp only [s6Parents, eval_bind_calls, check_evaluation_pure, s6_parent_pass_calls,
    s6_parent_passes_calls]

theorem s6_parents_deterministic (oracle : Oracle) (state : MachineState) :
    oracle.run (s6Parents state) = pure (checkEvaluation oracle (s6Parents state)) := by
  unfold s6Parents
  exact deterministic_bind oracle _ _ (s6_parent_pass_deterministic oracle _ 255) fun first =>
    deterministic_bind oracle _ _ (s6_parent_passes_deterministic oracle 16383 first)
      fun _ => deterministic_pure oracle _

/-- The invariant at node 0 for the final state, relative to the start of the sweep. -/
theorem s6_parents_invariant (oracle : Oracle) (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28))
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) :
    S6SweepInvariant oracle.compression state (checkEvaluation oracle (s6Parents state)).1 heap 0 := by
  have start : S6SweepInvariant oracle.compression state (s6ParentSetup state) heap
      (256 * 16383 + 255) := by
    have pointers := s6_parent_setup_pointers state heap base top
    rw [show 2 ^ 22 - 1 = 256 * 16383 + 255 by norm_num] at pointers
    refine ⟨pointers, ?_, ?_⟩
    · intro address _
      simp only [MachineState.getMem, s6_parent_setup_memory]
    · intro n above below
      omega
  have first := s6_parent_pass_invariant oracle state (s6ParentSetup state) heap (256 * 16383) 255
    aligned bound (by omega) start
  have rest := s6_parent_passes_invariant oracle state heap aligned bound 16383 _ 0 (by omega)
    (by rw [Nat.zero_add]; exact first)
  rw [s6_parents_evaluation_state]
  exact rest.congr _ (s6_parent_exit_memory _) (s6_parent_exit_register _)

/-! ### Heap, memory frame, queries and registers of the whole sweep -/

/-- Every doubleword outside the internal slots `[heap + 32, heap + 2^27)` is unchanged. -/
theorem s6_parents_memory (oracle : Oracle) (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28))
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (address : Word)
    (outside : address.toNat < heap + 32 ∨ heap + 2 ^ 27 ≤ address.toNat) :
    (checkEvaluation oracle (s6Parents state)).1.getMem address = state.getMem address :=
  (s6_parents_invariant oracle state heap base top aligned bound).frame address (by omega)

/-- Every buffer outside the internal slots `[heap + 32, heap + 2^27)` is unchanged. -/
theorem s6_parents_preserves (oracle : Oracle) (state : MachineState) (heap : Nat)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28))
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES) (address count : Nat)
    (outside : address + count ≤ heap + 32 ∨ heap + 2 ^ 27 ≤ address)
    (bounded : address + count ≤ 2 ^ 64) :
    readBuffer (checkEvaluation oracle (s6Parents state)).1 address count =
      readBuffer state address count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8 * count))
  apply Finset.sum_congr rfl
  intro i inside
  have small := Finset.mem_range.mp inside
  unfold MachineState.getByte
  rw [s6_parents_memory oracle state heap base top aligned bound]
  rw [s6_align_to_dword_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The heap after the sweep**: node `n` (0 < n < 2^23) is node `n` of the reference heap
over the group digests with the truncating compression. -/
theorem s6_parents_heap (oracle : Oracle) (state : MachineState) (heap : Nat) (leaf : Nat → Digest)
    (base : state.getReg .x9 = BitVec.ofNat 64 heap)
    (top : state.getReg .x22 = BitVec.ofNat 64 (heap + 2 ^ 28))
    (aligned : heap % 8 = 0) (bound : heap + 2 ^ 28 ≤ MEMORY_BYTES)
    (groups : ∀ g < 2 ^ 22, readBuffer state (heap + 32 * (2 ^ 22 + g)) 32 = leaf g)
    (node : Nat) (inside : 0 < node ∧ node < 2 ^ 23) :
    readBuffer (checkEvaluation oracle (s6Parents state)).1 (heap + 32 * node) 32 =
      referenceHeap (s6Compress oracle.compression) (2 ^ 22) leaf node := by
  have final := s6_parents_invariant oracle state heap base top aligned bound
  apply heap_eq_reference (s6Compress oracle.compression) (2 ^ 22) leaf
    (fun n => readBuffer (checkEvaluation oracle (s6Parents state)).1 (heap + 32 * n) 32)
  · intro n positive below
    exact final.parents n positive below
  · intro g below
    show readBuffer _ (heap + 32 * (2 ^ 22 + g)) 32 = leaf g
    rw [← groups g below]
    apply read_digest_congr _ _ _ (by omega)
    intro i small
    apply final.frame
    right
    have room : heap + 2 ^ 28 ≤ 2 ^ 36 := bound
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact inside.1
  · have : 2 * 2 ^ 22 = 2 ^ 23 := by norm_num
    omega

/-- Registers other than x7, x10..x13 are those at the start of the sweep. -/
theorem s6_parents_register (state finished : MachineState)
    (reachable : finished ∈ support (s6Parents state)) (reg : Reg)
    (outside : reg ∉ [Reg.x7, .x10, .x11, .x12, .x13]) :
    finished.getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
  obtain ⟨h7, h10, h11, h12, h13⟩ := outside
  have run (count : Nat) : ∀ (current next : MachineState), next ∈ support (s6ParentRun current count) →
      next.getReg reg = current.getReg reg := by
    induction count with
    | zero =>
      intro current next reached
      simp only [s6ParentRun, support_pure, Set.mem_singleton_iff] at reached
      rw [reached]
    | succ count ih =>
      intro current next reached
      simp only [s6ParentRun, mem_support_bind_iff] at reached
      obtain ⟨middle, middleReached, rest⟩ := reached
      obtain ⟨answer, rfl⟩ := s6_parent_support current middle middleReached
      rw [ih _ _ rest, s6_parent_result_register current answer reg h10 h12]
  have pass (count : Nat) (current next : MachineState) (reached : next ∈ support (s6ParentPass current count)) :
      next.getReg reg = current.getReg reg := by
    simp only [s6ParentPass, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨swept, sweptReached, rfl⟩ := reached
    rw [s6_parent_branch_register, run count current swept sweptReached]
  have passes (count : Nat) : ∀ (current next : MachineState),
      next ∈ support (s6ParentPasses current count) → next.getReg reg = current.getReg reg := by
    induction count with
    | zero =>
      intro current next reached
      simp only [s6ParentPasses, support_pure, Set.mem_singleton_iff] at reached
      rw [reached]
    | succ count ih =>
      intro current next reached
      simp only [s6ParentPasses, mem_support_bind_iff] at reached
      obtain ⟨middle, middleReached, rest⟩ := reached
      rw [ih _ _ rest, pass 256 current middle middleReached]
  simp only [s6Parents, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨first, firstReached, swept, sweptReached, rfl⟩ := reachable
  rw [s6_parent_exit_register, passes 16383 first swept sweptReached,
    pass 255 _ first firstReached, s6_parent_setup_register state reg h7 h10 h11 h12 h13]

theorem s6_parents_evaluation_register (oracle : Oracle) (state : MachineState) (reg : Reg)
    (outside : reg ∉ [Reg.x7, .x10, .x11, .x12, .x13]) :
    (checkEvaluation oracle (s6Parents state)).1.getReg reg = state.getReg reg :=
  s6_parents_register state _ (check_evaluation_support oracle _) reg outside

end CommitGolfCandidate
