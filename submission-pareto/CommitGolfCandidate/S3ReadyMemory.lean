import CommitGolfCandidate.S3LeafBytes
import CommitGolfCandidate.BufferRefinement

/-! Stage-3 commitment: contents and pointers of the state at the first appended
instruction, from the real commitment ABI and the private nonce reply. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option exponentiation.threshold 4096

private theorem setup_memory (state : MachineState) :
    (commitSetupState state).mem = state.mem := rfl

private theorem ready_memory (state : MachineState) :
    (commitReadyState state).mem = state.mem := rfl

private theorem initialized_memory (initial : MachineState) {bits : Nat} (answer : BitVec bits)
    (destination : Word) (pointer : initial.getReg .x12+1073741824 = destination) :
    (commitReadyState (writeBits (commitSetupState initial)
      ((commitSetupState initial).getReg .x10) answer)).mem =
      (writeBits initial destination answer).mem := by
  rw [ready_memory, (commit_setup_registers initial).2.2.2.1, pointer]
  exact write_bits_memory_congr _ _ _ answer (setup_memory _)

private theorem initial_heap_pointer (candidate : Submission) (message : Message) :
    (candidate.initialState .commit message).getReg .x12 =
      BitVec.ofNat 64 candidate.layout.trapdoor := rfl

/-- Setup changes registers only; the random syscall writes exactly the nonce buffer. -/
theorem commit_input_memory (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).mem =
      (writeBits (submission.initialState .commit message) (BitVec.ofNat 64 5368713248) answer).mem := by
  apply initialized_memory
  rw [initial_heap_pointer]
  rfl

private theorem link_memory (state : MachineState) :
    ((state.setReg .x1 4316).setPC 1011404).mem = state.mem := rfl

private theorem s3_link_memory (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).mem = (commitInputReady message answer).mem :=
  link_memory (commitInputReady message answer)

/-- The link register and entry PC do not affect memory. -/
theorem s3_ready_memory (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).mem =
      (writeBits (submission.initialState .commit message) (BitVec.ofNat 64 5368713248) answer).mem := by
  rw [s3_link_memory message answer]
  exact commit_input_memory message answer

private theorem s3_extract_all (value : Entry) : value.extractLsb' (8*0) (8*256) = value := by
  apply BitVec.eq_of_toNat_eq
  have bound : value.toNat < 2^(8*256) := value.isLt
  simp only [BitVec.extractLsb'_toNat, Nat.mul_zero, Nat.shiftRight_zero]
  exact Nat.mod_eq_of_lt bound

/-- Nonce generation leaves every original 256-byte message entry intact. -/
theorem s3_ready_value (message : Message) (answer : BitVec (192*LENGTH)) (index : Index) :
    readBuffer (s3CommitReady message answer) (4096+256*index.val) 256 = message index := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [s3_read_memory _ _ (s3_ready_memory message answer),
    write_bits_read_outside _ answer 5368713248 _ 256 (by decide) (by omega) (Or.inl (by omega))]
  have decoded := read_serialized_slice (submission.initialState .commit message) (message index)
    (4096+256*index.val) 0 256 (by
      intro j hj
      have byte := commit_input_byte message index j hj
      rw [Nat.zero_add]
      exact byte)
  rw [decoded]
  exact s3_extract_all (message index)

/-- Each packed 24-byte nonce is exactly its slice of the private random reply. -/
theorem s3_ready_nonce (message : Message) (answer : BitVec (192*LENGTH)) (index : Index) :
    readBuffer (s3CommitReady message answer) (5368713248+24*index.val) 24 =
      answer.extractLsb' (192*index.val) 192 := by
  rw [s3_read_memory _ _ (s3_ready_memory message answer)]
  have chunk := write_bits_nonce_chunk LENGTH (submission.initialState .commit message)
    5368713248 answer index (by decide)
  rw [read_nonce_buffer] at chunk
  exact expand_nonce_injective chunk

private theorem s3_ready_link (message : Message) {bits : Nat} (answer : BitVec bits)
    (reg : Reg) (other : reg ≠ .x1) :
    (s3CommitReady message answer).getReg reg = (commitInputReady message answer).getReg reg := by
  unfold s3CommitReady
  rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm other)]

/-- Fixed pointers at the first appended instruction, for every nonce reply. -/
theorem s3_ready_registers (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x10 = BitVec.ofNat 64 4064 ∧
    (s3CommitReady message answer).getReg .x8 = BitVec.ofNat 64 4096 ∧
    (s3CommitReady message answer).getReg .x18 = BitVec.ofNat 64 5368713248 ∧
    (s3CommitReady message answer).getReg .x22 = BitVec.ofNat 64 5368713248 ∧
    (s3CommitReady message answer).getReg .x23 = BitVec.ofNat 64 4831842336 ∧
    (s3CommitReady message answer).getReg .x9 = BitVec.ofNat 64 4294971424 ∧
    (s3CommitReady message answer).getReg .x19 = BitVec.ofNat 64 16777216 ∧
    (s3CommitReady message answer).getReg .x26 = BitVec.ofNat 64 4294971392 := by
  have regs := commit_input_registers message answer
  have input : (commitInputReady message answer).getReg .x10 =
      (commitInputReady message answer).getReg .x21 := commit_ready_input _
  have saved : (commitInputReady message answer).getReg .x22 =
      (commitInputReady message answer).getReg .x18 := by
    unfold commitInputReady
    rw [commit_ready_heap_end, commit_ready_register _ .x18 (by decide) (by decide) (by decide)]
  rw [s3_ready_link message answer .x10 (by decide),
    s3_ready_link message answer .x8 (by decide),
    s3_ready_link message answer .x18 (by decide),
    s3_ready_link message answer .x22 (by decide),
    s3_ready_link message answer .x23 (by decide),
    s3_ready_link message answer .x9 (by decide),
    s3_ready_link message answer .x19 (by decide),
    s3_ready_link message answer .x26 (by decide)]
  exact ⟨input.trans regs.2.2.2.2.2.2.1, regs.1, regs.2.2.1, saved.trans regs.2.2.1,
    regs.2.2.2.2.1, regs.2.1, regs.2.2.2.1, regs.2.2.2.2.2.1⟩

end CommitGolfCandidate
