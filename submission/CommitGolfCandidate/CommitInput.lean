import CommitGolfCandidate.CommitTree

/-! The trusted commitment ABI establishes every tree-building address invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem commit_buffer_access (base words word : Nat)
    (space : base + 8 * words ≤ MEMORY_BYTES) (aligned : base % 8 = 0) (inside : word < words) :
    accessValid (BitVec.ofNat 64 base + BitVec.ofNat 64 (8 * word)) 8 = true := by
  have baseSmall : base < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  have offsetSmall : 8 * word < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  have totalSmall : base + 8 * word < 2 ^ 64 := by dsimp [MEMORY_BYTES] at space; omega
  simp only [accessValid, rangeValid, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt baseSmall, Nat.mod_eq_of_lt offsetSmall, Nat.mod_eq_of_lt totalSmall,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega

/-- State at the first leaf, for any private random answer. The width is generic
so this address proof does not depend on the contents or encoding of randomness. -/
def commitInputReady (message : Message) {bits : Nat} (answer : BitVec bits) : MachineState :=
  let setup := commitSetupState (submission.initialState .commit message)
  commitReadyState (writeBits setup (setup.getReg .x10) answer)

/-- Setup and random writes preserve all register values needed by the loops. -/
private theorem initialized_registers (initial : MachineState) {bits : Nat} (answer : BitVec bits) :
    let setup := commitSetupState initial
    let ready := commitReadyState (writeBits setup (setup.getReg .x10) answer)
    ready.getReg .x8 = initial.getReg .x10 ∧
    ready.getReg .x9 = initial.getReg .x12 ∧
    ready.getReg .x18 = initial.getReg .x12 + 1073741824 ∧
    ready.getReg .x19 = 16777216 ∧
    ready.getReg .x23 = initial.getReg .x12 + 536870912 ∧
    ready.getReg .x26 = initial.getReg .x11 ∧
    ready.getReg .x21 = initial.getReg .x10 - 32 ∧ ready.getReg .x20 = initial.getReg .x20 := by
  dsimp only
  have regs := commit_setup_registers initial
  have readyReg (reg : Reg) (notScratch : reg ≠ .x21) (notCounter : reg ≠ .x20)
      (notArguments : reg ∉ [.x5,.x10,.x11,.x12,.x13,.x28]) :
      (commitReadyState (writeBits (commitSetupState initial)
        ((commitSetupState initial).getReg .x10) answer)).getReg reg =
          (commitSetupState initial).getReg reg := by
    rw [commit_ready_register _ reg notScratch notCounter notArguments, writeBits_register]
  have counters := commit_ready_counters (writeBits (commitSetupState initial)
    ((commitSetupState initial).getReg .x10) answer)
  exact ⟨(readyReg .x8 (by decide) (by decide) (by decide)).trans regs.2.1,
    (readyReg .x9 (by decide) (by decide) (by decide)).trans regs.2.2.1,
    (readyReg .x18 (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.1,
    (readyReg .x19 (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.1,
    (readyReg .x23 (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.2.1,
    (readyReg .x26 (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.2.2,
    (by rw [counters.1, writeBits_register, regs.2.1]), (by rw [counters.2, writeBits_register]; rfl)⟩

/-- Fixed ABI pointers and loop registers, independent of sampled salt bytes. -/
theorem commit_input_registers (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x8 = 4096 ∧
    (commitInputReady message answer).getReg .x9 = 4294971424 ∧
    (commitInputReady message answer).getReg .x18 = 5368713248 ∧
    (commitInputReady message answer).getReg .x19 = 16777216 ∧
    (commitInputReady message answer).getReg .x23 = 4831842336 ∧
    (commitInputReady message answer).getReg .x26 = 4294971392 ∧
    (commitInputReady message answer).getReg .x21 = 4064 ∧
    (commitInputReady message answer).getReg .x20 = 0 := by
  let initial := submission.initialState .commit message
  have regs := initialized_registers initial answer
  have messagePtr : initial.getReg .x10 = (4096 : Word) := rfl
  have heapPtr : initial.getReg .x12 = (4294971424 : Word) := rfl
  have outputPtr : initial.getReg .x11 = (4294971392 : Word) := rfl
  have saltPtr : initial.getReg .x12 + 1073741824 = (5368713248 : Word) := by rw [heapPtr]; rfl
  have leafPtr : initial.getReg .x12 + 536870912 = (4831842336 : Word) := by rw [heapPtr]; rfl
  exact ⟨regs.1.trans messagePtr, regs.2.1.trans heapPtr, regs.2.2.1.trans saltPtr,
    regs.2.2.2.1, regs.2.2.2.2.1.trans leafPtr, regs.2.2.2.2.2.1.trans outputPtr,
    regs.2.2.2.2.2.2.1.trans (by rw [messagePtr]; rfl), regs.2.2.2.2.2.2.2⟩

/-- The first iteration has space for every remaining message block, salt, and
leaf digest, for all actual messages and every private random answer. -/
theorem commit_input_leaves (message : Message) {bits : Nat} (answer : BitVec bits) :
    CommitLeavesInvariant (commitInputReady message answer) (2 ^ 24) := by
  have regs := commit_input_registers message answer
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have setupPC := commit_setup_pc (submission.initialState .commit message) rfl
    change (commitReadyState _).pc = 4280
    apply commit_ready_pc
    simp only [writeBits, MachineState.setPC]
    rw [setupPC]; rfl
  · exact regs.2.2.2.2.2.2.2
  · rw [regs.2.2.2.1]; decide
  · rw [regs.2.2.2.2.2.2.1, regs.1]; rfl
  · rw [regs.1]; decide
  · rw [regs.1]
    exact fun word inside => commit_buffer_access 4096 (32 * 2 ^ 24) word (by decide) (by decide) inside
  · rw [regs.2.2.1]
    exact fun word inside => commit_buffer_access 5368713248 (4 * 2 ^ 24) word (by decide) (by decide) inside
  · rw [regs.2.2.2.2.1]
    exact fun word inside => commit_buffer_access 4831842336 (4 * 2 ^ 24) word (by decide) (by decide) inside

  · exact commit_ready_oracle _
  · unfold commitInputReady
    rw [commit_ready_block_counter, writeBits_register]
    rfl
  · rw [regs.1, regs.2.2.2.2.2.1]
    rfl

/-- The complete fixed heap allocation meets the oracle syscall's size and
alignment requirements for every internal node. -/
theorem commit_input_parents (message : Message) {bits : Nat} (answer : BitVec bits) :
    ParentBuffers ((commitInputReady message answer).getReg .x9) (2 ^ 24 - 1) := by
  rw [(commit_input_registers message answer).2.1]
  change ParentBuffers (4294971424#64) (2 ^ 24 - 1)
  intro node positive bounded
  have inputNat : (4294971424#64 + (BitVec.ofNat 64 node <<< 6)).toNat = 4294971424 + 64 * node := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  have outputNat : (4294971424#64 + (BitVec.ofNat 64 node <<< 5)).toNat = 4294971424 + 32 * node := by
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  simp only [rangeValid, inputNat, outputNat, decide_eq_true_eq]
  norm_num [MEMORY_BYTES] at bounded ⊢
  omega

theorem commit_input_root (message : Message) {bits : Nat} (answer : BitVec bits) :
    (∀ word : Fin 4,
      accessValid ((commitInputReady message answer).getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true) ∧
    (∀ word : Fin 4,
      accessValid ((commitInputReady message answer).getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true) := by
  rw [(commit_input_registers message answer).2.1,
    (commit_input_registers message answer).2.2.2.2.2.1]
  constructor <;> intro word <;> fin_cases word <;> rfl

end CommitGolfCandidate
