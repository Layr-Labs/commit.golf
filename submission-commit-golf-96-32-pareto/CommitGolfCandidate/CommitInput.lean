import CommitGolfCandidate.CommitTree

/-! The trusted commitment ABI establishes every tree-building address invariant. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- State at the first 32-leaf block, for any private random answer. -/
def commitInputReady (message : Message) {bits : Nat} (answer : BitVec bits) : MachineState :=
  let setup := commitSetupState (submission.initialState .commit message)
  commitReadyState (writeBits setup (setup.getReg .x10) answer)

private theorem initialized_registers (initial : MachineState) {bits : Nat} (answer : BitVec bits) :
    let setup := commitSetupState initial
    let ready := commitReadyState (writeBits setup (setup.getReg .x10) answer)
    ready.getReg .x10 = initial.getReg .x10 + 18446744073709551592 ∧
    ready.getReg .x9 = initial.getReg .x12 ∧
    ready.getReg .x18 = initial.getReg .x12 + 1610612736 ∧
    ready.getReg .x23 = initial.getReg .x12 + 805306368 ∧
    ready.getReg .x26 = initial.getReg .x11 ∧
    ready.getReg .x20 = initial.getReg .x12 + 1879048192 ∧
    ready.getReg .x5 = 0 ∧ ready.getReg .x11 = 96 ∧ ready.getReg .x13 = 0 := by
  dsimp only
  have regs := commit_setup_registers initial
  have readyReg (reg : Reg) (not10 : reg ≠ .x10)
      (not5 : reg ≠ .x5) (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) :
      (commitReadyState (writeBits (commitSetupState initial)
        ((commitSetupState initial).getReg .x10) answer)).getReg reg =
          (commitSetupState initial).getReg reg := by
    rw [commit_ready_register _ reg not10 not5 not11 not13, writeBits_register]
  have rdy := commit_ready_regs (writeBits (commitSetupState initial)
    ((commitSetupState initial).getReg .x10) answer)
  exact ⟨(rdy.1.trans (writeBits_register _ _ _ .x8)).trans regs.2.1,
    (readyReg .x9 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.1,
    (readyReg .x18 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.1,
    (readyReg .x23 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.1,
    (readyReg .x26 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.2.1,
    (readyReg .x20 (by decide) (by decide) (by decide) (by decide)).trans regs.2.2.2.2.2.2.2.2,
    rdy.2.1, rdy.2.2.1, rdy.2.2.2⟩

/-- Fixed ABI pointers and loop registers at entry to the 32-leaf loop. -/
theorem commit_input_registers (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x10 = 4072 ∧
    (commitInputReady message answer).getReg .x9 = 4294971424 ∧
    (commitInputReady message answer).getReg .x18 = 5905584160 ∧
    (commitInputReady message answer).getReg .x23 = 5100277792 ∧
    (commitInputReady message answer).getReg .x26 = 4294971392 ∧
    (commitInputReady message answer).getReg .x20 = 6174019616 ∧
    (commitInputReady message answer).getReg .x5 = 0 ∧
    (commitInputReady message answer).getReg .x11 = 96 ∧
    (commitInputReady message answer).getReg .x13 = 0 := by
  let initial := submission.initialState .commit message
  have regs := initialized_registers initial answer
  have messagePtr : initial.getReg .x10 = (4096 : Word) := rfl
  have heapPtr : initial.getReg .x12 = (4294971424 : Word) := rfl
  have outputPtr : initial.getReg .x11 = (4294971392 : Word) := rfl
  have slotPtr : initial.getReg .x10 + 18446744073709551592 = (4072 : Word) := by rw [messagePtr]; rfl
  have saltPtr : initial.getReg .x12 + 1610612736 = (5905584160 : Word) := by rw [heapPtr]; rfl
  have leafPtr : initial.getReg .x12 + 805306368 = (5100277792 : Word) := by rw [heapPtr]; rfl
  have endPtr : initial.getReg .x12 + 1879048192 = (6174019616 : Word) := by rw [heapPtr]; rfl
  exact ⟨regs.1.trans slotPtr, regs.2.1.trans heapPtr, regs.2.2.1.trans saltPtr,
    regs.2.2.2.1.trans leafPtr, regs.2.2.2.2.1.trans outputPtr, regs.2.2.2.2.2.1.trans endPtr,
    regs.2.2.2.2.2.2⟩

/-- The first 32-leaf block establishes `CommitLeavesInvariant` for all `2^19` blocks. -/
theorem commit_input_leaves (message : Message) {bits : Nat} (answer : BitVec bits) :
    CommitLeavesInvariant (commitInputReady message answer) (2 ^ 19) := by
  have regs := commit_input_registers message answer
  refine ⟨?_, ?_, by norm_num, regs.2.2.2.2.2.2.1, regs.2.2.2.2.2.2.2.1, regs.2.2.2.2.2.2.2.2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have setupPC := commit_setup_pc (submission.initialState .commit message) rfl
    change (commitReadyState _).pc = _
    rw [if_neg (by norm_num)]
    apply commit_ready_pc
    rw [writeBits_pc, setupPC]; rfl
  · rw [regs.2.2.2.2.2.1, regs.2.2.1]; rfl
  · rw [regs.1]; decide
  · rw [regs.1]; decide
  · rw [regs.2.2.1]; decide
  · rw [regs.2.2.1]; decide
  · rw [regs.2.2.2.1]; decide
  · rw [regs.2.2.2.1]; decide

theorem commit_input_root (message : Message) {bits : Nat} (answer : BitVec bits) :
    (∀ word : Fin 4,
      accessValid ((commitInputReady message answer).getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true) := by
  rw [(commit_input_registers message answer).2.2.2.2.1]
  intro word; fin_cases word <;> rfl

end CommitGolfCandidate
