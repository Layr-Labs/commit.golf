import CommitGolfCandidate.S3LoopExec

/-! Stage-3 commitment after the private nonces are written: the appended leaf phase
(S3LoopExec), then the retained parent setup, the long parent schedule, the root copy and
the successful halt. The appended leaf phase hands
over at PC 4364 with the compression width and selector restored, so the parent-phase
theorems apply to the actual machine state without any register frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### Root copy after the parent phase -/

theorem s3_load_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.LD destination source offset) =
      (execInstrBr state (.LD destination source offset)).setPC (pc + 4) := by
  cases destination <;> rfl

theorem s3_store_pc (state : MachineState) (pc : Word)
    (destination source : Reg) (offset : BitVec 12) :
    execInstrBr (state.setPC pc) (.SD destination source offset) =
      (execInstrBr state (.SD destination source offset)).setPC (pc + 4) := rfl

/-- The root copy does not read the program counter. -/
theorem s3_root_copy_pc (state : MachineState) (pc : Word) :
    commitCopyState (state.setPC pc) 79 = (commitCopyState state 79).setPC (pc + 32) := by
  rw [commit_copy_expansion, commit_copy_expansion]
  simp only [show (79 : Nat) ≠ 46 by decide, show (79 : Nat) ≠ 55 by decide,
    ite_false, ite_true, List.foldl, s3_load_pc, s3_store_pc]
  simp only [BitVec.add_assoc]
  rfl

theorem s3_exit_pc (state : MachineState) (pc : Word) :
    commitExitState (state.setPC pc) = commitExitState state := by
  cases state
  rfl

/-! ### Parent phase from the hand-over state -/

/-- From PC 4364 with all `2^24` leaf digests in the heap: parent setup, the long parent
schedule, root copy and halt, on the actual machine state. -/
theorem s3_parents_execute (leaves : MachineState) (pc : leaves.pc = 4364)
    (total : leaves.getReg .x19 = BitVec.ofNat 64 (2 ^ 24))
    (constants : leaves.getReg .x5 = 0 ∧ leaves.getReg .x11 = 64 ∧ leaves.getReg .x13 = 0)
    (buffers : ParentBuffers (leaves.getReg .x9) (2 ^ 24 - 1))
    (rootValid : ∀ word : Fin 4,
      accessValid (leaves.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true)
    (outputValid : ∀ word : Fin 4,
      accessValid (leaves.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (6 + (251660 * 200 + 49 + (11 + fuel))) leaves true =
      (do let parents ← commitParents (commitParentsStartState leaves) (2 ^ 24 - 1)
          return ⟨.success, commitExitState (commitCopyState parents 79),
            838862 * 200 + 171, 2 ^ 24 - 1⟩) := by
  have residual : leaves.getReg .x19 - 1 = BitVec.ofNat 64 (2 ^ 24 - 1) := by
    rw [total]
    rfl
  have nonempty : leaves.getReg .x19 - 1 ≠ 0 := by
    rw [residual]
    decide
  let ready := commitParentsStartState leaves
  have readyRegister (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      ready.getReg reg = leaves.getReg reg := by
    apply commit_parents_start_register leaves reg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  have readyPointers : ParentPointerInvariant ready (2 ^ 24 - 1) :=
    commit_parents_start_pointers leaves (2 ^ 24 - 1) nonempty residual
  have readyPC : ready.pc = group341Schedule.initialPlan.entry := by
    rw [group341_schedule_entry]
    exact commit_parents_start_pc leaves nonempty
  have scheduleParents : group341Schedule.parents 200 = 2 ^ 24 - 1 := by
    rw [group341_schedule_parents]
    decide
  have readyBuffers : ParentBuffers (ready.getReg .x9) (2 ^ 24 - 1) := by
    rw [readyRegister .x9 (by simp)]
    exact buffers
  have parentRun := long_parent_schedule_execute (submission.image .commit) group341Schedule
    group341_schedule_valid group341_image_fetched ready 200 (by decide)
    (by rw [scheduleParents]; decide)
    (by rw [scheduleParents]; exact readyPointers)
    (commit_parents_start_constants leaves constants)
    (by rw [scheduleParents]; exact readyBuffers) (11 + fuel)
  rw [← readyPC, hoist_pc_self, group341_schedule_instructions, group341_schedule_cycles,
    scheduleParents] at parentRun
  rw [commit_parents_start leaves pc nonempty, parentRun]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have parentDone := commit_parents_finished ready (2 ^ 24 - 1) (by decide) readyPointers
    finished reachedParents
  have root : ∀ word : Fin 4,
      accessValid ((finished.setPC 4412).getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 =
        true := by
    rw [MachineState.getReg_setPC, parentDone.2 .x9 (by simp), readyRegister .x9 (by simp)]
    exact rootValid
  have output : ∀ word : Fin 4,
      accessValid ((finished.setPC 4412).getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 =
        true := by
    rw [MachineState.getReg_setPC, parentDone.2 .x26 (by simp), readyRegister .x26 (by simp)]
    exact outputValid
  rw [commit_root (finished.setPC 4412) rfl root output, s3_root_copy_pc, s3_exit_pc]
  simp only [pure_bind, Execution.charge, Nat.add_zero]
  congr 1

/-! ### The whole run after the random syscall -/

theorem s3_ready_register (message : Message) {bits : Nat} (answer : BitVec bits) (reg : Reg)
    (notLink : reg ≠ .x1) :
    (s3CommitReady message answer).getReg reg = (commitInputReady message answer).getReg reg := by
  simp only [s3CommitReady, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLink)]

theorem s3_ready_pc (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).pc = BitVec.ofNat 64 1011404 := rfl

/-- The limit register of the leaf loop is the nonce base. -/
theorem s3_ready_limit (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x22 = 5368713248 := by
  have saved : (commitInputReady message answer).getReg .x22 =
      (commitInputReady message answer).getReg .x18 := by
    unfold commitInputReady
    rw [commit_ready_heap_end, commit_ready_register _ .x18 (by decide) (by decide) (by decide)]
  rw [saved, (commit_input_registers message answer).2.2.1]

/-- The carried input register starts at the old salt slot, 32 bytes below the message. -/
theorem s3_ready_input (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x10 = 4064 := by
  have carried : (commitInputReady message answer).getReg .x10 =
      (commitInputReady message answer).getReg .x21 := by
    unfold commitInputReady
    exact commit_ready_input _
  rw [carried, (commit_input_registers message answer).2.2.2.2.2.2.1]

theorem s3_ready_selector (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x5 = 0 :=
  (commit_input_leaves message answer).oracleReady.1

set_option maxHeartbeats 16000000 in
/-- After the random syscall and the eleven readiness instructions: the appended leaf phase
(entry, `2^18` groups of 64 leaves, nonce repair, exit), parent setup, parents, root copy,
halt. -/
theorem s3_body_execute (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    execute (submission.image .commit)
        (771 * 2 ^ 18 + 50 + (6 + (251660 * 200 + 49 + (11 + fuel))))
        (s3CommitReady message answer) true =
      (do let finished ← s3CommitBody (s3CommitReady message answer) (2 ^ 18)
          return ⟨.success, finished, 1667 * 2 ^ 18 + 50 + (838862 * 200 + 171),
            128 * 2 ^ 18 + (2 ^ 24 - 1)⟩) := by
  have regs := commit_input_registers message answer
  have ready (reg : Reg) (h1 : reg ≠ .x1 := by decide) :
      (s3CommitReady message answer).getReg reg = (commitInputReady message answer).getReg reg :=
    s3_ready_register message answer reg h1
  have leavesRun := s3_leaves_execute (s3CommitReady message answer) (2 ^ 18 - 1) 4064 4096
    5368713248 4831842336 (s3_ready_pc message answer)
    ((ready .x5).trans (s3_ready_selector message answer))
    ((ready .x10).trans (s3_ready_input message answer))
    ((ready .x8).trans regs.1) ((ready .x18).trans regs.2.2.1)
    ((ready .x23).trans regs.2.2.2.2.1) ((ready .x22).trans (s3_ready_limit message answer))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (6 + (251660 * 200 + 49 + (11 + fuel)))
  have groupCount : 2 ^ 18 - 1 + 1 = 2 ^ 18 := by decide
  have parentCount : 64 * 2 ^ 18 - 1 = 2 ^ 24 - 1 := by decide
  rw [groupCount] at leavesRun
  rw [leavesRun.1]
  simp only [s3CommitBody, bind_assoc, pure_bind, parentCount]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have known := leavesRun.2 leaves reached
  have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide)
      (h10 : reg ≠ .x10 := by decide) (h11 : reg ≠ .x11 := by decide)
      (h12 : reg ≠ .x12 := by decide) (h13 : reg ≠ .x13 := by decide)
      (h18 : reg ≠ .x18 := by decide) (h23 : reg ≠ .x23 := by decide)
      (h1 : reg ≠ .x1 := by decide) :
      leaves.getReg reg = (commitInputReady message answer).getReg reg :=
    (known.2.2.2.2 reg h6 h7 h10 h11 h12 h13 h18 h23).trans (ready reg h1)
  have root := commit_input_root message answer
  have parents := s3_parents_execute leaves known.1 ((kept .x19).trans regs.2.2.2.1)
    ⟨known.2.1, known.2.2.1, known.2.2.2.1⟩
    (by rw [kept .x9]; exact commit_input_parents message answer)
    (by rw [kept .x9]; exact root.1) (by rw [kept .x26]; exact root.2) fuel
  rw [parents]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun parent => ?_
  simp only [Execution.charge]

end CommitGolfCandidate
