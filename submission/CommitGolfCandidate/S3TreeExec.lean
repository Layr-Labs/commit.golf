import CommitGolfCandidate.S3LoopExec
import CommitGolfCandidate.S6ParentExec
import CommitGolfCandidate.CommitInput
import CommitGolfCandidate.CommitTree

/-! The commitment after the random syscall and the readiness instructions: the appended code
(nonce generator, seed-block clearing, leaf-phase setup, 2^18 blocks of 64 leaves and 16 group
calls, the parent sweep ending in the jump to PC 4412), then the existing root copy and the
successful halt, on the actual machine state. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### The state at the first appended instruction -/

theorem s3_ready_register (message : Message) {bits : Nat} (answer : BitVec bits) (reg : Reg)
    (notLink : reg ≠ .x1) :
    (s3CommitReady message answer).getReg reg = (commitInputReady message answer).getReg reg := by
  simp only [s3CommitReady, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLink)]

theorem s3_ready_pc (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).pc = BitVec.ofNat 64 1011404 := rfl

theorem s3_ready_selector (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).getReg .x5 = 0 :=
  (commit_input_leaves message answer).oracleReady.1

/-! ### The whole run after the random syscall -/

set_option maxHeartbeats 16000000 in
/-- After the random syscall and the eleven readiness instructions: the nonce generator
(`9 + 193 * 23832` instructions), the clearing and leaf-phase setup (14), `2^18` blocks (759
instructions each), the parent sweep (`7 + 4 * 4194303 + 16384 + 1`), and the root copy and halt
(11). Cycles `9 + 641 * 23832 + 14 + 1767 * 2^18 + (7 + 11 * 4194303 + 16384 + 1) + 11`, oracle
queries `1525248 + 144 * 2^18 + 4194303`, for every sequence of replies. -/
theorem s3_body_execute (message : Message) {bits : Nat} (answer : BitVec bits) (fuel : Nat) :
    execute (submission.image .commit)
        (9 + 193 * 23832 + 14 + 759 * 2 ^ 18 + (7 + 4 * 4194303 + 16384 + 1 + (11 + fuel)))
        (s3CommitReady message answer) true =
      (do let finished ← s3CommitBody (s3CommitReady message answer) (2 ^ 18)
          return ⟨.success, finished,
            9 + 641 * 23832 + 14 + 1767 * 2 ^ 18 + (7 + 11 * 4194303 + 16384 + 1) + 11,
            1525248 + 144 * 2 ^ 18 + 4194303⟩) := by
  have regs := commit_input_registers message answer
  have ready (reg : Reg) (h1 : reg ≠ .x1 := by decide) :
      (s3CommitReady message answer).getReg reg = (commitInputReady message answer).getReg reg :=
    s3_ready_register message answer reg h1
  have leavesRun := s3_leaves_execute (s3CommitReady message answer) 4096 5368713248 4294971424
    (s3_ready_pc message answer) ((ready .x5).trans (s3_ready_selector message answer))
    ((ready .x8).trans regs.1) ((ready .x18).trans regs.2.2.1) ((ready .x9).trans regs.2.1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (7 + 4 * 4194303 + 16384 + 1 + (11 + fuel))
  rw [leavesRun.1]
  simp only [s3CommitBody, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaves reached
  have known := leavesRun.2 leaves reached
  have kept (reg : Reg) (h6 : reg ≠ .x6 := by decide) (h7 : reg ≠ .x7 := by decide)
      (h10 : reg ≠ .x10 := by decide) (h11 : reg ≠ .x11 := by decide)
      (h12 : reg ≠ .x12 := by decide) (h13 : reg ≠ .x13 := by decide)
      (h18 : reg ≠ .x18 := by decide) (h21 : reg ≠ .x21 := by decide)
      (h22 : reg ≠ .x22 := by decide) (h23 : reg ≠ .x23 := by decide)
      (h24 : reg ≠ .x24 := by decide) (h25 : reg ≠ .x25 := by decide)
      (h27 : reg ≠ .x27 := by decide) (h1 : reg ≠ .x1 := by decide) :
      leaves.getReg reg = (commitInputReady message answer).getReg reg :=
    (known.2.2.2 reg h6 h7 h10 h11 h12 h13 h18 h21 h22 h23 h24 h25 h27).trans (ready reg h1)
  have parents := s6_parents_execute leaves 4294971424 (11 + fuel) known.1
    ((kept .x9).trans regs.2.1) known.2.2.1 known.2.1 (by decide) (by decide)
  rw [parents.1]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachedParents
  have done := parents.2 finished reachedParents
  have root := commit_input_root message answer
  have rootValid : ∀ word : Fin 4,
      accessValid (finished.getReg .x9 + BitVec.ofNat 64 (32 + 8 * word.val)) 8 = true := by
    rw [done.2.1, kept .x9]
    exact root.1
  have outputValid : ∀ word : Fin 4,
      accessValid (finished.getReg .x26 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [done.2.2, kept .x26]
    exact root.2
  rw [commit_root finished done.1 rootValid outputValid fuel]
  simp only [pure_bind, Execution.charge]

end CommitGolfCandidate
