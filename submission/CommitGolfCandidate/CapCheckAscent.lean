import CommitGolfCandidate.CapAdvanceGuard
import CommitGolfCandidate.CapParentRootMemory

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capParentPrefix

def capCheckAscentPrepared (state : MachineState) : MachineState :=
  capNavigationState .ascend (capAdvanceGuardState true state)
def capCheckAscentAnswer (state : MachineState) (answer : BitVec 256) : MachineState :=
  capFlowState (.jump 2097116) (capParentAnswerState (capCheckAscentPrepared state) answer)
abbrev capCheckAscentQuery (state : MachineState) (node : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (12288 + 64 * (node / 2) + 32) 32 ++
    readBuffer state (12288 + 64 * (node / 2)) 32

def capCheckCompression (input : BitVec COMPRESSION_INPUT_LENGTH) :
    OracleComp World (BitVec 256) :=
  World.query (.inr (.inl input))

theorem cap_check_ascent_prepared_memory (state : MachineState) :
    (capCheckAscentPrepared state).mem = state.mem := by
  rw [capCheckAscentPrepared, cap_navigation_memory, cap_advance_guard_memory]

theorem cap_check_ascent_prepared_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x20 ∧ reg ≠ .x7) :
    (capCheckAscentPrepared state).getReg reg = state.getReg reg := by
  rw [capCheckAscentPrepared, cap_navigation_register _ _ reg outside,
    cap_advance_guard_register true state reg outside.2]

theorem cap_check_ascent_prepared_index (state : MachineState) (node : Nat)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capCheckAscentPrepared state).getReg .x20 = BitVec.ofNat 64 (node / 2) := by
  apply cap_navigation_ascend _ node _ bounded
  exact (cap_advance_guard_register true state .x20 (by decide)).trans index

theorem cap_check_ascent_prepared_pc (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry true)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (odd : node % 2 ≠ 0) :
    (capCheckAscentPrepared state).pc = 4704 := by
  have guardPC := cap_advance_guard_pc true state node pc index root bounded nonroot
  simp only [if_neg odd] at guardPC
  rw [capCheckAscentPrepared, cap_navigation_pc, guardPC]
  rfl

theorem cap_check_ascent_answer_pc (state : MachineState) (answer : BitVec 256)
    (pc : (capCheckAscentPrepared state).pc = 4704) :
    (capCheckAscentAnswer state answer).pc = capAdvanceEntry true := by
  have answerPC : (capParentAnswerState (capCheckAscentPrepared state) answer).pc =
      (capCheckAscentPrepared state).pc + 20 := by
    change (capParentPrefix (capCheckAscentPrepared state) 4).pc + 4 =
      (capCheckAscentPrepared state).pc + 20
    rw [cap_parent_prefix_pc _ 4 (by decide)]
    rw [BitVec.add_assoc]
    rfl
  rw [capCheckAscentAnswer, cap_flow_jump_pc, answerPC, pc]
  rfl

private theorem charge_pair (result : Execution) (first second callsFirst callsSecond : Nat) :
    (result.charge first callsFirst).charge second callsSecond =
      result.charge (second + first) (callsSecond + callsFirst) := by
  simp only [Execution.charge, Nat.add_assoc]

attribute [local irreducible] capCheckAscentPrepared

theorem cap_check_ascent_execute (state : MachineState) (node : Nat)
    (pc : state.pc = capAdvanceEntry true)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (root : state.getReg .x31 = 1) (bounded : node < 512) (nonroot : node ≠ 1)
    (odd : node % 2 ≠ 0) (roots : state.getReg .x18 = 12288)
    (selectors : state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (capWalkImage true) (10 + fuel) state allowCoins =
      (do let answer ← capCheckCompression (capCheckAscentQuery state node)
          let result ← execute (capWalkImage true) fuel
            (capCheckAscentAnswer state answer) allowCoins
          return result.charge 17 1) := by
  have guardPC := cap_advance_guard_pc true state node pc index root bounded nonroot
  simp only [if_neg odd] at guardPC
  have preparedPC := cap_check_ascent_prepared_pc state node pc index root bounded nonroot odd
  have preparedIndex := cap_check_ascent_prepared_index state node index bounded
  have preparedRoots : (capCheckAscentPrepared state).getReg .x18 = 12288 :=
    (cap_check_ascent_prepared_register state .x18 (by decide)).trans roots
  have preparedSelectors :
      (capCheckAscentPrepared state).getReg .x5 = 0 ∧
      (capCheckAscentPrepared state).getReg .x11 = 64 ∧
      (capCheckAscentPrepared state).getReg .x13 = 0 :=
    ⟨(cap_check_ascent_prepared_register state .x5 (by decide)).trans selectors.1,
     (cap_check_ascent_prepared_register state .x11 (by decide)).trans selectors.2.1,
     (cap_check_ascent_prepared_register state .x13 (by decide)).trans selectors.2.2⟩
  have back : ∀ answer : BitVec 256,
      fetch (capWalkImage true) (capParentAnswerState (capCheckAscentPrepared state) answer) =
        some (.base (capFlowInstruction (.jump 2097116))) := by
    intro answer
    apply cap_image_fetch _ _ 157 _ (by decide)
    · change (capParentPrefix (capCheckAscentPrepared state) 4).pc + 4 = 4724
      rw [cap_parent_prefix_pc _ 4 (by decide), preparedPC]
      rfl
    · rfl
  have parent : execute (capWalkImage true) (5 + (1 + fuel))
        (capCheckAscentPrepared state) allowCoins =
      (do let answer ← capCheckCompression (capCheckAscentQuery state node)
          let result ← execute (capWalkImage true) (1 + fuel)
            (capParentAnswerState (capCheckAscentPrepared state) answer) allowCoins
          return result.charge 12 1) := by
    have normalized := cap_parent_execute (capCheckAscentPrepared state) (node / 2)
      preparedPC preparedRoots preparedIndex (by omega) preparedSelectors
      (1 + fuel) allowCoins
    change execute (capWalkImage true) (5 + (1 + fuel))
        (capCheckAscentPrepared state) allowCoins =
      (do let answer ← capCheckCompression
            (capCheckAscentQuery (capCheckAscentPrepared state) node)
          let result ← execute (capWalkImage true) (1 + fuel)
            (capParentAnswerState (capCheckAscentPrepared state) answer) allowCoins
          return result.charge 12 1) at normalized
    have querySame : capCheckAscentQuery (capCheckAscentPrepared state) node =
        capCheckAscentQuery state node := by
      unfold capCheckAscentQuery
      rw [read_buffer_memory_congr (capCheckAscentPrepared state) state
        (cap_check_ascent_prepared_memory state),
        read_buffer_memory_congr (capCheckAscentPrepared state) state
          (cap_check_ascent_prepared_memory state)]
    rw [querySame] at normalized
    exact normalized
  rw [show 10 + fuel = 3 + (1 + (5 + (1 + fuel))) by omega,
    cap_advance_guard_execute true state node pc index root bounded nonroot,
    cap_navigation_image_execute true .ascend _ guardPC]
  rw [show capNavigationState .ascend (capAdvanceGuardState true state) =
    capCheckAscentPrepared state from (by unfold capCheckAscentPrepared; rfl)]
  rw [parent]
  simp_rw [cap_flow_execute _ _ _ (back _)]
  simp only [bind_assoc, pure_bind, charge_pair, capCheckAscentAnswer]

theorem cap_check_ascent_answer_index (state : MachineState) (answer : BitVec 256)
    (node : Nat) (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capCheckAscentAnswer state answer).getReg .x20 = BitVec.ofNat 64 (node / 2) := by
  rw [capCheckAscentAnswer, cap_flow_register, cap_parent_answer_register _ _ .x20 (by decide)]
  exact cap_check_ascent_prepared_index state node index bounded

theorem cap_check_ascent_answer_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x10 ∧ reg ≠ .x12) :
    (capCheckAscentAnswer state answer).getReg reg = state.getReg reg := by
  rw [capCheckAscentAnswer, cap_flow_register,
    cap_parent_answer_register _ _ reg ⟨outside.2.2.1, outside.2.2.2⟩]
  exact cap_check_ascent_prepared_register state reg ⟨outside.2.1, outside.1⟩

theorem cap_check_ascent_answer_marks (state : MachineState) (node : Nat)
    (answer : BitVec 256) (marked : Nat → Bool)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (roots : state.getReg .x18 = 12288) (bounded : node < 512)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capCheckAscentAnswer state answer) 256 0 marked := by
  apply cap_marks_ready_memory
    (capParentAnswerState (capCheckAscentPrepared state) answer)
    (capCheckAscentAnswer state answer) 256 0 marked
    (cap_flow_memory (.jump 2097116) _)
  apply cap_parent_answer_marks _ (node / 2) answer marked
    ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
    (cap_check_ascent_prepared_index state node index bounded) (by omega)
  exact cap_marks_ready_memory state (capCheckAscentPrepared state) 256 0 marked
    (cap_check_ascent_prepared_memory state) ready

theorem cap_check_ascent_answer_root_map (state : MachineState) (answer : BitVec 256)
    (node other : Nat) (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (roots : state.getReg .x18 = 12288) (bounded : node < 512) (otherBound : other < 512) :
    capReadRoot (capCheckAscentAnswer state answer) other =
      if other = node / 2 then answer else capReadRoot state other := by
  have frame := cap_flow_memory (.jump 2097116)
    (capParentAnswerState (capCheckAscentPrepared state) answer)
  unfold capReadRoot
  unfold capCheckAscentAnswer
  rw [read_buffer_memory_congr _ _ frame]
  change capReadRoot (capParentAnswerState (capCheckAscentPrepared state) answer) other = _
  rw [cap_parent_answer_root_map _ (node / 2) answer
    ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
    (cap_check_ascent_prepared_index state node index bounded) (by omega) other otherBound]
  unfold capReadRoot
  rw [read_buffer_memory_congr _ _ (cap_check_ascent_prepared_memory state)]

end CommitGolfCandidate
