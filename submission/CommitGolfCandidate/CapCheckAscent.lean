import CommitGolfCandidate.CapAdvanceGuard
import CommitGolfCandidate.CapParentRootMemory
import CommitGolfCandidate.S6CheckTrunc

/-! Checker ascent is a complete paid DFS macro. It dispatches the odd child,
moves to its parent, snapshots both child roots, writes one arbitrary answer,
jumps to the truncation code, which clears the parent root's bytes 30 and 31,
and jumps back to advance. The 12 instructions cost 19 cycles and one query. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer capParentPrefix

def capCheckAscentPrepared (state : MachineState) : MachineState :=
  capNavigationState .ascend (capAdvanceGuardState true state)
/-- The parent reply, then the jump from word 157 to the truncation code at word 443. -/
def capCheckAscentReply (state : MachineState) (answer : BitVec 256) : MachineState :=
  capFlowState (.jump 1144) (capParentAnswerState (capCheckAscentPrepared state) answer)
/-- `SH x0, 30(x12)` clears the parent root's bytes 30 and 31. -/
def capCheckAscentCleared (state : MachineState) (answer : BitVec 256) : MachineState :=
  execInstrBr (capCheckAscentReply state answer) (.SH .x12 .x0 30)
def capCheckAscentAnswer (state : MachineState) (answer : BitVec 256) : MachineState :=
  capFlowState (.jump 2095968) (capCheckAscentCleared state answer)
abbrev capCheckAscentQuery (state : MachineState) (node : Nat) : BitVec COMPRESSION_INPUT_LENGTH :=
  readBuffer state (12288 + 64 * (node / 2) + 32) 32 ++
    readBuffer state (12288 + 64 * (node / 2)) 32

/-- A typed paid World query; its explicit result type keeps continuation
rewrites independent of reduction of the oracle's dependent range. -/
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

theorem cap_check_ascent_reply_pc (state : MachineState) (answer : BitVec 256)
    (pc : (capCheckAscentPrepared state).pc = 4704) :
    (capParentAnswerState (capCheckAscentPrepared state) answer).pc = 4724 := by
  change (capParentPrefix (capCheckAscentPrepared state) 4).pc + 4 = 4724
  rw [cap_parent_prefix_pc _ 4 (by decide), pc]
  rfl

theorem cap_check_ascent_answer_pc (state : MachineState) (answer : BitVec 256)
    (pc : (capCheckAscentPrepared state).pc = 4704) :
    (capCheckAscentAnswer state answer).pc = capAdvanceEntry true := by
  have replyPC := cap_check_ascent_reply_pc state answer pc
  rw [capCheckAscentAnswer, cap_flow_jump_pc]
  change ((capCheckAscentReply state answer).pc + 4) + signExtend21 2095968 = _
  rw [capCheckAscentReply, cap_flow_jump_pc, replyPC]
  rfl

theorem cap_check_ascent_reply_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) :
    (capCheckAscentReply state answer).getReg reg =
      (capParentPrefix (capCheckAscentPrepared state) 4).getReg reg := by
  rw [capCheckAscentReply, cap_flow_register]
  exact cap_compression_register _ answer reg

theorem cap_check_ascent_reply_destination (state : MachineState) (answer : BitVec 256)
    (node : Nat) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capCheckAscentReply state answer).getReg .x12 = capRootAddress (node / 2) := by
  rw [cap_check_ascent_reply_register]
  exact cap_parent_destination _ (node / 2)
    ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
    (cap_check_ascent_prepared_index state node index bounded)

private theorem half_register (state : MachineState) (address : Word) (half : BitVec 16)
    (reg : Reg) : (state.setHalfword address half).getReg reg = state.getReg reg := by
  cases reg <;> rfl

private theorem half_congr (left right : MachineState) (same : left.mem = right.mem)
    (address : Word) (half : BitVec 16) :
    (left.setHalfword address half).mem = (right.setHalfword address half).mem := by
  simp only [MachineState.setHalfword, MachineState.setMem, MachineState.getMem, same]

theorem cap_check_ascent_cleared_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) :
    (capCheckAscentCleared state answer).getReg reg =
      (capCheckAscentReply state answer).getReg reg := by
  rw [capCheckAscentCleared, execInstrBr, MachineState.getReg_setPC, half_register]

/-- The macro's only writes: the reply in the parent root slot, then the cleared halfword. -/
theorem cap_check_ascent_memory (state : MachineState) (answer : BitVec 256)
    (node : Nat) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capCheckAscentAnswer state answer).mem =
      ((capParentAnswerState (capCheckAscentPrepared state) answer).setHalfword
        (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 24 + 6)) 0).mem := by
  have destination := cap_check_ascent_reply_destination state answer node roots index bounded
  rw [capCheckAscentAnswer, cap_flow_memory, capCheckAscentCleared, execInstrBr]
  change ((capCheckAscentReply state answer).setHalfword
    ((capCheckAscentReply state answer).getReg .x12 + signExtend12 30)
    (BitVec.truncate 16 ((capCheckAscentReply state answer).getReg .x0))).mem = _
  rw [destination, capRootAddress,
    show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 by decide, ← BitVec.ofNat_add,
    show 12288 + 32 * (node / 2) + 30 = 12288 + 32 * (node / 2) + 24 + 6 by omega]
  exact half_congr _ _ (cap_flow_memory _ _) _ _

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
    execute (capWalkImage true) (12 + fuel) state allowCoins =
      (do let answer ← capCheckCompression (capCheckAscentQuery state node)
          let result ← execute (capWalkImage true) fuel
            (capCheckAscentAnswer state answer) allowCoins
          return result.charge 19 1) := by
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
  have enter : ∀ answer : BitVec 256,
      fetch (capWalkImage true) (capParentAnswerState (capCheckAscentPrepared state) answer) =
        some (.base (capFlowInstruction (.jump 1144))) := by
    intro answer
    apply cap_image_fetch _ _ 157 _ (by decide)
    · rw [cap_check_ascent_reply_pc state answer preparedPC]
      rfl
    · rfl
  have replyPC (answer : BitVec 256) : (capCheckAscentReply state answer).pc = 5868 := by
    rw [capCheckAscentReply, cap_flow_jump_pc, cap_check_ascent_reply_pc state answer preparedPC]
    rfl
  have clearFetched : ∀ answer : BitVec 256,
      fetch (capWalkImage true) (capCheckAscentReply state answer) =
        some (.base (.SH .x12 .x0 30)) := by
    intro answer
    apply cap_image_fetch _ _ 443 _ (by decide)
    · rw [replyPC answer]
      rfl
    · rfl
  have clearStep : ∀ answer : BitVec 256,
      ordinaryStep (capCheckAscentReply state answer) (.base (.SH .x12 .x0 30)) =
        some (capCheckAscentCleared state answer) := by
    intro answer
    have destination := cap_check_ascent_reply_destination state answer node roots index bounded
    have address : (capCheckAscentReply state answer).getReg .x12 + signExtend12 30 =
        BitVec.ofNat 64 (12288 + 32 * (node / 2) + 30) := by
      rw [destination, capRootAddress,
        show signExtend12 (30 : BitVec 12) = BitVec.ofNat 64 30 by decide, ← BitVec.ofNat_add]
    have valid : accessValid (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 30)) 2 = true := by
      have small : (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 30)).toNat =
          12288 + 32 * (node / 2) + 30 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [accessValid, rangeValid, small, MEMORY_BYTES, Bool.and_eq_true,
        decide_eq_true_eq]
      omega
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, address, valid, ↓reduceIte]
    rfl
  have back : ∀ answer : BitVec 256,
      fetch (capWalkImage true) (capCheckAscentCleared state answer) =
        some (.base (capFlowInstruction (.jump 2095968))) := by
    intro answer
    apply cap_image_fetch _ _ 444 _ (by decide)
    · change (capCheckAscentReply state answer).pc + 4 = _
      rw [replyPC answer]
      rfl
    · rfl
  have tail : ∀ answer : BitVec 256,
      execute (capWalkImage true) (1 + (1 + (1 + fuel)))
        (capParentAnswerState (capCheckAscentPrepared state) answer) allowCoins =
      (do let result ← execute (capWalkImage true) fuel
            (capCheckAscentAnswer state answer) allowCoins
          return result.charge 3 0) := by
    intro answer
    have replyEq : capFlowState (.jump 1144)
        (capParentAnswerState (capCheckAscentPrepared state) answer) =
        capCheckAscentReply state answer := rfl
    rw [cap_flow_execute _ _ _ (enter answer), replyEq,
      show 1 + (1 + fuel) = (1 + fuel) + 1 by omega,
      execute_ordinary_step _ _ _ _ _ _ (clearFetched answer) (clearStep answer),
      cap_flow_execute _ _ _ (back answer)]
    simp only [bind_assoc, pure_bind, charge_pair, capCheckAscentAnswer, instructionCycles]
  have parent : execute (capWalkImage true) (5 + (1 + (1 + (1 + fuel))))
        (capCheckAscentPrepared state) allowCoins =
      (do let answer ← capCheckCompression (capCheckAscentQuery state node)
          let result ← execute (capWalkImage true) (1 + (1 + (1 + fuel)))
            (capParentAnswerState (capCheckAscentPrepared state) answer) allowCoins
          return result.charge 12 1) := by
    have normalized := cap_parent_execute (capCheckAscentPrepared state) (node / 2)
      preparedPC preparedRoots preparedIndex (by omega) preparedSelectors
      (1 + (1 + (1 + fuel))) allowCoins
    change execute (capWalkImage true) (5 + (1 + (1 + (1 + fuel))))
        (capCheckAscentPrepared state) allowCoins =
      (do let answer ← capCheckCompression
            (capCheckAscentQuery (capCheckAscentPrepared state) node)
          let result ← execute (capWalkImage true) (1 + (1 + (1 + fuel)))
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
  rw [show 12 + fuel = 3 + (1 + (5 + (1 + (1 + (1 + fuel))))) by omega,
    cap_advance_guard_execute true state node pc index root bounded nonroot,
    cap_navigation_image_execute true .ascend _ guardPC]
  rw [show capNavigationState .ascend (capAdvanceGuardState true state) =
    capCheckAscentPrepared state from (by unfold capCheckAscentPrepared; rfl)]
  rw [parent]
  simp_rw [tail]
  simp only [bind_assoc, pure_bind, charge_pair]

theorem cap_check_ascent_answer_index (state : MachineState) (answer : BitVec 256)
    (node : Nat) (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512) :
    (capCheckAscentAnswer state answer).getReg .x20 = BitVec.ofNat 64 (node / 2) := by
  rw [capCheckAscentAnswer, cap_flow_register, cap_check_ascent_cleared_register,
    capCheckAscentReply, cap_flow_register, cap_parent_answer_register _ _ .x20 (by decide)]
  exact cap_check_ascent_prepared_index state node index bounded

theorem cap_check_ascent_answer_register (state : MachineState) (answer : BitVec 256)
    (reg : Reg) (outside : reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x10 ∧ reg ≠ .x12) :
    (capCheckAscentAnswer state answer).getReg reg = state.getReg reg := by
  rw [capCheckAscentAnswer, cap_flow_register, cap_check_ascent_cleared_register,
    capCheckAscentReply, cap_flow_register,
    cap_parent_answer_register _ _ reg ⟨outside.2.2.1, outside.2.2.2⟩]
  exact cap_check_ascent_prepared_register state reg ⟨outside.2.1, outside.1⟩

theorem cap_check_ascent_answer_marks (state : MachineState) (node : Nat)
    (answer : BitVec 256) (marked : Nat → Bool)
    (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (roots : state.getReg .x18 = 12288) (bounded : node < 512)
    (ready : CapMarksReady state 256 0 marked) :
    CapMarksReady (capCheckAscentAnswer state answer) 256 0 marked := by
  have parent : CapMarksReady (capParentAnswerState (capCheckAscentPrepared state) answer)
      256 0 marked := by
    apply cap_parent_answer_marks _ (node / 2) answer marked
      ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
      (cap_check_ascent_prepared_index state node index bounded) (by omega)
    exact cap_marks_ready_memory state (capCheckAscentPrepared state) 256 0 marked
      (cap_check_ascent_prepared_memory state) ready
  intro mark lower upper
  rw [show (capCheckAscentAnswer state answer).getMem (capMarkAddress mark) =
      ((capParentAnswerState (capCheckAscentPrepared state) answer).setHalfword
        (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 24 + 6)) 0).getMem (capMarkAddress mark) from
      congrFun (cap_check_ascent_memory state answer node roots index bounded) _,
    clear_half_other _ _ (by omega)]
  · exact parent mark lower upper
  · intro equal
    have numeric := congrArg BitVec.toNat equal
    rw [capMarkAddress, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at numeric
    omega

/-- High input bytes survive the macro: both of its writes stay in the low root heap. -/
theorem cap_check_ascent_answer_high (state reference : MachineState) (node : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18 = 12288)
    (index : state.getReg .x20 = BitVec.ofNat 64 node) (bounded : node < 512)
    (frame : CapHighBytes (capParentAnswerState (capCheckAscentPrepared state) answer)
      reference) :
    CapHighBytes (capCheckAscentAnswer state answer) reference := by
  apply cap_high_bytes_memory
    ((capParentAnswerState (capCheckAscentPrepared state) answer).setMem
      (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 24))
      (replaceHalfword ((capParentAnswerState (capCheckAscentPrepared state) answer).getMem
        (BitVec.ofNat 64 (12288 + 32 * (node / 2) + 24))) 3 0))
    _ reference
  · rw [cap_check_ascent_memory state answer node roots index bounded]
    simp only [MachineState.setHalfword,
      (clear_half_address (12288 + 32 * (node / 2) + 24) (by omega)).1,
      (clear_half_address (12288 + 32 * (node / 2) + 24) (by omega)).2]
  · exact cap_high_bytes_store _ reference _ _ (by omega) frame

theorem cap_check_ascent_answer_root_map (state : MachineState) (answer : BitVec 256)
    (node other : Nat) (index : state.getReg .x20 = BitVec.ofNat 64 node)
    (roots : state.getReg .x18 = 12288) (bounded : node < 512) (otherBound : other < 512) :
    capReadRoot (capCheckAscentAnswer state answer) other =
      if other = node / 2 then s6Trunc answer else capReadRoot state other := by
  have parent := cap_parent_answer_root_map (capCheckAscentPrepared state) (node / 2) answer
    ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
    (cap_check_ascent_prepared_index state node index bounded) (by omega)
  unfold capReadRoot
  rw [read_buffer_memory_congr _ _ (cap_check_ascent_memory state answer node roots index bounded)]
  by_cases same : other = node / 2
  · subst other
    rw [if_pos rfl, show 12288 + 32 * (node / 2) + 24 + 6 = 12288 + 32 * (node / 2) + 30 by omega,
      read_digest_clear_top _ _ (by omega) (by omega)]
    have own := parent (node / 2) (by omega)
    rw [if_pos rfl] at own
    unfold capReadRoot at own
    rw [own]
  · rw [if_neg same, read_digest_clear_outside _ _ _ (by omega) (by omega) (by omega) (by omega)
      (by omega)]
    have rest := parent other otherBound
    rw [if_neg same] at rest
    unfold capReadRoot at rest
    rw [rest, read_buffer_memory_congr _ _ (cap_check_ascent_prepared_memory state)]

end CommitGolfCandidate
