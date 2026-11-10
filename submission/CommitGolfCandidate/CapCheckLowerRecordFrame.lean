import CommitGolfCandidate.CapCheckLowerRecord
import CommitGolfCandidate.CapCheckRecordLeafWords
import CommitGolfCandidate.CapCheckPathFrame

/-! All-reply outcomes of a complete lower record. Value and proof cursors
advance by 256 and 576 bytes respectively; the loaded index is divided by
2^17. Every root, occupancy word and admitted high input survives the macro. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capCheckPathInitPrefix

theorem cap_check_path_init_state_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x29) :
    (capCheckPathInitState state).getReg reg = state.getReg reg := by
  unfold capCheckPathInitState
  rw [MachineState.getReg_setPC]
  exact cap_check_path_init_register state 3 (by decide) reg outside

theorem cap_check_lower_record_register (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLowerRecord state)) (reg : Reg)
    (outside : reg ∉ [.x20,.x6,.x7,.x25,.x1,.x28,.x29,
      .x5,.x8,.x10,.x11,.x12,.x13]) :
    finished.getReg reg = state.getReg reg := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  rw [cap_check_path_loop_register_frame _ 17 finished pathReachable reg (by simp_all),
    cap_check_path_init_state_register leaf reg (by simp_all)]
  exact cap_check_record_leaf_register state leaf leafReachable reg (by simp_all)

theorem cap_check_lower_record_source (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    finished.getReg .x8 = state.getReg .x8+256 := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  rw [cap_check_path_loop_register_frame _ 17 finished pathReachable .x8 (by decide),
    cap_check_path_init_state_register leaf .x8 (by decide)]
  exact cap_check_record_leaf_source state leaf leafReachable

theorem cap_check_lower_record_cursor (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    finished.getReg .x25 = state.getReg .x25+576 := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  rw [cap_check_path_loop_cursor _ 17 finished pathReachable,
    cap_check_path_init_state_register leaf .x25 (by decide),
    cap_check_record_leaf_cursor state leaf leafReachable, BitVec.add_assoc]
  rfl

theorem cap_check_lower_record_node (state finished : MachineState) (index : Nat)
    (small : index < 2^64)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 index)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    finished.getReg .x20 = BitVec.ofNat 64 (index/2^17) := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  apply cap_check_path_loop_node _ 17 index small _ finished pathReachable
  rw [cap_check_path_init_state_register leaf .x20 (by decide),
    cap_check_record_leaf_index state leaf leafReachable]
  exact loaded

theorem cap_check_lower_record_finished (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    finished.pc = 4420 ∧ finished.getReg .x29 = 0 := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, _, pathReachable⟩ := reachable
  have counter : (capCheckPathInitState leaf).getReg .x29 = BitVec.ofNat 64 17 := by
    unfold capCheckPathInitState
    rw [MachineState.getReg_setPC, cap_check_path_init_counter]
    rfl
  have result := cap_check_path_loop_finished _ 17 (by decide) counter finished pathReachable
  exact ⟨result.2 (by decide),result.1⟩

theorem cap_check_lower_record_word_frame (state finished : MachineState)
    (scratch : state.getReg .x21 = 256)
    (reachable : finished ∈ support (capCheckLowerRecord state))
    (address : Word) (outside : ∀ i < 8,
      address ≠ BitVec.ofNat 64 (256+8*i)) :
    finished.getMem address = state.getMem address := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  have pathScratch : (capCheckPathInitState leaf).getReg .x21 = 256 := by
    rw [cap_check_path_init_state_register leaf .x21 (by decide),
      cap_check_record_leaf_register state leaf leafReachable .x21 (by decide)]
    exact scratch
  have pathFrame := cap_check_path_loop_word_frame _ 17 pathScratch finished pathReachable
    address outside
  have initFrame := congrFun (cap_check_path_init_memory leaf) address
  exact pathFrame.trans (initFrame.trans
    (cap_check_record_leaf_word_frame state leaf scratch leafReachable address outside))

theorem cap_check_lower_record_high_frame (state reference finished : MachineState)
    (scratch : state.getReg .x21 = 256) (frame : CapHighBytes state reference)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    CapHighBytes finished reference := by
  simp only [capCheckLowerRecord, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReachable, pathReachable⟩ := reachable
  have leafFrame := cap_check_record_leaf_high_frame state reference leaf scratch frame leafReachable
  have pathFrame := cap_high_bytes_memory _ _ _
    (cap_check_path_init_memory leaf) leafFrame
  have pathScratch : (capCheckPathInitState leaf).getReg .x21 = 256 := by
    rw [cap_check_path_init_state_register leaf .x21 (by decide),
      cap_check_record_leaf_register state leaf leafReachable .x21 (by decide)]
    exact scratch
  exact cap_check_path_loop_high_frame _ reference 17 pathScratch finished pathReachable pathFrame

end CommitGolfCandidate
