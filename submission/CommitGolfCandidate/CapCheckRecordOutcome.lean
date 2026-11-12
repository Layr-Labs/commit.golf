import CommitGolfCandidate.CapCheckRecordRun

/-! Accepted record outcomes preserve the outer-loop inputs, advance the three
input cursors and decrement the positive remaining count. These are support
facts for arbitrary oracle replies; digest/map consistency is proved separately. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckRecordNextPrefix

theorem cap_check_record_result_state (lower : MachineState)
    (passed : (capCheckRecordResult lower).2 = true) :
    (capCheckRecordResult lower).1 =
      capCheckRecordNextPrefix (capCheckGroupResult lower).1 3 := by
  have groupPassed := (cap_check_record_result_passed lower).symm.trans passed
  simp only [capCheckRecordResult,groupPassed,↓reduceIte]

theorem cap_check_record_result_register (lower : MachineState)
    (passed : (capCheckRecordResult lower).2 = true) (reg : Reg)
    (outside : reg ∉ [.x20,.x7,.x30,.x23,.x6,.x24,.x27]) :
    (capCheckRecordResult lower).1.getReg reg = lower.getReg reg := by
  rw [cap_check_record_result_state lower passed,
    cap_check_record_next_register _ reg (by simp_all) (by simp_all)]
  exact cap_check_group_result_register lower
    ((cap_check_record_result_passed lower).symm.trans passed) reg (by simp_all)

theorem cap_check_record_result_index (lower : MachineState)
    (passed : (capCheckRecordResult lower).2 = true) :
    (capCheckRecordResult lower).1.getReg .x24 = lower.getReg .x24+8 := by
  rw [cap_check_record_result_state lower passed,
    (cap_check_record_next_projection _).1,
    cap_check_group_result_register lower
      ((cap_check_record_result_passed lower).symm.trans passed) .x24 (by decide)]

theorem cap_check_record_result_counter (lower : MachineState) (remaining : Nat)
    (positive : 0 < remaining)
    (counter : lower.getReg .x27 = BitVec.ofNat 64 remaining)
    (passed : (capCheckRecordResult lower).2 = true) :
    (capCheckRecordResult lower).1.getReg .x27 = BitVec.ofNat 64 (remaining-1) := by
  rw [cap_check_record_result_state lower passed]
  apply cap_check_record_next_counter _ remaining positive
  rw [cap_check_group_result_register lower
    ((cap_check_record_result_passed lower).symm.trans passed) .x27 (by decide)]
  exact counter

theorem cap_check_record_result_pc (lower : MachineState) (remaining : Nat)
    (positive : 0 < remaining) (bounded : remaining < 2^64)
    (counter : lower.getReg .x27 = BitVec.ofNat 64 remaining)
    (passed : (capCheckRecordResult lower).2 = true) :
    (capCheckRecordResult lower).1.pc = if remaining=1 then 4548 else 4212 := by
  have groupPassed := (cap_check_record_result_passed lower).symm.trans passed
  rw [cap_check_record_result_state lower passed]
  apply cap_check_record_next_exit _ remaining
    (cap_check_group_result_pc lower groupPassed) positive bounded
  rw [cap_check_group_result_register lower groupPassed .x27 (by decide)]
  exact counter

theorem cap_check_record_run_register (state : MachineState) (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2 = true) (reg : Reg)
    (outside : reg ∉ [.x20,.x6,.x7,.x25,.x1,.x28,.x29,.x5,
      .x8,.x10,.x11,.x12,.x13,.x30,.x23,.x24,.x27]) :
    result.1.getReg reg = state.getReg reg := by
  obtain ⟨lower, lowerReachable, equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  rw [cap_check_record_result_register lower passed reg (by simp_all)]
  exact cap_check_lower_record_register state lower lowerReachable reg (by simp_all)

theorem cap_check_record_run_cursors (state : MachineState) (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2 = true) :
    result.1.getReg .x8 = state.getReg .x8+256 ∧
    result.1.getReg .x25 = state.getReg .x25+544 ∧
    result.1.getReg .x24 = state.getReg .x24+8 := by
  obtain ⟨lower, lowerReachable, equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  constructor
  · rw [cap_check_record_result_register lower passed .x8 (by decide)]
    exact cap_check_lower_record_source state lower lowerReachable
  constructor
  · rw [cap_check_record_result_register lower passed .x25 (by decide)]
    exact cap_check_lower_record_cursor state lower lowerReachable
  · rw [cap_check_record_result_index lower passed,
      cap_check_lower_record_register state lower lowerReachable .x24 (by decide)]

theorem cap_check_record_run_control (state : MachineState) (result : MachineState × Bool)
    (remaining : Nat) (positive : 0 < remaining) (bounded : remaining < 2^64)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining)
    (reachable : result ∈ support (capCheckRecordRun state))
    (passed : result.2 = true) :
    result.1.getReg .x27 = BitVec.ofNat 64 (remaining-1) ∧
    result.1.pc = if remaining=1 then 4548 else 4212 := by
  obtain ⟨lower, lowerReachable, equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  have lowerCounter : lower.getReg .x27 = BitVec.ofNat 64 remaining := by
    rw [cap_check_lower_record_register state lower lowerReachable .x27 (by decide)]
    exact counter
  exact ⟨cap_check_record_result_counter lower remaining positive lowerCounter passed,
    cap_check_record_result_pc lower remaining positive bounded lowerCounter passed⟩

end CommitGolfCandidate
