import CommitGolfCandidate.CapCheckRecordsRun

/-! A nonempty checker record always establishes the compression selectors.
These are effects of the actual lower-path setup, not assumptions about the
ABI registers. Accepted group/latch handling retains them for cap ascent. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckPathPreparedState

def CapCheckSelectors (state : MachineState) : Prop :=
  state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0

theorem cap_check_path_block_selectors (state : MachineState) (answer : BitVec 256) :
    CapCheckSelectors (capCheckPathBlockState state answer) := by
  have projected (reg : Reg) (selected : reg ∈ [Reg.x5,.x11,.x13]) :
      (capCheckPathBlockState state answer).getReg reg=
        (capCheckCompressionPrefix (capCheckPathPreparedState state) 5).getReg reg := by
    have outside : reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x29 ∧ reg ≠ .x1 := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at selected
      rcases selected with rfl | rfl | rfl <;> decide
    rw [capCheckPathBlockState,
      cap_check_path_tail_register _ reg outside,
      capCheckCompressionState,cap_compression_register]
  unfold CapCheckSelectors
  rw [projected .x5 (by decide),projected .x11 (by decide),projected .x13 (by decide)]
  simp [capCheckCompressionPrefix,capCheckCompressionInstructions,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,signExtend12]
  rfl

theorem cap_check_path_loop_selectors (state : MachineState) (count : Nat)
    (positive : 0<count) (finished : MachineState)
    (reachable : finished ∈ support (capCheckPathLoop state count)) :
    CapCheckSelectors finished := by
  induction count generalizing state with
  | zero => omega
  | succ count ih =>
    simp only [capCheckPathLoop,mem_support_bind_iff] at reachable
    obtain ⟨answer,_,tailReachable⟩ := reachable
    cases count with
    | zero =>
      simp only [capCheckPathLoop,support_pure,Set.mem_singleton_iff] at tailReachable
      subst finished
      exact cap_check_path_block_selectors state answer
    | succ count => exact ih _ (by omega) tailReachable

theorem cap_check_lower_record_selectors (state finished : MachineState)
    (reachable : finished ∈ support (capCheckLowerRecord state)) :
    CapCheckSelectors finished := by
  simp only [capCheckLowerRecord,mem_support_bind_iff] at reachable
  obtain ⟨leaf,_,pathReachable⟩ := reachable
  exact cap_check_path_loop_selectors _ 14 (by decide) finished pathReachable

theorem cap_check_record_run_selectors (state : MachineState) (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordRun state)) (passed : result.2=true) :
    CapCheckSelectors result.1 := by
  obtain ⟨lower,lowerReachable,equal⟩ :=
    (cap_check_record_run_support state result).mp reachable
  subst result
  have selectors := cap_check_lower_record_selectors state lower lowerReachable
  unfold CapCheckSelectors at selectors ⊢
  rw [cap_check_record_result_register lower passed .x5 (by decide),
    cap_check_record_result_register lower passed .x11 (by decide),
    cap_check_record_result_register lower passed .x13 (by decide)]
  exact selectors

theorem cap_check_records_run_selectors (state : MachineState) (count : Nat)
    (positive : 0<count) (result : MachineState × Bool)
    (reachable : result ∈ support (capCheckRecordsRun count state)) (passed : result.2=true) :
    CapCheckSelectors result.1 := by
  induction count generalizing state with
  | zero => omega
  | succ count ih =>
    simp only [capCheckRecordsRun,mem_support_bind_iff] at reachable
    obtain ⟨head,headReachable,tailReachable⟩ := reachable
    cases headPassed : head.2
    · simp only [headPassed,Bool.false_eq_true,↓reduceIte,support_pure,
        Set.mem_singleton_iff] at tailReachable
      subst result
      rw [headPassed] at passed
      contradiction
    · simp only [headPassed,↓reduceIte] at tailReachable
      cases count with
      | zero =>
        simp only [capCheckRecordsRun,support_pure,Set.mem_singleton_iff] at tailReachable
        subst result
        exact cap_check_record_run_selectors state head headReachable headPassed
      | succ count => exact ih head.1 (by omega) tailReachable

end CommitGolfCandidate
