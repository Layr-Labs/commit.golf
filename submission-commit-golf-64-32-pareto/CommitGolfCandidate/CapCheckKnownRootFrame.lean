import CommitGolfCandidate.CapCheckStepRoots
import CommitGolfCandidate.CapCheckValueFrame

/-! Previously collected known leaves survive every successful DFS transition.
The proof uses finalized occupancy and bounded leaf indices, not consistency
of any initial internal hash. The natural proof cursor never moves backwards. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_root_step_known (compress : Compression) (marked : Nat → Bool)
    (control : CapDfsControl) (roots : Nat → Digest) (boundary : Digest)
    (valid : CapDfsControlValid control) (leaf : Nat)
    (lower : 256≤leaf) (known : marked leaf=true) :
    capCheckRootStep compress marked control roots boundary leaf=roots leaf := by
  cases control with
  | visit node =>
    by_cases present : marked node=true
    · simp only [capCheckRootStep,if_pos present]
    · have distinct : leaf≠node := by
        intro same
        subst leaf
        exact present known
      simp only [capCheckRootStep,if_neg present,if_neg distinct]
  | advance node =>
    have distinct : leaf≠node/2 := by
      have bound := valid.2
      omega
    simp only [capCheckRootStep]
    split
    · rfl
    · exact if_neg distinct
  | done => rfl

theorem cap_check_step_cursor_monotone (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state next : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (notShort : capCheckDfsShort marked control state=false)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    (state.getReg .x25).toNat≤(next.getReg .x25).toNat := by
  have effect := cap_dfs_check_cursor_effect marked control state next
    (state.getReg .x25).toNat
    (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]) reached
  have space := cap_check_cursor_space marked control state limit ready.window
    (cap_check_dfs_not_short_enough marked control state notShort)
  have small : (state.getReg .x25).toNat+capBoundaryIncrement marked control<2^64 := by
    have bound := ready.window.limitBound
    simp only [MEMORY_BYTES] at bound
    omega
  have numeric := congrArg BitVec.toNat effect
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
  rw [numeric]
  omega

theorem cap_check_next_known_root (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (control : CapDfsControl) (state : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (above : 32768≤(state.getReg .x25).toNat)
    (leaf : Nat) (lower : 256≤leaf) (upper : leaf<512)
    (known : marked leaf=true) :
    capReadRoot (capCheckDfsNext oracle marked control state) leaf=
      capReadRoot state leaf := by
  rw [cap_check_dfs_next_roots oracle limit marked control state ready above leaf upper]
  exact cap_check_root_step_known oracle.compression marked control _ _
    ready.valid leaf lower known

theorem cap_check_next_supported (oracle : Oracle) (marked : Nat → Bool)
    (control : CapDfsControl) (state : MachineState) :
    capCheckDfsNext oracle marked control state ∈
      support (capDfsStep true marked control state) := by
  have reached := check_evaluation_support oracle (capDfsStep true marked control state)
  rw [cap_check_dfs_step_evaluation] at reached
  exact reached

theorem cap_check_value_cursor_monotone (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state : MachineState) (ready : CapCheckDfsReady limit marked control state)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    (state.getReg .x25).toNat≤
      ((capCheckDfsValue oracle marked count control state).1.getReg .x25).toNat := by
  induction count generalizing control state with
  | zero => exact le_rfl
  | succ count ih =>
    rw [capCheckDfsValue] at passed ⊢
    cases short : capCheckDfsShort marked control state
    · simp only [short,Bool.false_eq_true,↓reduceIte] at passed ⊢
      have reached := cap_check_next_supported oracle marked control state
      have nextReady := cap_check_dfs_ready_transport limit marked control state _
        ready short reached
      have progress := cap_check_step_cursor_monotone limit marked control state _
        ready short reached
      exact progress.trans (ih (capControlStep marked control)
        (capCheckDfsNext oracle marked control state) nextReady passed)
    · simp only [short,↓reduceIte] at passed
      contradiction

theorem cap_check_value_known_root (oracle : Oracle) (limit : Nat)
    (marked : Nat → Bool) (count : Nat) (control : CapDfsControl)
    (state : MachineState) (ready : CapCheckDfsReady limit marked control state)
    (above : 32768≤(state.getReg .x25).toNat)
    (leaf : Nat) (lower : 256≤leaf) (upper : leaf<512)
    (known : marked leaf=true)
    (passed : (capCheckDfsValue oracle marked count control state).2=true) :
    capReadRoot (capCheckDfsValue oracle marked count control state).1 leaf=
        capReadRoot state leaf ∧
      (state.getReg .x25).toNat≤
        ((capCheckDfsValue oracle marked count control state).1.getReg .x25).toNat := by
  induction count generalizing control state with
  | zero => exact ⟨rfl,le_rfl⟩
  | succ count ih =>
    rw [capCheckDfsValue] at passed ⊢
    cases short : capCheckDfsShort marked control state
    · simp only [short,Bool.false_eq_true,↓reduceIte] at passed ⊢
      have reached := cap_check_next_supported oracle marked control state
      have nextReady := cap_check_dfs_ready_transport limit marked control state _
        ready short reached
      have progress := cap_check_step_cursor_monotone limit marked control state _
        ready short reached
      have nextAbove := above.trans progress
      have tail := ih (capControlStep marked control)
        (capCheckDfsNext oracle marked control state) nextReady nextAbove passed
      exact ⟨tail.1.trans (cap_check_next_known_root oracle limit marked control state
        ready above leaf lower upper known),progress.trans tail.2⟩
    · simp only [short,↓reduceIte] at passed
      contradiction

end CommitGolfCandidate
