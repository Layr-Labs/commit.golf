import CommitGolfCandidate.CapDfsCursorEffect

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapOpenCursorWindow (limit : Nat) (control : CapDfsControl)
    (state : MachineState) : Prop :=
  ∃ cursor : Nat, state.getReg .x25 = BitVec.ofNat 64 cursor ∧
    cursor % 8 = 0 ∧ 32768 ≤ cursor ∧
    cursor + 32 * (1022 - capControlRank control) ≤ limit

theorem cap_open_cursor_initial (limit cursor : Nat) (control : CapDfsControl)
    (state : MachineState) (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (high : 32768 ≤ cursor)
    (space : cursor + 32 * 1022 ≤ limit) :
    CapOpenCursorWindow limit control state := by
  refine ⟨cursor, pointer, aligned, high, ?_⟩
  have residual : 1022 - capControlRank control ≤ 1022 := Nat.sub_le _ _
  omega

theorem cap_open_cursor_transport (marked : Nat → Bool) (limit : Nat)
    (control : CapDfsControl) (state next : MachineState)
    (valid : CapDfsControlValid control)
    (window : CapOpenCursorWindow limit control state)
    (reached : next ∈ support (capDfsStep false marked control state)) :
    CapOpenCursorWindow limit (capControlStep marked control) next := by
  obtain ⟨cursor, pointer, aligned, high, space⟩ := window
  by_cases done : control = .done
  · subst control
    have same := eq_of_mem_support_pure state reached
    subst next
    exact ⟨cursor, pointer, aligned, high, space⟩
  · have progress := cap_control_step_progress marked control valid done
    have currentBound := cap_control_rank_bounded control valid
    have nextBound := cap_control_rank_bounded (capControlStep marked control)
      (cap_control_step_valid marked control valid)
    have increment := cap_boundary_increment_bound marked control
    have incrementAligned := cap_boundary_increment_aligned marked control
    refine ⟨cursor + capBoundaryIncrement marked control,
      cap_dfs_open_cursor_effect marked control state next cursor pointer reached, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega

noncomputable def cap_open_boundary_ready (marked : Nat → Bool)
    (rootBase limit : Nat) (control : CapDfsControl) (state : MachineState)
    (valid : CapDfsControlValid control)
    (window : CapOpenCursorWindow limit control state)
    (limitBound : limit ≤ MEMORY_BYTES)
    (rootBound : rootBase + 16384 ≤ MEMORY_BYTES)
    (rootAligned : rootBase % 8 = 0)
    (node : Nat) (atNode : control = .visit node) :
    CapDfsBoundaryReady false state rootBase node := by
  let cursor := Classical.choose window
  have facts := Classical.choose_spec window
  have unfinished : control ≠ .done := by
    rw [atNode]
    exact CapDfsControl.noConfusion
  have before := cap_control_rank_before_done control valid unfinished
  have nodeBound : node < 512 := by
    rw [atNode] at valid
    exact valid.2
  refine {
    cursor := cursor
    pointer := facts.1
    aligned := facts.2.1
    bound := ?_
    rootBound := ?_
    rootAligned := rootAligned
    limit := limit
    proofEnd := ?_
    limitBound := ?_
    enough := ?_
    highOutput := ?_
  }
  · have space := facts.2.2.2
    omega
  · omega
  · intro impossible
    contradiction
  · intro impossible
    contradiction
  · intro impossible
    contradiction
  · intro _
    exact facts.2.2.1

end CommitGolfCandidate
