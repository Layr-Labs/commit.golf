import CommitGolfCandidate.CapCheckDfsRun

/-! Successful cap traversal preserves the claimed commitment pointer and all
high ABI input bytes. Parent replies overwrite only a bounded low root slot;
unknown proof copies also write only the low heap. Arbitrary replies remain
allowed, and no frame is inferred from phase success alone without readiness. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_ascent_high (state reference : MachineState) (node : Nat)
    (answer : BitVec 256) (roots : state.getReg .x18=12288)
    (index : state.getReg .x20=BitVec.ofNat 64 node) (bounded : node<512)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capCheckAscentAnswer state answer) reference := by
  apply cap_check_ascent_answer_high state reference node answer roots index bounded
  apply cap_parent_answer_high (capCheckAscentPrepared state) reference (node/2) answer
    ((cap_check_ascent_prepared_register state .x18 (by decide)).trans roots)
    (cap_check_ascent_prepared_index state node index bounded) (by omega)
  exact cap_high_bytes_memory state (capCheckAscentPrepared state) reference
    (cap_check_ascent_prepared_memory state) frame

theorem cap_dfs_check_step_high (limit : Nat) (marked : Nat → Bool)
    (control : CapDfsControl) (state next reference : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (frame : CapHighBytes state reference)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    CapHighBytes next reference := by
  cases control with
  | visit node =>
      by_cases present : marked node=true
      · simp only [capDfsStep,present,↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState true state node) reached
        subst next
        exact cap_high_bytes_memory state _ reference
          (cap_marked_visit_memory true state node) frame
      · have absent := Bool.eq_false_iff.mpr present
        simp only [capDfsStep,absent,↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownCheckState state) reached
        subst next
        apply cap_unknown_check_high state reference node (state.getReg .x25).toNat
          (by simpa [capBoundaryRootRegister] using ready.stable.roots)
          ready.physical.2 ready.valid.2
          (by simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]) frame
  | advance node =>
      by_cases root : node=1
      · simp only [capDfsStep,if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState true state) reached
        subst next
        exact cap_high_bytes_memory state _ reference (cap_flow_memory _ _) frame
      · by_cases even : node%2=0
        · simp only [capDfsStep,if_neg root,if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState true state) reached
          subst next
          exact cap_high_bytes_memory state _ reference
            (cap_advance_sibling_memory true state) frame
        · simp only [capDfsStep,if_neg root,if_neg even,↓reduceIte] at reached
          obtain ⟨answer,_,returned⟩ := mem_support_bind_peel _ _ reached
          have same := eq_of_mem_support_pure (capCheckAscentAnswer state answer) returned
          subst next
          exact cap_check_ascent_high state reference node answer
            (by simpa [capBoundaryRootRegister] using ready.stable.roots)
            ready.physical.2 ready.valid.2 frame
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      exact frame

theorem cap_dfs_check_commitment_pointer (marked : Nat → Bool) (control : CapDfsControl)
    (state next : MachineState)
    (reached : next ∈ support (capDfsStep true marked control state)) :
    next.getReg .x26=state.getReg .x26 := by
  cases control with
  | visit node =>
      by_cases present : marked node=true
      · simp only [capDfsStep,present,↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState true state node) reached
        subst next
        rw [capMarkedVisitState,cap_known_state_register true _ node .x26 (by decide)]
        exact cap_marked_prepare_register true state .x26 (by decide)
      · have absent := Bool.eq_false_iff.mpr present
        simp only [capDfsStep,absent,↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capUnknownCheckState state) reached
        subst next
        exact cap_unknown_check_register state .x26 (by decide)
  | advance node =>
      by_cases root : node=1
      · simp only [capDfsStep,if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState true state) reached
        subst next
        exact cap_flow_register _ _ .x26
      · by_cases even : node%2=0
        · simp only [capDfsStep,if_neg root,if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState true state) reached
          subst next
          rw [capAdvanceSiblingState,cap_flow_register,
            cap_navigation_register _ _ .x26 (by decide)]
          exact cap_advance_guard_register true state .x26 (by decide)
        · simp only [capDfsStep,if_neg root,if_neg even,↓reduceIte] at reached
          obtain ⟨answer,_,returned⟩ := mem_support_bind_peel _ _ reached
          have same := eq_of_mem_support_pure (capCheckAscentAnswer state answer) returned
          subst next
          exact cap_check_ascent_answer_register state answer .x26 (by decide)
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      rfl

theorem cap_check_dfs_run_high (limit : Nat) (marked : Nat → Bool)
    (count : Nat) (control : CapDfsControl) (state reference : MachineState)
    (ready : CapCheckDfsReady limit marked control state)
    (frame : CapHighBytes state reference) (result : MachineState × Bool)
    (reached : result ∈ support (capCheckDfsRun marked count control state))
    (passed : result.2=true) :
    CapHighBytes result.1 reference ∧ result.1.getReg .x26=state.getReg .x26 := by
  induction count generalizing control state with
  | zero =>
      simp only [capCheckDfsRun,support_pure,Set.mem_singleton_iff] at reached
      subst result
      exact ⟨frame,rfl⟩
  | succ count ih =>
      rw [capCheckDfsRun] at reached
      cases short : capCheckDfsShort marked control state
      · simp only [short,Bool.false_eq_true,↓reduceIte,mem_support_bind_iff] at reached
        obtain ⟨next,nextReached,tailReached⟩ := reached
        have nextReady := cap_check_dfs_ready_transport limit marked control state next
          ready short nextReached
        have nextFrame := cap_dfs_check_step_high limit marked control state next
          reference ready frame nextReached
        have tail := ih (capControlStep marked control) next nextReady nextFrame tailReached
        exact ⟨tail.1,tail.2.trans
          (cap_dfs_check_commitment_pointer marked control state next nextReached)⟩
      · simp only [short,↓reduceIte,support_pure,Set.mem_singleton_iff] at reached
        subst result
        contradiction

end CommitGolfCandidate
