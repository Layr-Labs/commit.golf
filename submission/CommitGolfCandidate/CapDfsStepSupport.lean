import CommitGolfCandidate.CapDfsStep

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_dfs_step_support (checking : Bool) (marked : Nat → Bool)
    (control : CapDfsControl) (state next : MachineState) (rootBase : Nat)
    (physical : CapDfsStateControl checking state control)
    (valid : CapDfsControlValid control) (stable : CapDfsStable checking state rootBase)
    (ready : CapMarksReady state 256 0 marked)
    (checkBase : checking = true → rootBase = 12288)
    (boundary : ∀ node, control = .visit node → marked node = false →
      CapDfsBoundaryReady checking state rootBase node)
    (reached : next ∈ support (capDfsStep checking marked control state)) :
    CapDfsStateControl checking next (capControlStep marked control) ∧
      CapDfsStable checking next rootBase ∧ CapMarksReady next 256 0 marked := by
  cases control with
  | visit node =>
      by_cases present : marked node = true
      · simp only [capDfsStep, present, ↓reduceIte] at reached
        have same := eq_of_mem_support_pure (capMarkedVisitState checking state node) reached
        subst next
        exact ⟨cap_dfs_marked_control checking state node marked physical valid stable.marks
            stable.leaves ready present,
          cap_dfs_marked_stable checking state node rootBase stable,
          cap_marks_ready_memory state _ 256 0 marked
            (cap_marked_visit_memory checking state node) ready⟩
      · have absent : marked node = false := Bool.eq_false_iff.mpr present
        have admitted := boundary node rfl absent
        cases checking
        · simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capUnknownOpenState state) reached
          subst next
          exact ⟨cap_dfs_unknown_open_control state node marked physical valid stable.marks
              ready absent,
            cap_dfs_unknown_open_stable state rootBase stable,
            cap_unknown_open_marks state node rootBase admitted.cursor marked stable.roots
              physical.2 admitted.pointer
              (by
                have bound := admitted.bound
                simp only [MEMORY_BYTES] at bound
                omega) (admitted.highOutput rfl) ready⟩
        · simp only [capDfsStep, absent, Bool.false_eq_true, ↓reduceIte] at reached
          have same := eq_of_mem_support_pure (capUnknownCheckState state) reached
          subst next
          have roots : state.getReg .x18 = 12288 := by
            change state.getReg .x18 = BitVec.ofNat 64 12288
            simpa only [checkBase rfl, capBoundaryRootRegister, ↓reduceIte] using stable.roots
          have small : admitted.limit < 2^64 := by
            have bound := admitted.limitBound rfl
            simp only [MEMORY_BYTES] at bound
            omega
          exact ⟨cap_dfs_unknown_check_control state node admitted.cursor admitted.limit
              marked physical valid stable.marks ready absent admitted.pointer
              (admitted.proofEnd rfl) (by have enough := admitted.enough rfl; omega)
              small (admitted.enough rfl),
            cap_dfs_unknown_check_stable state rootBase stable,
            cap_unknown_check_marks state node admitted.cursor marked roots physical.2
              valid.2 admitted.pointer ready⟩
  | advance node =>
      by_cases root : node = 1
      · simp only [capDfsStep, if_pos root] at reached
        have same := eq_of_mem_support_pure (capAdvanceRootState checking state) reached
        subst next
        subst node
        refine ⟨cap_dfs_root_control checking state marked physical stable.root, ?_, ?_⟩
        · apply cap_dfs_stable_transport checking state _ rootBase stable
          intro reg _
          exact cap_flow_register _ _ reg
        · exact cap_marks_ready_memory state _ 256 0 marked
            (cap_flow_memory _ _) ready
      · by_cases even : node % 2 = 0
        · simp only [capDfsStep, if_neg root, if_pos even] at reached
          have same := eq_of_mem_support_pure (capAdvanceSiblingState checking state) reached
          subst next
          exact ⟨cap_dfs_sibling_control checking state node marked physical valid stable.root
              root even, cap_dfs_sibling_stable checking state rootBase stable,
            cap_marks_ready_memory state _ 256 0 marked
              (cap_advance_sibling_memory checking state) ready⟩
        · cases checking
          · simp only [capDfsStep, if_neg root, if_neg even, Bool.false_eq_true,
              ↓reduceIte] at reached
            have same := eq_of_mem_support_pure (capAdvanceOpenAscentState state) reached
            subst next
            exact ⟨cap_dfs_open_ascent_control state node marked physical valid stable.root
                root even, cap_dfs_open_ascent_stable state rootBase stable,
              cap_marks_ready_memory state _ 256 0 marked
                (cap_advance_open_ascent_memory state) ready⟩
          · simp only [capDfsStep, if_neg root, if_neg even, ↓reduceIte] at reached
            obtain ⟨answer, _, returned⟩ := mem_support_bind_peel _ _ reached
            have same := eq_of_mem_support_pure (capCheckAscentAnswer state answer) returned
            subst next
            have roots : state.getReg .x18 = 12288 := by
              change state.getReg .x18 = BitVec.ofNat 64 12288
              simpa only [checkBase rfl, capBoundaryRootRegister, ↓reduceIte] using stable.roots
            exact ⟨cap_dfs_check_ascent_control state node marked answer physical valid
                stable.root root even,
              cap_dfs_check_ascent_stable state answer rootBase stable,
              cap_check_ascent_answer_marks state node answer marked physical.2 roots
                valid.2 ready⟩
  | done =>
      have same := eq_of_mem_support_pure state reached
      subst next
      exact ⟨physical, stable, ready⟩

end CommitGolfCandidate
