import CommitGolfCandidate.CapCheckGroupRun

/-! Successful group handling reaches the common outer latch and preserves
its input pointers/counter. Unrelated memory words survive both storage and
duplicate paths, including rejected comparisons. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false
attribute [local irreducible] capCheckGroupStartPrefix

theorem cap_check_group_compared_register (state : MachineState) (reg : Reg) :
    (capCheckGroupCompared state).getReg reg =
      (capCheckGroupStartPrefix state 6).getReg reg := by
  unfold capCheckGroupCompared
  exact cap_check_group_branch_register _ reg

theorem cap_check_group_compared_memory (state : MachineState) :
    (capCheckGroupCompared state).mem = state.mem :=
  (cap_check_group_branch_memory _).trans
    (cap_check_group_start_memory state 6 (by decide))

theorem cap_check_group_compared_pc (state : MachineState) :
    (capCheckGroupCompared state).pc =
      if (capCheckGroupStartPrefix state 6).getReg .x6=0 then 4500 else 4448 := rfl

theorem cap_check_group_result_pc (state : MachineState)
    (passed : (capCheckGroupResult state).2=true) :
    (capCheckGroupResult state).1.pc = 4536 := by
  dsimp only [capCheckGroupResult] at passed ⊢
  split
  · rename_i absent
    apply cap_check_group_store_pc
    rw [cap_check_group_compared_pc, if_pos absent]
  · rename_i occupied
    split
    · rename_i equal
      apply cap_check_duplicate_done_pc _ _ equal
      rw [cap_check_group_compared_pc, if_neg occupied]
    · simp_all only [↓reduceIte,Bool.false_eq_true]

theorem cap_check_group_result_register (state : MachineState)
    (passed : (capCheckGroupResult state).2=true) (reg : Reg)
    (outside : reg ∉ [.x20,.x7,.x30,.x23,.x6]) :
    (capCheckGroupResult state).1.getReg reg = state.getReg reg := by
  have outside6 : reg ≠ .x6 := by simp_all
  have outside7 : reg ≠ .x7 := by simp_all
  dsimp only [capCheckGroupResult] at passed ⊢
  split
  · rw [cap_check_group_store_register _ reg outside6,
      cap_check_group_compared_register]
    exact cap_check_group_start_register state 6 (by decide) reg outside
  · split
    · rw [cap_check_duplicate_done_register _ reg outside6 outside7,
        cap_check_group_compared_register]
      exact cap_check_group_start_register state 6 (by decide) reg outside
    · simp_all only [↓reduceIte,Bool.false_eq_true]

theorem cap_check_group_result_word_frame (state : MachineState) (address : Word)
    (markOutside : address ≠ (capCheckGroupStartPrefix state 6).getReg .x30)
    (rootOutside : ∀ word : Fin 4, address ≠
      (capCheckGroupStartPrefix state 6).getReg .x23+BitVec.ofNat 64 (8*word.val)) :
    (capCheckGroupResult state).1.getMem address = state.getMem address := by
  have original : (capCheckGroupCompared state).getMem address = state.getMem address :=
    congrFun (cap_check_group_compared_memory state) address
  dsimp only [capCheckGroupResult]
  split
  · apply (cap_check_group_store_outside _ address _ _).trans original
    · simpa only [cap_check_group_compared_register] using markOutside
    · simpa only [cap_check_group_compared_register] using rootOutside
  · split
    · exact (congrFun (cap_check_duplicate_done_memory _) address).trans original
    · have same : (capCheckExitState
          (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).1 false).mem =
          (capCheckDuplicateLoop (capCheckGroupCompared state) 0 4).1.mem := rfl
      exact (congrFun same address).trans
        ((congrFun (cap_check_duplicate_loop_memory _ 0 4) address).trans original)

end CommitGolfCandidate
