import CommitGolfCandidate.ChainedCheckerAdmission

section

/-! Actual mark-table initialization and the bounded zeroing loop. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerMarksInitOps : List Instr :=
  [.ADDI .x4 .x0 1,.SLLI .x4 .x4 12,.ADDI .x2 .x4 0,.ADDI .x30 .x0 512]
@[irreducible] def checkerMarksInitPrefix (n : Nat) (s : MachineState) : MachineState :=
  (checkerMarksInitOps.take n).foldl execInstrBr s
theorem checker_marks_init_zero (s : MachineState) : checkerMarksInitPrefix 0 s=s := by rw [checkerMarksInitPrefix]; rfl
theorem checker_marks_init_succ (n : Nat) (s : MachineState) (small : n<4) :
    checkerMarksInitPrefix (n+1) s=execInstrBr (checkerMarksInitPrefix n s) (checkerMarksInitOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerMarksInitPrefix <;> rfl
theorem checker_marks_init_at : OpsAt chainedCheckerImage (4096+4*24) checkerMarksInitOps :=
  chained_checker_slice_at 24 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_marks_init_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x4,.x30]) :
    (checkerMarksInitPrefix 4 s).getReg reg=s.getReg reg := by
  rw [checkerMarksInitPrefix]
  cases reg <;> simp at kept <;> rfl
theorem checker_marks_init_memory (s : MachineState) (query : Word) :
    (checkerMarksInitPrefix 4 s).getMem query=s.getMem query := by rw [checkerMarksInitPrefix]; rfl
theorem checker_marks_init_base (s : MachineState) : (checkerMarksInitPrefix 4 s).getReg .x4=4096#64 := by
  rw [checkerMarksInitPrefix]; rfl
theorem checker_marks_init_pointer (s : MachineState) : (checkerMarksInitPrefix 4 s).getReg .x2=4096#64 := by
  rw [checkerMarksInitPrefix]; rfl
theorem checker_marks_init_count (s : MachineState) : (checkerMarksInitPrefix 4 s).getReg .x30=512#64 := by
  rw [checkerMarksInitPrefix]; rfl
theorem checker_marks_init_pc (n : Nat) (s : MachineState) (small : n≤4) :
    (checkerMarksInitPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_marks_init_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_marks_init_succ n s (by omega)]
    have step (t : MachineState) (i : Fin 4) : (execInstrBr t (checkerMarksInitOps.getD i.val .EBREAK)).pc=t.pc+4 := by fin_cases i <;> rfl
    rw [step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]; congr 1
theorem checker_marks_init_execution (s : MachineState) (pc : s.pc=4096+4*24) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerMarksInitPrefix 4 s) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_marks_init_zero s]
  apply execute_unit_steps (states := fun n => checkerMarksInitPrefix n s)
  intro i inside
  refine ⟨.base (checkerMarksInitOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_marks_init_at i inside
    rw [checker_marks_init_pc i s (by omega),pc]
  · rw [checker_marks_init_succ i s inside]; interval_cases i <;> rfl
  · interval_cases i <;> rfl

def checkerClearOps : List Instr :=
  [.SD .x2 .x0 0,.ADDI .x2 .x2 8,.ADDI .x30 .x30 4095,.BNE .x30 .x0 8180]
@[irreducible] def checkerClearPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerClearOps.getD index .EBREAK)) n
theorem checker_clear_zero (s : MachineState) : checkerClearPrefix 0 s=s := by rw [checkerClearPrefix]; rfl
theorem checker_clear_succ (n : Nat) (s : MachineState) (small : n<4) :
    checkerClearPrefix (n+1) s=execInstrBr (checkerClearPrefix n s) (checkerClearOps.getD n .EBREAK) := by
  unfold checkerClearPrefix
  rfl
theorem checker_clear_at : OpsAt chainedCheckerImage (4096+4*28) checkerClearOps :=
  chained_checker_slice_at 28 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
private theorem merged_ChainedCheckerMarksClear_clear_guard_register (s : MachineState) (reg : Reg) :
    (execInstrBr s (.BNE .x30 .x0 8180)).getReg reg=s.getReg reg := by
  change (if _ then s.setPC _ else s.setPC _).getReg reg=_
  split <;> exact MachineState.getReg_setPC
private theorem merged_ChainedCheckerMarksClear_clear_guard_memory (s : MachineState) (query : Word) :
    (execInstrBr s (.BNE .x30 .x0 8180)).getMem query=s.getMem query := by
  change (if _ then s.setPC _ else s.setPC _).getMem query=_
  split <;> exact MachineState.getMem_setPC
theorem checker_clear_pointer (s : MachineState) : (checkerClearPrefix 4 s).getReg .x2=s.getReg .x2+8 := by
  rw [checker_clear_succ 3 s (by decide)]
  change (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).getReg .x2=_
  rw [merged_ChainedCheckerMarksClear_clear_guard_register,checkerClearPrefix]
  rfl
theorem checker_clear_counter (s : MachineState) : (checkerClearPrefix 4 s).getReg .x30=s.getReg .x30-1 := by
  rw [checker_clear_succ 3 s (by decide)]
  change (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).getReg .x30=_
  rw [merged_ChainedCheckerMarksClear_clear_guard_register,checkerClearPrefix]
  change s.getReg .x30+signExtend12 4095=_
  rw [BitVec.sub_eq_add_neg]
  rfl
theorem checker_clear_register (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x30]) :
    (checkerClearPrefix 4 s).getReg reg=s.getReg reg := by
  rw [checker_clear_succ 3 s (by decide)]
  change (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).getReg reg=_
  rw [merged_ChainedCheckerMarksClear_clear_guard_register,checkerClearPrefix]
  cases reg <;> simp at kept <;> rfl
theorem checker_clear_memory (s : MachineState) (query : Word) :
    (checkerClearPrefix 4 s).getMem query=if query=s.getReg .x2 then 0#64 else s.getMem query := by
  rw [checker_clear_succ 3 s (by decide)]
  change (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).getMem query=_
  rw [merged_ChainedCheckerMarksClear_clear_guard_memory,checkerClearPrefix]
  change (if query==s.getReg .x2+signExtend12 0 then 0#64 else s.mem query)=_
  simp only [show signExtend12 0=0#64 by rfl,BitVec.add_zero,beq_iff_eq,MachineState.getMem]
theorem checker_clear_prefix_pc (n : Nat) (s : MachineState) (small : n≤3) :
    (checkerClearPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> rw [checkerClearPrefix]
  · exact (BitVec.add_zero _).symm
  · rfl
  · change s.pc+4+4=s.pc+8
    rw [BitVec.add_assoc]; rfl
  · change s.pc+4+4+4=s.pc+12
    simp only [BitVec.add_assoc]; rfl
theorem checker_clear_execution (s : MachineState) (pc : s.pc=4096+4*28)
    (valid : accessValid (s.getReg .x2) 8=true) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerClearPrefix 4 s) coins
          return result.charge 4 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_clear_zero s]
  apply execute_unit_steps (states := fun n => checkerClearPrefix n s)
  intro i inside
  refine ⟨.base (checkerClearOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_clear_at i inside
    rw [checker_clear_prefix_pc i s (by omega),pc]
  · rw [checker_clear_succ i s inside]
    interval_cases i
    · change (if accessValid ((checkerClearPrefix 0 s).getReg .x2+0) 8 then _ else _)=_
      rw [checker_clear_zero]
      exact ite_eq_left (by simpa using valid)
    all_goals rfl
  · interval_cases i <;> rfl

@[irreducible] def checkerClearRows : Nat → MachineState → MachineState
  | 0,s => s
  | count+1,s => checkerClearRows count (checkerClearPrefix 4 s)
theorem checker_clear_rows_zero (s : MachineState) : checkerClearRows 0 s=s := by rw [checkerClearRows]
theorem checker_clear_rows_succ (count : Nat) (s : MachineState) :
    checkerClearRows (count+1) s=checkerClearRows count (checkerClearPrefix 4 s) := by rw [checkerClearRows]
theorem checker_clear_rows_register (count : Nat) (s : MachineState) (reg : Reg) (kept : reg∉[.x2,.x30]) :
    (checkerClearRows count s).getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero => rw [checker_clear_rows_zero]
  | succ count ih => rw [checker_clear_rows_succ,ih,checker_clear_register s reg kept]
theorem checker_clear_rows_memory_frame (count : Nat) (s : MachineState) (query : Word)
    (away : ∀ index, index<count → query≠s.getReg .x2+BitVec.ofNat 64 (8*index)) :
    (checkerClearRows count s).getMem query=s.getMem query := by
  induction count generalizing s with
  | zero => rw [checker_clear_rows_zero]
  | succ count ih =>
    rw [checker_clear_rows_succ,ih,checker_clear_memory,ite_eq_right]
    · simpa using away 0 (by omega)
    · intro index inside
      rw [checker_clear_pointer]
      change query≠s.getReg .x2+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*index)
      rw [byte_offset_add]
      convert away (index+1) (by omega) using 1 <;> congr 2 <;> omega

end CommitGolfCandidate.Chained.Native

end

section

/-! Execution and memory content of all 512 mark-zeroing iterations. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

theorem checker_clear_next_count (s : MachineState) (count : Nat)
    (input : s.getReg .x30=BitVec.ofNat 64 (count+1)) :
    (checkerClearPrefix 4 s).getReg .x30=BitVec.ofNat 64 count := by
  rw [checker_clear_counter,input]
  change BitVec.ofNat 64 (count+1)-BitVec.ofNat 64 1=_
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),Nat.add_sub_cancel]
theorem checker_clear_next_pc (s : MachineState) (count : Nat) (small : count<512)
    (pc : s.pc=4096+4*28) (input : s.getReg .x30=BitVec.ofNat 64 (count+1)) :
    (checkerClearPrefix 4 s).pc=if count=0 then 4096+4*32 else 4096+4*28 := by
  have counter : (checkerClearPrefix 3 s).getReg .x30=BitVec.ofNat 64 count := by
    have same : (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).getReg .x30=
        (checkerClearPrefix 3 s).getReg .x30 := by
      change (if _ then (checkerClearPrefix 3 s).setPC _ else (checkerClearPrefix 3 s).setPC _).getReg .x30=_
      split <;> exact MachineState.getReg_setPC
    have result := checker_clear_next_count s count input
    rw [checker_clear_succ 3 s (by decide)] at result
    exact same.symm.trans result
  rw [checker_clear_succ 3 s (by decide)]
  change (execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)).pc=_
  by_cases last : count=0
  · have same : execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)=
        (checkerClearPrefix 3 s).setPC ((checkerClearPrefix 3 s).pc+4) := by
      apply ite_eq_right
      change ¬((checkerClearPrefix 3 s).getReg .x30 != 0#64)=true
      rw [counter,last]
      decide
    rw [same]
    change (checkerClearPrefix 3 s).pc+4=_
    rw [checker_clear_prefix_pc 3 s (by decide),pc,ite_eq_left last]
    rfl
  · have different : BitVec.ofNat 64 count≠0#64 := word_of_nat_ne count 0 (by omega) (by decide) last
    have same : execInstrBr (checkerClearPrefix 3 s) (.BNE .x30 .x0 8180)=
        (checkerClearPrefix 3 s).setPC ((checkerClearPrefix 3 s).pc+signExtend13 8180) := by
      apply ite_eq_left
      change ((checkerClearPrefix 3 s).getReg .x30 != 0#64)=true
      rw [counter]
      exact bne_iff_ne.mpr different
    rw [same]
    change (checkerClearPrefix 3 s).pc+signExtend13 8180=_
    rw [checker_clear_prefix_pc 3 s (by decide),pc,ite_eq_right last]
    rfl

theorem checker_clear_rows_pointer (count : Nat) (s : MachineState) :
    (checkerClearRows count s).getReg .x2=s.getReg .x2+BitVec.ofNat 64 (8*count) := by
  induction count generalizing s with
  | zero => rw [checker_clear_rows_zero]; exact (BitVec.add_zero _).symm
  | succ count ih =>
    rw [checker_clear_rows_succ,ih,checker_clear_pointer]
    change s.getReg .x2+BitVec.ofNat 64 8+BitVec.ofNat 64 (8*count)=_
    rw [byte_offset_add]
    congr 2
    omega
theorem checker_clear_rows_execution (count base : Nat) (s : MachineState) (small : count≤512)
    (pc : s.pc=if count=0 then 4096+4*32 else 4096+4*28)
    (pointer : s.getReg .x2=BitVec.ofNat 64 base) (aligned : base%8=0)
    (room : base+8*count≤8192) (counter : s.getReg .x30=BitVec.ofNat 64 count)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (4*count+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerClearRows count s) coins
          return result.charge (4*count) 0) := by
  induction count generalizing s base with
  | zero => simp [checker_clear_rows_zero,Execution.charge]
  | succ count ih =>
    have headPC : s.pc=4096+4*28 := by simpa using pc
    have valid : accessValid (s.getReg .x2) 8=true := by
      rw [pointer]
      have fit : base<2^64 := by omega
      simp [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fit,MEMORY_BYTES,aligned]
      omega
    have nextPointer : (checkerClearPrefix 4 s).getReg .x2=BitVec.ofNat 64 (base+8) := by
      rw [checker_clear_pointer,pointer]
      exact (BitVec.ofNat_add _ _).symm
    rw [show 4*(count+1)+fuel=4+(4*count+fuel) by omega,checker_clear_execution s headPC valid,
      ih (base+8) _ (by omega) (checker_clear_next_pc s count (by omega) headPC counter) nextPointer
        (by omega) (by omega) (checker_clear_next_count s count counter),←checker_clear_rows_succ]
    simp [Execution.charge,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem checker_clear_rows_content (count base : Nat) (s : MachineState)
    (pointer : s.getReg .x2=BitVec.ofNat 64 base) (room : base+8*count≤8192) :
    ∀ node, node<count → (checkerClearRows count s).getMem (BitVec.ofNat 64 (base+8*node))=0#64 := by
  induction count generalizing s base with
  | zero => intro node inside; omega
  | succ count ih =>
    intro node inside
    rw [checker_clear_rows_succ]
    have nextPointer : (checkerClearPrefix 4 s).getReg .x2=BitVec.ofNat 64 (base+8) := by
      rw [checker_clear_pointer,pointer]
      exact (BitVec.ofNat_add _ _).symm
    cases node with
    | zero =>
      rw [checker_clear_rows_memory_frame]
      · rw [checker_clear_memory,pointer]
        simp
      · intro index before
        rw [nextPointer,←BitVec.ofNat_add]
        apply word_of_nat_ne _ _ (by omega) (by omega)
        omega
    | succ node =>
      have result := ih (base+8) _ nextPointer (by omega) node (by omega)
      have address : base+8*(node+1)=(base+8)+8*node := by omega
      simpa only [address] using result

theorem checker_clear_rows_control (count : Nat) (s : MachineState) (small : count≤512)
    (pc : s.pc=if count=0 then 4096+4*32 else 4096+4*28)
    (counter : s.getReg .x30=BitVec.ofNat 64 count) :
    (checkerClearRows count s).pc=4096+4*32 ∧ (checkerClearRows count s).getReg .x30=0#64 := by
  induction count generalizing s with
  | zero => rw [checker_clear_rows_zero]; exact ⟨by simpa using pc,counter⟩
  | succ count ih =>
    have headPC : s.pc=4096+4*28 := by simpa using pc
    rw [checker_clear_rows_succ]
    exact ih _ (by omega) (checker_clear_next_pc s count (by omega) headPC counter)
      (checker_clear_next_count s count counter)

theorem checker_marks_init_saved_abi (original s : MachineState) (saved : CheckerSavedABI original s) :
    CheckerSavedABI original (checkerMarksInitPrefix 4 s) :=
  checker_saved_abi_frame original s _ saved (fun _ => checker_marks_init_memory s _)
theorem checker_clear_rows_saved_abi (original s : MachineState) (count : Nat) (small : count≤512)
    (pointer : s.getReg .x2=4096#64) (saved : CheckerSavedABI original s) :
    CheckerSavedABI original (checkerClearRows count s) := by
  apply checker_saved_abi_frame original s _ saved
  intro slot
  apply checker_clear_rows_memory_frame
  intro index before
  rw [pointer]
  change BitVec.ofNat 64 (checkerSavedAddress slot)≠BitVec.ofNat 64 4096+BitVec.ofNat 64 (8*index)
  rw [←BitVec.ofNat_add]
  have range := checker_saved_byte_range slot 0 (by decide)
  have low : 8192<checkingMetadataBase := by decide +kernel
  apply word_of_nat_ne _ _ (by omega) (by omega)
  omega

@[irreducible] def checkerMarksClearedState (s : MachineState) : MachineState :=
  checkerClearRows 512 (checkerMarksInitPrefix 4 (checkerSavedState (checkerEmptyState 13 s)))
theorem checker_marks_cleared_eq (s : MachineState) : checkerMarksClearedState s=
    checkerClearRows 512 (checkerMarksInitPrefix 4 (checkerSavedState (checkerEmptyState 13 s))) := by rw [checkerMarksClearedState]
theorem checker_marks_cleared_saved_abi (s : MachineState) : CheckerSavedABI s (checkerMarksClearedState s) := by
  rw [checker_marks_cleared_eq]
  exact checker_clear_rows_saved_abi s _ 512 (by decide) (checker_marks_init_pointer _)
    (checker_marks_init_saved_abi s _ (checker_admission_saved_abi s))
theorem checker_marks_cleared_content (s : MachineState) (node : Nat) (inside : node<512) :
    (checkerMarksClearedState s).getMem (BitVec.ofNat 64 (4096+8*node))=0#64 := by
  rw [checker_marks_cleared_eq]
  exact checker_clear_rows_content 512 4096 _ (checker_marks_init_pointer _) (by decide) node inside
theorem checker_marks_cleared_base (s : MachineState) : (checkerMarksClearedState s).getReg .x4=4096#64 := by
  rw [checker_marks_cleared_eq,checker_clear_rows_register 512 _ .x4 (by decide),checker_marks_init_base]
theorem checker_marks_cleared_metadata (s : MachineState) :
    (checkerMarksClearedState s).getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
  rw [checker_marks_cleared_eq,checker_clear_rows_register 512 _ .x8 (by decide),
    checker_marks_init_register _ .x8 (by decide),checker_saved_state_metadata]
theorem checker_marks_cleared_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x4,.x8,.x12,.x30]) : (checkerMarksClearedState s).getReg reg=s.getReg reg := by
  cases reg <;> simp at kept
  all_goals rw [checker_marks_cleared_eq,checker_clear_rows_register 512 _ _ (by decide),
    checker_marks_init_register _ _ (by decide),checker_saved_state_register _ _ (by decide),
    checker_admission_register 13 s (by decide) _ (by decide)]
theorem checker_marks_cleared_memory_frame (s : MachineState) (query : Word)
    (savedAway : ∀ slot : Fin 4, query≠BitVec.ofNat 64 (checkerSavedAddress slot))
    (marksAway : ∀ index, index<512 → query≠BitVec.ofNat 64 (4096+8*index)) :
    (checkerMarksClearedState s).getMem query=s.getMem query := by
  rw [checker_marks_cleared_eq,checker_clear_rows_memory_frame]
  · rw [checker_marks_init_memory,checker_saved_state_memory_frame _ query savedAway,
      checker_empty_memory s 13 (by decide)]
  · intro index inside
    rw [checker_marks_init_pointer]
    change query≠BitVec.ofNat 64 4096+BitVec.ofNat 64 (8*index)
    rw [←BitVec.ofNat_add]
    exact marksAway index inside

theorem checker_admission_marks_clear_execution (s : MachineState) (pc : s.pc=4096)
    (bounds : CheckerAdmissionBounds s) (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (2071+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerMarksClearedState s) coins
          return result.charge 2071 0) := by
  have savedPC : (checkerSavedState (checkerEmptyState 13 s)).pc=4096+4*24 := by
    rw [checker_saved_state_pc,checker_admission_pc 13 s (by decide) pc bounds nonempty]
    rfl
  have clearPC : (checkerMarksInitPrefix 4 (checkerSavedState (checkerEmptyState 13 s))).pc=4096+4*28 := by
    rw [checker_marks_init_pc 4 _ (by decide),savedPC]
    rfl
  rw [checker_marks_cleared_eq,show 2071+fuel=19+(4+(4*512+fuel)) by omega,
    checker_admission_save_execution s pc bounds nonempty,checker_marks_init_execution _ savedPC,
    checker_clear_rows_execution 512 4096 _ (by decide) (by simpa using clearPC)
      (checker_marks_init_pointer _) (by decide) (by decide) (checker_marks_init_count _)]
  simp [Execution.charge,←Nat.add_assoc]
theorem checker_marks_cleared_pc (s : MachineState) (pc : s.pc=4096)
    (bounds : CheckerAdmissionBounds s) (nonempty : s.getReg .x16≠0#64) :
    (checkerMarksClearedState s).pc=4096+4*32 := by
  rw [checker_marks_cleared_eq]
  apply (checker_clear_rows_control 512 _ (by decide) _ (checker_marks_init_count _)).1
  rw [checker_marks_init_pc 4 _ (by decide),checker_saved_state_pc,
    checker_admission_pc 13 s (by decide) pc bounds nonempty]
  rfl

end CommitGolfCandidate.Chained.Native

end
