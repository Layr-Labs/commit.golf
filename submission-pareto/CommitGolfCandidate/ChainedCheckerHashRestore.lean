import CommitGolfCandidate.ChainedCheckerHashWrapper
import CommitGolfCandidate.ChainedCheckHashLowFrame

/-! The installed hash-wrapper loads restore every saved caller register. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerLoadBackSlot (i : Fin 31) : Fin 31 := ⟨if i.val<30 then i.val+1 else 0,by split_ifs <;> omega⟩
def checkerLoadBackPosition (slot : Fin 31) : Nat := if slot.val=0 then 30 else slot.val-1
def checkerLoadBackOps : List Instr := (List.finRange 31).map fun i =>
  .LD (checkerSnapshotReg (checkerLoadBackSlot i)) .x0 (BitVec.ofNat 12 (8*(checkerLoadBackSlot i).val))
def CheckerHashSite.restoreIndex : CheckerHashSite → Nat | .lower => 2829 | .cap => 2927

@[irreducible] def checkerLoadBackPrefix (s : MachineState) (n : Nat) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (checkerLoadBackOps.getD i .EBREAK)) n
theorem checker_load_back_zero (s : MachineState) : checkerLoadBackPrefix s 0=s := by rw [checkerLoadBackPrefix]; rfl
theorem checker_load_back_succ (s : MachineState) (n : Nat) : checkerLoadBackPrefix s (n+1)=
    execInstrBr (checkerLoadBackPrefix s n) (checkerLoadBackOps.getD n .EBREAK) := by unfold checkerLoadBackPrefix; rfl
theorem checker_load_back_opcode (i : Fin 31) : checkerLoadBackOps.getD i.val .EBREAK=
    .LD (checkerSnapshotReg (checkerLoadBackSlot i)) .x0 (BitVec.ofNat 12 (8*(checkerLoadBackSlot i).val)) := by
  fin_cases i <;> rfl

theorem checker_load_back_at (site : CheckerHashSite) :
    OpsAt chainedCheckerImage (4096+BitVec.ofNat 64 (4*site.restoreIndex)) checkerLoadBackOps := by
  cases site
  · exact chained_checker_slice_at 2829 31 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2927 31 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_snapshot_reg_injective : Function.Injective checkerSnapshotReg := by decide +kernel
theorem checker_snapshot_reg_nonzero (slot : Fin 31) : checkerSnapshotReg slot≠.x0 := by fin_cases slot <;> decide
theorem checker_load_back_position_eq (i slot : Fin 31) :
    checkerLoadBackPosition slot=i.val ↔ checkerLoadBackSlot i=slot := by revert i slot; decide +kernel
theorem checker_load_back_position_lt (slot : Fin 31) : checkerLoadBackPosition slot<31 := by
  unfold checkerLoadBackPosition
  split_ifs <;> omega

theorem checker_load_back_memory (s : MachineState) (n : Nat) (small : n≤31) (query : Word) :
    (checkerLoadBackPrefix s n).getMem query=s.getMem query := by
  have step (t : MachineState) (i : Fin 31) :
      (execInstrBr t (checkerLoadBackOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_load_back_zero]
  | succ n ih => rw [checker_load_back_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_load_back_pc (s : MachineState) (n : Nat) (small : n≤31) :
    (checkerLoadBackPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 31) :
      (execInstrBr t (checkerLoadBackOps.getD i.val .EBREAK)).pc=t.pc+4 := by
    fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_load_back_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_load_back_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1

private theorem load_back_value (s : MachineState) (i : Fin 31) :
    (execInstrBr s (checkerLoadBackOps.getD i.val .EBREAK)).getReg (checkerSnapshotReg (checkerLoadBackSlot i))=
      s.getMem (checkerSaveWord (checkerLoadBackSlot i)) := by
  rw [checker_load_back_opcode]
  have zero : s.getReg .x0=0#64 := rfl
  simp only [execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (checker_snapshot_reg_nonzero _),zero,BitVec.zero_add]
  fin_cases i <;> rfl

private theorem load_back_other (s : MachineState) (i slot : Fin 31) (different : checkerLoadBackSlot i≠slot) :
    (execInstrBr s (checkerLoadBackOps.getD i.val .EBREAK)).getReg (checkerSnapshotReg slot)=s.getReg (checkerSnapshotReg slot) := by
  rw [checker_load_back_opcode]
  simp only [execInstrBr,MachineState.getReg_setPC]
  apply MachineState.getReg_setReg_ne
  exact fun same => different (checker_snapshot_reg_injective same)

theorem checker_load_back_prefix_register (s : MachineState) (n : Nat) (small : n≤31) (slot : Fin 31) :
    (checkerLoadBackPrefix s n).getReg (checkerSnapshotReg slot)=
      if checkerLoadBackPosition slot<n then s.getMem (checkerSaveWord slot) else s.getReg (checkerSnapshotReg slot) := by
  induction n with
  | zero => rw [checker_load_back_zero,if_neg (by omega)]
  | succ n ih =>
    rw [checker_load_back_succ]
    by_cases same : checkerLoadBackPosition slot=n
    · have assigned := (checker_load_back_position_eq ⟨n,by omega⟩ slot).mp same
      rw [←assigned,load_back_value _ ⟨n,by omega⟩,checker_load_back_memory _ _ (by omega),assigned,
        if_pos (by omega)]
    · have different : checkerLoadBackSlot ⟨n,by omega⟩≠slot := by
        intro assigned
        exact same ((checker_load_back_position_eq ⟨n,by omega⟩ slot).mpr assigned)
      rw [load_back_other _ ⟨n,by omega⟩ slot different,ih (by omega)]
      by_cases before : checkerLoadBackPosition slot<n
      · rw [ite_eq_left before,ite_eq_left (by omega)]
      · rw [ite_eq_right before,ite_eq_right (by omega)]

theorem checker_load_back_register (s : MachineState) (slot : Fin 31) :
    (checkerLoadBackPrefix s 31).getReg (checkerSnapshotReg slot)=s.getMem (checkerSaveWord slot) := by
  rw [checker_load_back_prefix_register s 31 (by omega),if_pos (checker_load_back_position_lt slot)]

private theorem load_back_ordinary (s : MachineState) (i : Fin 31) :
    ordinaryStep s (.base (checkerLoadBackOps.getD i.val .EBREAK))=
      some (execInstrBr s (checkerLoadBackOps.getD i.val .EBREAK)) := by
  have zero : s.getReg .x0=0#64 := rfl
  fin_cases i
  all_goals change (if accessValid (s.getReg .x0+_) 8 then _ else _)=_
  all_goals rw [zero]; exact ite_eq_left (by decide +kernel)

theorem checker_load_back_execution (site : CheckerHashSite) (s : MachineState)
    (pc : s.pc=4096+BitVec.ofNat 64 (4*site.restoreIndex)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (31+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLoadBackPrefix s 31) coins
          return result.charge 31 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_load_back_zero s]
  apply execute_unit_steps (states := checkerLoadBackPrefix s)
  intro i inside
  refine ⟨.base (checkerLoadBackOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_load_back_at site i inside
    rw [checker_load_back_pc _ _ (by omega),pc]
  · rw [checker_load_back_succ]
    exact load_back_ordinary _ ⟨i,inside⟩
  · interval_cases i <;> rfl

def CheckerHashSite.resultSlot : CheckerHashSite → Fin 31 | .lower => ⟨22,by omega⟩ | .cap => ⟨11,by omega⟩
def checkerResultOps (site : CheckerHashSite) : List Instr := [
  .LD .x31 .x0 (BitVec.ofNat 12 (8*site.resultSlot.val)),
  .LD .x20 .x0 256,.SD .x31 .x20 0,
  .LD .x20 .x0 264,.SD .x31 .x20 8,
  .LD .x20 .x0 272,.SD .x31 .x20 16,
  .LD .x20 .x0 280,.SD .x31 .x20 24]
@[irreducible] def checkerResultPrefix (site : CheckerHashSite) (s : MachineState) (n : Nat) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before ((checkerResultOps site).getD i .EBREAK)) n
theorem checker_result_zero (site : CheckerHashSite) (s : MachineState) : checkerResultPrefix site s 0=s := by
  rw [checkerResultPrefix]; rfl
theorem checker_result_succ (site : CheckerHashSite) (s : MachineState) (n : Nat) : checkerResultPrefix site s (n+1)=
    execInstrBr (checkerResultPrefix site s n) ((checkerResultOps site).getD n .EBREAK) := by unfold checkerResultPrefix; rfl

theorem checker_result_at (site : CheckerHashSite) : OpsAt chainedCheckerImage site.resume (checkerResultOps site) := by
  cases site
  · exact chained_checker_slice_at 2820 9 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2918 9 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_result_pc (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9) :
    (checkerResultPrefix site s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have step (t : MachineState) (i : Fin 9) :
      (execInstrBr t ((checkerResultOps site).getD i.val .EBREAK)).pc=t.pc+4 := by
    cases site <;> fin_cases i <;> rfl
  induction n with
  | zero => rw [checker_result_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_result_succ,step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1

theorem checker_result_destination (site : CheckerHashSite) (s : MachineState) (n : Nat)
    (positive : 0<n) (small : n≤9) :
    (checkerResultPrefix site s n).getReg .x31=s.getMem (checkerSaveWord site.resultSlot) := by
  have step (t : MachineState) (i : Fin 8) :
      (execInstrBr t ((checkerResultOps site).getD (i.val+1) .EBREAK)).getReg .x31=t.getReg .x31 := by
    cases site <;> fin_cases i <;> rfl
  induction n with
  | zero => omega
  | succ n ih =>
    rw [checker_result_succ]
    by_cases empty : n=0
    · subst n
      rw [checker_result_zero]
      cases site <;> rfl
    · have kept := step (checkerResultPrefix site s n) ⟨n-1,by omega⟩
      simp only [show n-1+1=n by omega] at kept
      rw [kept]
      exact ih (by omega) (by omega)

theorem checker_result_outside (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (query : Word)
    (away : ∀ i : Fin 4, query≠(12288 : Word)+BitVec.ofNat 64 (8*i.val)) :
    (checkerResultPrefix site s n).getMem query=s.getMem query := by
  induction n with
  | zero => rw [checker_result_zero]
  | succ n ih =>
    rw [checker_result_succ,←ih (by omega)]
    have source (positive : 0<n) : (checkerResultPrefix site s n).getReg .x31=12288 :=
      (checker_result_destination site s n positive (by omega)).trans destination
    have bound : n<9 := by omega
    cases site <;> interval_cases n
    all_goals first | rfl | apply word_store_frame
    all_goals rw [source (by omega)]
    all_goals first | exact away ⟨0,by omega⟩ | exact away ⟨1,by omega⟩ |
      exact away ⟨2,by omega⟩ | exact away ⟨3,by omega⟩

theorem checker_save_word_result_apart (slot : Fin 31) (i : Fin 4) :
    checkerSaveWord slot≠(12288 : Word)+BitVec.ofNat 64 (8*i.val) := by revert slot i; decide +kernel

theorem checker_result_saved_memory (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (slot : Fin 31) :
    (checkerResultPrefix site s n).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) :=
  checker_result_outside site s n small destination _ (checker_save_word_result_apart slot)

private theorem result_ordinary (site : CheckerHashSite) (s : MachineState) (i : Fin 9)
    (source : 0 < i.val → s.getReg .x31=12288) :
    ordinaryStep s (.base ((checkerResultOps site).getD i.val .EBREAK))=
      some (execInstrBr s ((checkerResultOps site).getD i.val .EBREAK)) := by
  have zero : s.getReg .x0=0#64 := rfl
  by_cases initial : i.val=0
  · have same : i=0 := Fin.ext initial
    subst i
    cases site
    all_goals change (if accessValid (s.getReg .x0+_) 8 then _ else _)=_
    all_goals rw [zero]; exact ite_eq_left (by decide +kernel)
  have destination := source (by omega)
  cases site <;> fin_cases i
  all_goals simp only [checkerResultOps,CheckerHashSite.resultSlot,List.getD_cons_zero,List.getD_cons_succ,
    ordinaryStep,memoryArgumentsValid,memAccess,zero,destination]
  all_goals exact ite_eq_left (by decide +kernel)

theorem checker_result_execution (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.resume)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerResultPrefix site s 9) coins
          return result.charge 9 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_result_zero site s]
  apply execute_unit_steps (states := checkerResultPrefix site s)
  intro i inside
  refine ⟨.base ((checkerResultOps site).getD i .EBREAK),?_,?_,?_⟩
  · apply checker_result_at site i inside
    rw [checker_result_pc _ _ _ (by omega),pc]
  · rw [checker_result_succ]
    exact result_ordinary site _ ⟨i,inside⟩ (fun positive =>
      (checker_result_destination site s i positive (by omega)).trans destination)
  · cases site <;> interval_cases i <;> rfl

theorem checker_save_word_pair_apart (slot : Fin 31) (i : Fin 8) :
    checkerSaveWord slot≠(12544 : Word)+BitVec.ofNat 64 (8*i.val) := by revert slot i; decide +kernel

theorem checker_child_mask_saved_memory (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (pair : s.getReg site.childReg=12544) (slot : Fin 31) :
    (checkerChildMaskPrefix site s n).getMem (checkerSaveWord slot)=s.getMem (checkerSaveWord slot) := by
  have succ (i : Nat) (inside : i<9) : checkerChildMaskPrefix site s (i+1)=
      execInstrBr (checkerChildMaskPrefix site s i) ((checkerChildMaskOps site).getD i .EBREAK) := by
    cases site <;> interval_cases i <;> rw [checkerChildMaskPrefix,checkerChildMaskPrefix] <;> rfl
  have step (t : MachineState) (i : Fin 9) (source : t.getReg .x14=12544) :
      (execInstrBr t ((checkerChildMaskOps site).getD i.val .EBREAK)).getMem (checkerSaveWord slot)=t.getMem (checkerSaveWord slot) := by
    cases site <;> fin_cases i
    all_goals first | rfl | apply word_store_frame
    all_goals rw [source]
    all_goals first | exact checker_save_word_pair_apart slot ⟨3,by omega⟩ |
      exact checker_save_word_pair_apart slot ⟨7,by omega⟩
  induction n with
  | zero => rw [checkerChildMaskPrefix]; rfl
  | succ n ih =>
    by_cases empty : n=0
    · subst n
      rw [checkerChildMaskPrefix]
      cases site <;> rfl
    · rw [succ n (by omega),step _ ⟨n,by omega⟩
        ((checker_child_mask_source site s n (by omega) (by omega)).trans pair),ih (by omega)]

theorem checker_first_schedule_memory (s : MachineState) (query : Word) :
    (checkerFirstSchedulePrefix s 7).getMem query=s.getMem query := by
  have succ (n : Nat) (inside : n<7) : checkerFirstSchedulePrefix s (n+1)=
      execInstrBr (checkerFirstSchedulePrefix s n) (checkerFirstScheduleOps.getD n .EBREAK) := by
    interval_cases n <;> rw [checkerFirstSchedulePrefix,checkerFirstSchedulePrefix] <;> rfl
  have step (t : MachineState) (i : Fin 7) :
      (execInstrBr t (checkerFirstScheduleOps.getD i.val .EBREAK)).getMem query=t.getMem query := by
    fin_cases i
    all_goals first | rfl |
      (simp only [checkerFirstScheduleOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr]; split_ifs <;> rfl)
  have all (n : Nat) (small : n≤7) : (checkerFirstSchedulePrefix s n).getMem query=s.getMem query := by
    induction n with
    | zero => rw [checkerFirstSchedulePrefix]; rfl
    | succ n ih => rw [succ n (by omega),step _ ⟨n,by omega⟩,ih (by omega)]
  exact all 7 (by omega)

theorem checker_hash_abi_memory (s : MachineState) (query : Word) :
    (checkerHashABIPrefix s 5).getMem query=s.getMem query := by
  rw [checkerHashABIPrefix]
  rfl

theorem checker_first_hash_saved (s : MachineState) (pair : s.getReg .x24=12544) (slot : Fin 31) :
    (checkerFirstHashState s).getMem (checkerSaveWord slot)=s.getReg (checkerSnapshotReg slot) := by
  rw [checker_first_hash_eq,checker_hash_abi_memory,checker_first_schedule_memory,
    checker_child_mask_saved_memory .lower _ 9 (by omega)]
  · exact checker_snapshot_saved 31 s (by omega) slot slot.isLt
  · exact (checker_snapshot_register 31 s (by omega) .x24).trans pair

@[irreducible] def checkerHashReturned (site : CheckerHashSite) (s : MachineState) : MachineState :=
  execInstrBr (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31) (.JALR .x0 .x1 0)

theorem checker_hash_returned_register (site : CheckerHashSite) (s : MachineState)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (slot : Fin 31) :
    (checkerHashReturned site s).getReg (checkerSnapshotReg slot)=s.getMem (checkerSaveWord slot) := by
  rw [checkerHashReturned]
  have step (t : MachineState) (reg : Reg) : (execInstrBr t (.JALR .x0 .x1 0)).getReg reg=t.getReg reg := by cases reg <;> rfl
  rw [step,checker_load_back_register,checker_result_saved_memory _ _ _ (by omega) destination]

theorem checker_hash_returned_pc (s : MachineState)
    (destination : s.getMem (checkerSaveWord CheckerHashSite.lower.resultSlot)=12288)
    (link : s.getMem (checkerSaveWord ⟨0,by omega⟩)=4096+4*2609) :
    (checkerHashReturned .lower s).pc=4096+4*2609 := by
  rw [checkerHashReturned]
  have restored : (checkerLoadBackPrefix (checkerResultPrefix .lower s 9) 31).getReg .x1=4096+4*2609 := by
    exact (checker_load_back_register _ ⟨0,by omega⟩).trans
      ((checker_result_saved_memory .lower s 9 (by omega) destination ⟨0,by omega⟩).trans link)
  change ((checkerLoadBackPrefix (checkerResultPrefix .lower s 9) 31).getReg .x1+signExtend12 0) &&& _=_
  rw [restored]
  rfl

theorem checker_hash_return_execution (site : CheckerHashSite) (s : MachineState) (pc : s.pc=site.resume)
    (destination : s.getMem (checkerSaveWord site.resultSlot)=12288) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (41+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashReturned site s) coins
          return result.charge 41 0) := by
  have resultPC : (checkerResultPrefix site s 9).pc=4096+BitVec.ofNat 64 (4*site.restoreIndex) := by
    rw [checker_result_pc _ _ _ (by omega),pc]
    cases site <;> rfl
  have loadPC : (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31).pc=
      4096+BitVec.ofNat 64 (4*(site.restoreIndex+31)) := by
    rw [checker_load_back_pc _ _ (by omega),resultPC]
    cases site <;> rfl
  have tail : execute (Artifact.submission.image .check) (1+fuel)
      (checkerLoadBackPrefix (checkerResultPrefix site s 9) 31) coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashReturned site s) coins
          return result.charge 1 0) := by
    rw [checking_manifest_image,checkerHashReturned]
    rw [show 1+fuel=fuel+1 by omega]
    apply execute_ordinary_step (instruction := .base (.JALR .x0 .x1 0))
    · cases site
      · exact chained_checker_ops_at 2860 (by rw [chained_checker_ops_length]; decide) _ loadPC
      · exact chained_checker_ops_at 2958 (by rw [chained_checker_ops_length]; decide) _ loadPC
    · rfl
  have count : 41+fuel=9+(31+(1+fuel)) := by omega
  rw [count,checker_result_execution site s pc destination,
    checker_load_back_execution site _ resultPC,tail]
  simp [Execution.charge,←Nat.add_assoc]

def checkerLowerFinishOps : List Instr := [.JAL .x0 528,
  .LD .x31 .x23 24,.SLLI .x31 .x31 18,.SRLI .x31 .x31 18,.SD .x23 .x31 24,
  .JAL .x0 2096612,.ADD .x21 .x21 .x30,.SRLI .x6 .x6 1,
  .ADDI .x29 .x29 4095,.BNE .x29 .x0 7488]
@[irreducible] def checkerLowerFinishPrefix (s : MachineState) (n : Nat) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (checkerLowerFinishOps.getD i .EBREAK)) n
theorem checker_lower_finish_zero (s : MachineState) : checkerLowerFinishPrefix s 0=s := by rw [checkerLowerFinishPrefix]; rfl
theorem checker_lower_finish_succ (s : MachineState) (n : Nat) : checkerLowerFinishPrefix s (n+1)=
    execInstrBr (checkerLowerFinishPrefix s n) (checkerLowerFinishOps.getD n .EBREAK) := by unfold checkerLowerFinishPrefix; rfl
def checkerLowerFinishIndex (i : Fin 10) : Nat := if i.val=0 then 2609 else if i.val≤5 then 2740+i.val else 2604+i.val

private theorem finish_reg_mem (s : MachineState) (query value : Word) (reg : Reg) :
    (s.setMem query value).getReg reg=s.getReg reg := by cases reg <;> rfl
private theorem finish_reg_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

theorem checker_lower_finish_digest (s : MachineState) (n : Nat) (small : n≤10) :
    (checkerLowerFinishPrefix s n).getReg .x23=s.getReg .x23 := by
  have step (t : MachineState) (i : Fin 10) :
      (execInstrBr t (checkerLowerFinishOps.getD i.val .EBREAK)).getReg .x23=t.getReg .x23 := by
    fin_cases i
    all_goals simp (disch := decide) only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,finish_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq]
    all_goals split_ifs <;> simp only [MachineState.getReg_setPC]
  induction n with
  | zero => rw [checker_lower_finish_zero]
  | succ n ih => rw [checker_lower_finish_succ,step _ ⟨n,by omega⟩,ih (by omega)]

theorem checker_lower_finish_pc (s : MachineState) (pc : s.pc=4096+4*2609) (i : Fin 10) :
    (checkerLowerFinishPrefix s i.val).pc=4096+BitVec.ofNat 64 (4*checkerLowerFinishIndex i) := by
  have step (t : MachineState) (j : Fin 9) :
      (execInstrBr t (checkerLowerFinishOps.getD j.val .EBREAK)).pc=
        t.pc+(if j.val=0 then signExtend21 528 else if j.val=5 then signExtend21 2096612 else 4) := by
    fin_cases j <;> rfl
  fin_cases i
  all_goals repeat rw [checker_lower_finish_succ,step _ ⟨_,by omega⟩]
  all_goals rw [checker_lower_finish_zero,pc]; rfl

private theorem finish_ordinary (s : MachineState) (i : Fin 10) (source : s.getReg .x23=12288) :
    ordinaryStep s (.base (checkerLowerFinishOps.getD i.val .EBREAK))=
      some (execInstrBr s (checkerLowerFinishOps.getD i.val .EBREAK)) := by
  fin_cases i
  all_goals first | rfl |
    (simp only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,ordinaryStep,memoryArgumentsValid,memAccess,source];
     exact ite_eq_left (by decide +kernel))

theorem checker_lower_finish_execution (s : MachineState) (pc : s.pc=4096+4*2609)
    (source : s.getReg .x23=12288) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (10+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerLowerFinishPrefix s 10) coins
          return result.charge 10 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_lower_finish_zero s]
  apply execute_unit_steps (states := checkerLowerFinishPrefix s)
  intro i inside
  refine ⟨.base (checkerLowerFinishOps.getD i .EBREAK),?_,?_,?_⟩
  · have position := checker_lower_finish_pc s pc ⟨i,inside⟩
    interval_cases i
    all_goals exact chained_checker_ops_at _ (by rw [chained_checker_ops_length]; simp [checkerLowerFinishIndex]) _ position
  · rw [checker_lower_finish_succ]
    exact finish_ordinary _ ⟨i,inside⟩ ((checker_lower_finish_digest s i (by omega)).trans source)
  · interval_cases i <;> rfl

theorem checker_lower_finish_values (s : MachineState) (counter : s.getReg .x29=16) :
    (checkerLowerFinishPrefix s 10).getReg .x21=s.getReg .x21+s.getReg .x30 ∧
    (checkerLowerFinishPrefix s 10).getReg .x6=s.getReg .x6 >>> 1 ∧
    (checkerLowerFinishPrefix s 10).getReg .x29=15 := by
  repeat rw [checker_lower_finish_succ]
  simp (disch := decide) only [checker_lower_finish_zero,checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
    MachineState.getReg_setPC,finish_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq,finish_reg_zero,counter]
  split_ifs <;> simp (disch := decide) only [MachineState.getReg_setPC,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq]
  all_goals exact ⟨True.intro,rfl,by decide +kernel⟩

theorem checker_lower_finish_return_pc (s : MachineState) (pc : s.pc=4096+4*2609) (counter : s.getReg .x29=16) :
    (checkerLowerFinishPrefix s 10).pc=4096+4*2437 := by
  have before := checker_lower_finish_pc s pc ⟨9,by omega⟩
  have count : (checkerLowerFinishPrefix s 9).getReg .x29=15 := by
    repeat rw [checker_lower_finish_succ]
    simp (disch := decide) only [checker_lower_finish_zero,checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
      MachineState.getReg_setPC,finish_reg_mem,MachineState.getReg_setReg_eq,MachineState.getReg_setReg_ne,reduceCtorEq,counter]
    rfl
  rw [show 10=9+1 from rfl,checker_lower_finish_succ]
  simp only [checkerLowerFinishOps,List.getD_cons_zero,List.getD_cons_succ,execInstrBr,
    finish_reg_zero,count]
  change (checkerLowerFinishPrefix s 9).pc+signExtend13 7488=_
  rw [before]
  rfl

end CommitGolfCandidate.Chained.Native
