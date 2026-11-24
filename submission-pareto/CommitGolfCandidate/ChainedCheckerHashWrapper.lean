import CommitGolfCandidate.ChainedCheckHashDelivered
import CommitGolfCandidate.ChainedCheckerSavedSlots

/-! The checking wrappers save the actual caller registers in low memory. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerSnapshotRegs : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,
  .x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]
def checkerSnapshotReg (slot : Fin 31) : Reg := checkerSnapshotRegs.getD slot.val .x0
def checkerSnapshotOps : List Instr := (List.range 31).map fun i =>
  .SD .x0 (checkerSnapshotRegs.getD i .x0) (BitVec.ofNat 12 (8*i))
def CheckerHashSite.wrapperIndex : CheckerHashSite → Nat | .lower => 2757 | .cap => 2861

@[irreducible] def checkerSnapshotPrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun i before => execInstrBr before (checkerSnapshotOps.getD i .EBREAK)) n
theorem checker_snapshot_zero (s : MachineState) : checkerSnapshotPrefix 0 s=s := by rw [checkerSnapshotPrefix]; rfl
theorem checker_snapshot_succ (n : Nat) (s : MachineState) : checkerSnapshotPrefix (n+1) s=
    execInstrBr (checkerSnapshotPrefix n s) (checkerSnapshotOps.getD n .EBREAK) := by unfold checkerSnapshotPrefix; rfl
theorem checker_snapshot_opcode (i : Fin 31) : checkerSnapshotOps.getD i.val .EBREAK=
    .SD .x0 (checkerSnapshotReg i) (BitVec.ofNat 12 (8*i.val)) := by fin_cases i <;> rfl
theorem checker_snapshot_at (site : CheckerHashSite) :
    OpsAt chainedCheckerImage (4096+BitVec.ofNat 64 (4*site.wrapperIndex)) checkerSnapshotOps := by
  cases site
  · exact chained_checker_slice_at 2757 31 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2861 31 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_snapshot_register (n : Nat) (s : MachineState) (small : n≤31) (reg : Reg) :
    (checkerSnapshotPrefix n s).getReg reg=s.getReg reg := by
  induction n with
  | zero => rw [checker_snapshot_zero]
  | succ n ih =>
    rw [checker_snapshot_succ,checker_snapshot_opcode ⟨n,by omega⟩]
    change (checkerSnapshotPrefix n s).getReg reg=s.getReg reg
    exact ih (by omega)

theorem checker_snapshot_step_memory (s : MachineState) (i : Fin 31) (query : Word) :
    (execInstrBr s (checkerSnapshotOps.getD i.val .EBREAK)).getMem query=
      if query=BitVec.ofNat 64 (8*i.val) then s.getReg (checkerSnapshotReg i) else s.getMem query := by
  have sd (r : Reg) (offset : BitVec 12) :
      (execInstrBr s (.SD .x0 r offset)).getMem query=
        if query=signExtend12 offset then s.getReg r else s.getMem query := by
    change (if query==s.getReg .x0+signExtend12 offset then _ else _)=_
    have zero : s.getReg .x0=0#64 := rfl
    simp only [zero,BitVec.zero_add,beq_iff_eq,MachineState.getMem]
  rw [checker_snapshot_opcode,sd]
  fin_cases i <;> rfl

theorem checker_snapshot_saved (n : Nat) (s : MachineState) (small : n≤31) :
    ∀ i : Fin 31, i.val<n → (checkerSnapshotPrefix n s).getMem (BitVec.ofNat 64 (8*i.val))=s.getReg (checkerSnapshotReg i) := by
  induction n with
  | zero => intro i inside; omega
  | succ n ih =>
    intro i inside
    rw [checker_snapshot_succ,checker_snapshot_step_memory _ ⟨n,by omega⟩]
    by_cases same : i.val=n
    · have eq : i=⟨n,by omega⟩ := Fin.ext same
      rw [eq,ite_eq_left rfl,checker_snapshot_register n s (by omega)]
    · have apart : BitVec.ofNat 64 (8*i.val)≠BitVec.ofNat 64 (8*n) := by
        apply word_of_nat_ne _ _ (by omega) (by omega)
        omega
      rw [ite_eq_right apart]
      exact ih (by omega) i (by omega)

theorem checker_snapshot_pc (n : Nat) (s : MachineState) (small : n≤31) :
    (checkerSnapshotPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_snapshot_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_snapshot_succ,checker_snapshot_opcode ⟨n,by omega⟩]
    change (checkerSnapshotPrefix n s).pc+4=_
    rw [ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1

theorem checker_snapshot_memory_frame (n : Nat) (s : MachineState) (small : n≤31) (query : Word)
    (away : ∀ slot : Fin 31, query≠BitVec.ofNat 64 (8*slot.val)) :
    (checkerSnapshotPrefix n s).getMem query=s.getMem query := by
  induction n with
  | zero => rw [checker_snapshot_zero]
  | succ n ih =>
    rw [checker_snapshot_succ,checker_snapshot_step_memory _ ⟨n,by omega⟩,ite_eq_right (away ⟨n,by omega⟩),ih (by omega)]

theorem checker_snapshot_execution (site : CheckerHashSite) (s : MachineState)
    (pc : s.pc=4096+BitVec.ofNat 64 (4*site.wrapperIndex)) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (31+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSnapshotPrefix 31 s) coins
          return result.charge 31 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_snapshot_zero s]
  apply execute_unit_steps (states := fun n => checkerSnapshotPrefix n s)
  intro i inside
  refine ⟨.base (checkerSnapshotOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_snapshot_at site i inside
    rw [checker_snapshot_pc i s (by omega),pc]
  · rw [checker_snapshot_succ,checker_snapshot_opcode ⟨i,inside⟩]
    change (if accessValid ((checkerSnapshotPrefix i s).getReg .x0+_) 8 then _ else _)=_
    rw [checker_snapshot_register i s (by omega)]
    have valid (slot : Fin 31) : accessValid (s.getReg .x0+signExtend12 (BitVec.ofNat 12 (8*slot.val))) 8=true := by
      have zero : s.getReg .x0=0#64 := rfl
      rw [zero]
      fin_cases slot <;> decide +kernel
    exact ite_eq_left (valid ⟨i,inside⟩)
  · rw [checker_snapshot_opcode ⟨i,inside⟩]
    rfl

private theorem wrapper_reg_mem (s : MachineState) (address value : Word) (reg : Reg) :
    (s.setMem address value).getReg reg=s.getReg reg := by cases reg <;> rfl

def CheckerHashSite.childReg : CheckerHashSite → Reg | .lower => .x24 | .cap => .x10
def checkerChildMaskOps (site : CheckerHashSite) : List Instr := [
  .ADDI .x14 site.childReg 0,
  .LD .x20 .x14 24,.SLLI .x20 .x20 18,.SRLI .x20 .x20 18,.SD .x14 .x20 24,
  .LD .x20 .x14 56,.SLLI .x20 .x20 18,.SRLI .x20 .x20 18,.SD .x14 .x20 56]
@[irreducible] def checkerChildMaskPrefix (site : CheckerHashSite) (s : MachineState) (n : Nat) : MachineState :=
  (checkerChildMaskOps site |>.take n).foldl execInstrBr s

theorem checker_child_mask_at (site : CheckerHashSite) :
    OpsAt chainedCheckerImage (4096+BitVec.ofNat 64 (4*(site.wrapperIndex+31))) (checkerChildMaskOps site) := by
  cases site
  · exact chained_checker_slice_at 2788 9 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
  · exact chained_checker_slice_at 2892 9 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_child_mask_pc (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9) :
    (checkerChildMaskPrefix site s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  have succ (i : Nat) (inside : i<9) : checkerChildMaskPrefix site s (i+1)=
      execInstrBr (checkerChildMaskPrefix site s i) ((checkerChildMaskOps site).getD i .EBREAK) := by
    interval_cases i <;> rw [checkerChildMaskPrefix,checkerChildMaskPrefix] <;> rfl
  have step (t : MachineState) (i : Fin 9) :
      (execInstrBr t ((checkerChildMaskOps site).getD i.val .EBREAK)).pc=t.pc+4 := by
    cases site <;> fin_cases i <;> rfl
  induction n with
  | zero => rw [checkerChildMaskPrefix]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [succ n (by omega),step _ ⟨n,by omega⟩,ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1

theorem checker_child_mask_register (site : CheckerHashSite) (s : MachineState) (n : Nat) (small : n≤9)
    (reg : Reg) (source : reg≠.x14) (temp : reg≠.x20) :
    (checkerChildMaskPrefix site s n).getReg reg=s.getReg reg := by
  cases site <;> interval_cases n <;> rw [checkerChildMaskPrefix]
  all_goals simp only [checkerChildMaskOps,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,wrapper_reg_mem,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm source),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp)]
  all_goals rfl

theorem checker_child_mask_source (site : CheckerHashSite) (s : MachineState) (n : Nat)
    (small : n≤9) (positive : 0<n) :
    (checkerChildMaskPrefix site s n).getReg .x14=
      s.getReg site.childReg := by
  cases site <;> interval_cases n <;> rw [checkerChildMaskPrefix]
  all_goals simp [checkerChildMaskOps,List.take,List.foldl,execInstrBr,signExtend12,
    MachineState.getReg_setPC,wrapper_reg_mem,MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne,BitVec.add_zero]

theorem checker_child_mask_execution_at (site : CheckerHashSite) (s : MachineState) (address : Word)
    (pc : s.pc=4096+BitVec.ofNat 64 (4*(site.wrapperIndex+31)))
    (source : s.getReg site.childReg=address)
    (first : accessValid (address+signExtend12 24) 8=true)
    (last : accessValid (address+signExtend12 56) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerChildMaskPrefix site s 9) coins
          return result.charge 9 0) := by
  rw [checking_manifest_image]
  have zero : checkerChildMaskPrefix site s 0=s := by rw [checkerChildMaskPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerChildMaskPrefix site s)
  intro i inside
  refine ⟨.base ((checkerChildMaskOps site).getD i .EBREAK),?_,?_,?_⟩
  · apply checker_child_mask_at site i inside
    rw [checker_child_mask_pc _ _ _ (by omega),pc]
  · have src (n : Nat) (small : n≤9) (positive : 0<n) :
        (checkerChildMaskPrefix site s n).getReg .x14=address :=
      (checker_child_mask_source site s n small positive).trans source
    cases site <;> interval_cases i
    all_goals first
      | (rw [checkerChildMaskPrefix,checkerChildMaskPrefix]; rfl)
      | (simp only [checkerChildMaskOps,List.getD_cons_zero,List.getD_cons_succ];
         change (if accessValid ((checkerChildMaskPrefix _ s _).getReg .x14+_) 8 then _ else _)=_;
         rw [src _ (by omega) (by omega)];
         simp only [first,last,ite_true];
         rw [checkerChildMaskPrefix,checkerChildMaskPrefix]; rfl)
  · cases site <;> interval_cases i <;> rfl

theorem checker_child_mask_execution (site : CheckerHashSite) (s : MachineState)
    (pc : s.pc=4096+BitVec.ofNat 64 (4*(site.wrapperIndex+31)))
    (source : s.getReg site.childReg=12544) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (9+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerChildMaskPrefix site s 9) coins
          return result.charge 9 0) :=
  checker_child_mask_execution_at site s 12544 pc source (by decide +kernel) (by decide +kernel) fuel coins

def checkerFirstScheduleOps : List Instr := [.ADDI .x17 .x0 16,.SUB .x17 .x17 .x29,
  .ADDI .x18 .x0 3,.ADDI .x16 .x0 4095,.SRLI .x16 .x16 22,.ADDI .x30 .x0 8,.BLTU .x17 .x30 36]
@[irreducible] def checkerFirstSchedulePrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerFirstScheduleOps.take n).foldl execInstrBr s
theorem checker_first_schedule_at : OpsAt chainedCheckerImage (4096+4*2797) checkerFirstScheduleOps :=
  chained_checker_slice_at 2797 7 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

@[local simp] private theorem wrapper_reg_zero (s : MachineState) : s.getReg .x0=0#64 := rfl
@[local simp] private theorem wrapper_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne MachineState.getReg_setPC

theorem checker_first_schedule_pc (s : MachineState) (pc : s.pc=4096+4*2797) (counter : s.getReg .x29=16) :
    (checkerFirstSchedulePrefix s 7).pc=4096+4*2812 := by
  simp [checkerFirstSchedulePrefix,checkerFirstScheduleOps,execInstrBr,pc,counter,signExtend12,signExtend13]

theorem checker_first_schedule_register (s : MachineState) (reg : Reg)
    (height : reg≠.x17) (counter : reg≠.x18) (mask : reg≠.x16) (temp : reg≠.x30) :
    (checkerFirstSchedulePrefix s 7).getReg reg=s.getReg reg := by
  simp only [checkerFirstSchedulePrefix,checkerFirstScheduleOps,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm height),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm counter),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm mask),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp)]
  split_ifs <;> simp only [MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm height),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm counter),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm mask),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm temp)]

theorem checker_first_schedule_values (s : MachineState) (counter : s.getReg .x29=16) :
    (checkerFirstSchedulePrefix s 7).getReg .x17=0 ∧
    (checkerFirstSchedulePrefix s 7).getReg .x18=3 ∧
    (checkerFirstSchedulePrefix s 7).getReg .x16=finalMask ⟨0,by decide⟩ := by
  simp [checkerFirstSchedulePrefix,checkerFirstScheduleOps,execInstrBr,counter,signExtend12,
    finalMask,width]

theorem checker_first_schedule_execution (s : MachineState) (pc : s.pc=4096+4*2797)
    (counter : s.getReg .x29=16) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (7+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstSchedulePrefix s 7) coins
          return result.charge 7 0) := by
  rw [checking_manifest_image]
  have zero : checkerFirstSchedulePrefix s 0=s := by rw [checkerFirstSchedulePrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerFirstSchedulePrefix s)
  intro i inside
  refine ⟨.base (checkerFirstScheduleOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_first_schedule_at i inside
    interval_cases i <;> simp [checkerFirstSchedulePrefix,checkerFirstScheduleOps,execInstrBr,pc,BitVec.add_assoc]
  · interval_cases i <;> rw [checkerFirstSchedulePrefix,checkerFirstSchedulePrefix] <;> rfl
  · interval_cases i <;> rfl

def checkerHashABIOps : List Instr := [.ADDI .x10 .x0 256,.ADDI .x12 .x10 0,
  .ADDI .x5 .x0 0,.ADDI .x11 .x0 64,.ADDI .x13 .x0 0]
@[irreducible] def checkerHashABIPrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerHashABIOps.take n).foldl execInstrBr s
theorem checker_hash_abi_at : OpsAt chainedCheckerImage (4096+4*2812) checkerHashABIOps :=
  chained_checker_slice_at 2812 5 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_hash_abi_pc (s : MachineState) (pc : s.pc=4096+4*2812) :
    (checkerHashABIPrefix s 5).pc=4096+4*2817 := by
  simp [checkerHashABIPrefix,checkerHashABIOps,execInstrBr,pc]

theorem checker_hash_abi_register (s : MachineState) (reg : Reg)
    (src : reg≠.x10) (dst : reg≠.x12) (selector : reg≠.x5) (size : reg≠.x11) (kind : reg≠.x13) :
    (checkerHashABIPrefix s 5).getReg reg=s.getReg reg := by
  simp [checkerHashABIPrefix,checkerHashABIOps,execInstrBr,Ne.symm src,Ne.symm dst,
    Ne.symm selector,Ne.symm size,Ne.symm kind]

theorem checker_hash_abi_args (s : MachineState) : LoopArgs (checkerHashABIPrefix s 5) 256 := by
  refine ⟨?_,?_,?_,?_,?_,by decide,by decide,by decide,by decide⟩
  all_goals rw [checkerHashABIPrefix]; rfl

theorem checker_hash_abi_execution (s : MachineState) (pc : s.pc=4096+4*2812)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (5+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerHashABIPrefix s 5) coins
          return result.charge 5 0) := by
  rw [checking_manifest_image]
  have zero : checkerHashABIPrefix s 0=s := by rw [checkerHashABIPrefix]; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := checkerHashABIPrefix s)
  intro i inside
  refine ⟨.base (checkerHashABIOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_hash_abi_at i inside
    interval_cases i <;> simp [checkerHashABIPrefix,checkerHashABIOps,execInstrBr,pc,BitVec.add_assoc]
  · interval_cases i <;> rw [checkerHashABIPrefix,checkerHashABIPrefix] <;> rfl
  · interval_cases i <;> rfl

@[irreducible] def checkerFirstHashState (s : MachineState) : MachineState :=
  checkerHashABIPrefix (checkerFirstSchedulePrefix
    (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9) 7) 5

theorem checker_first_hash_eq (s : MachineState) : checkerFirstHashState s=
    checkerHashABIPrefix (checkerFirstSchedulePrefix
      (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9) 7) 5 := by rw [checkerFirstHashState]

structure CheckerFirstHashReady (s : MachineState) : Prop where
  pc : s.pc=CheckerHashSite.lower.base
  args : LoopArgs s 256
  remaining : s.getReg .x18=3
  height : s.getReg .x17=0
  mask : s.getReg .x16=finalMask ⟨0,by decide⟩
  source : s.getReg .x14=12544

theorem checker_first_hash_ready (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544) (counter : s.getReg .x29=16) :
    CheckerFirstHashReady (checkerFirstHashState s) := by
  have snapPC : (checkerSnapshotPrefix 31 s).pc=4096+4*2788 := by
    rw [checker_snapshot_pc _ _ (by omega),pc]; rfl
  have maskPC : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).pc=4096+4*2797 := by
    rw [checker_child_mask_pc _ _ _ (by omega),snapPC]; rfl
  have maskCounter : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).getReg .x29=16 := by
    rw [checker_child_mask_register _ _ _ (by omega) _ (by decide) (by decide),
      checker_snapshot_register _ _ (by omega),counter]
  have values := checker_first_schedule_values _ maskCounter
  rw [checker_first_hash_eq]
  refine ⟨checker_hash_abi_pc _ (checker_first_schedule_pc _ maskPC maskCounter),checker_hash_abi_args _,?_,?_,?_,?_⟩
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.2.1
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.1
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact values.2.2
  · rw [checker_hash_abi_register _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      checker_first_schedule_register _ _ (by decide) (by decide) (by decide) (by decide),
      checker_child_mask_source _ _ _ (by omega) (by omega),checker_snapshot_register _ _ (by omega)]
    exact pair

theorem checker_first_hash_setup_execution (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544) (counter : s.getReg .x29=16)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (52+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerFirstHashState s) coins
          return result.charge 52 0) := by
  have snapPC : (checkerSnapshotPrefix 31 s).pc=4096+4*2788 := by
    rw [checker_snapshot_pc _ _ (by omega),pc]; rfl
  have maskPC : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).pc=4096+4*2797 := by
    rw [checker_child_mask_pc _ _ _ (by omega),snapPC]; rfl
  have maskCounter : (checkerChildMaskPrefix .lower (checkerSnapshotPrefix 31 s) 9).getReg .x29=16 := by
    rw [checker_child_mask_register _ _ _ (by omega) _ (by decide) (by decide),
      checker_snapshot_register _ _ (by omega),counter]
  rw [show 52+fuel=31+(9+(7+(5+fuel))) by omega,
    checker_snapshot_execution .lower s pc,
    checker_child_mask_execution .lower _ snapPC ((checker_snapshot_register _ _ (by omega) .x24).trans pair)]
  simp only [bind_assoc]
  rw [checker_first_schedule_execution _ maskPC maskCounter,
    checker_hash_abi_execution _ (checker_first_schedule_pc _ maskPC maskCounter),checker_first_hash_eq]
  simp [Execution.charge,←Nat.add_assoc]

theorem checker_first_hash_execution (s : MachineState)
    (pc : s.pc=4096+4*2757) (pair : s.getReg .x24=12544) (counter : s.getReg .x29=16)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (117+fuel) s coins=
      (do let out ← checkerHashTrace .lower 3 (checkerFirstHashState s)
          let result ← execute (Artifact.submission.image .check) fuel out coins
          return result.charge 145 4) := by
  have ready := checker_first_hash_ready s pc pair counter
  have inputs : ∀ k : Fin 8, accessValid ((checkerFirstHashState s).getReg .x14+BitVec.ofNat 64 (8*k.val)) 8=true := by
    intro k
    rw [ready.source]
    fin_cases k <;> decide +kernel
  rw [show 117+fuel=52+(34+continuationInstructions 3+fuel) by change 117+fuel=52+(65+fuel); omega,
    checker_first_hash_setup_execution s pc pair counter,
    artifact_checking_hash .lower 3 (by omega) _ ready.args ready.pc ready.remaining inputs]
  simp [Execution.charge,continuationCycles,←Nat.add_assoc,bind_assoc]

end CommitGolfCandidate.Chained.Native
