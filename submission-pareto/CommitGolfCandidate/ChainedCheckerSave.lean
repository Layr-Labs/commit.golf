import CommitGolfCandidate.ChainedCheckerSavedSlots

/-! Metadata initialization and four ABI stores, characterized independently. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerMetadataOps : List Instr := [.ADDI .x8 .x0 1,.SLLI .x8 .x8 35]
@[irreducible] def checkerMetadataPrefix (n : Nat) (s : MachineState) : MachineState :=
  (checkerMetadataOps.take n).foldl execInstrBr s
theorem checker_metadata_zero (s : MachineState) : checkerMetadataPrefix 0 s=s := by rw [checkerMetadataPrefix]; rfl
theorem checker_metadata_succ (n : Nat) (s : MachineState) (small : n<2) :
    checkerMetadataPrefix (n+1) s=execInstrBr (checkerMetadataPrefix n s) (checkerMetadataOps.getD n .EBREAK) := by
  interval_cases n <;> rw [checkerMetadataPrefix,checkerMetadataPrefix] <;> rfl
theorem checker_metadata_value (s : MachineState) :
    (checkerMetadataPrefix 2 s).getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
  rw [checkerMetadataPrefix]
  change (1#64 <<< 35)=BitVec.ofNat 64 checkingMetadataBase
  rfl
theorem checker_metadata_register (s : MachineState) (reg : Reg) (kept : reg≠.x8) :
    (checkerMetadataPrefix 2 s).getReg reg=s.getReg reg := by
  rw [checkerMetadataPrefix]
  cases reg <;> first | contradiction | rfl
theorem checker_metadata_memory (s : MachineState) (query : Word) :
    (checkerMetadataPrefix 2 s).getMem query=s.getMem query := by rw [checkerMetadataPrefix]; rfl
theorem checker_metadata_pc (n : Nat) (s : MachineState) (small : n≤2) :
    (checkerMetadataPrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> rw [checkerMetadataPrefix]
  · exact (BitVec.add_zero _).symm
  · rfl
  · change s.pc+4+4=s.pc+8
    rw [BitVec.add_assoc]
    rfl
theorem checker_metadata_at : OpsAt chainedCheckerImage (4096+4*18) checkerMetadataOps :=
  chained_checker_slice_at 18 2 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_metadata_execution (s : MachineState) (pc : s.pc=4096+4*18) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (2+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerMetadataPrefix 2 s) coins
          return result.charge 2 0) := by
  conv_lhs => rw [←checker_metadata_zero s]
  apply execute_unit_steps (states := fun n => checkerMetadataPrefix n s)
  intro i inside
  refine ⟨.base (checkerMetadataOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_metadata_at i inside
    rw [checker_metadata_pc i s (by omega),pc]
  · rw [checker_metadata_succ i s inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

def checkerStoreOps : List Instr :=
  [.SD .x8 .x11 1024,.SD .x8 .x13 1032,.SD .x8 .x14 1040,.SD .x8 .x16 1048]
@[irreducible] def checkerStorePrefix (n : Nat) (s : MachineState) : MachineState :=
  Nat.rec s (fun index before => execInstrBr before (checkerStoreOps.getD index .EBREAK)) n
theorem checker_store_zero (s : MachineState) : checkerStorePrefix 0 s=s := by rw [checkerStorePrefix]; rfl
theorem checker_store_succ (n : Nat) (s : MachineState) : checkerStorePrefix (n+1) s=
    execInstrBr (checkerStorePrefix n s) (checkerStoreOps.getD n .EBREAK) := by unfold checkerStorePrefix; rfl
theorem checker_store_at : OpsAt chainedCheckerImage (4096+4*20) checkerStoreOps :=
  chained_checker_slice_at 20 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)
theorem checker_store_opcode (i : Fin 4) : checkerStoreOps.getD i.val .EBREAK=
    .SD .x8 (checkerSavedReg i) (BitVec.ofNat 12 (1024+8*i.val)) := by fin_cases i <;> rfl
theorem checker_store_register (n : Nat) (s : MachineState) (small : n≤4) (reg : Reg) :
    (checkerStorePrefix n s).getReg reg=s.getReg reg := by
  induction n with
  | zero => rw [checker_store_zero]
  | succ n ih =>
    rw [checker_store_succ,checker_store_opcode ⟨n,by omega⟩]
    change (checkerStorePrefix n s).getReg reg=_
    exact ih (by omega)
theorem checker_store_step_memory (s : MachineState) (i : Fin 4) (query : Word)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) :
    (execInstrBr s (checkerStoreOps.getD i.val .EBREAK)).getMem query=
      if query=BitVec.ofNat 64 (checkerSavedAddress i) then s.getReg (checkerSavedReg i) else s.getMem query := by
  have sd (t : MachineState) (r : Reg) (offset : BitVec 12) :
      (execInstrBr t (.SD .x8 r offset)).getMem query=
        if query=t.getReg .x8+signExtend12 offset then t.getReg r else t.getMem query := by
    change (if query==t.getReg .x8+signExtend12 offset then _ else _)=_
    simp only [beq_iff_eq,MachineState.getMem]
  rw [checker_store_opcode,sd,metadata]
  fin_cases i <;> rfl
theorem checker_store_saved (n : Nat) (s : MachineState) (small : n≤4)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) :
    ∀ i : Fin 4, i.val<n → (checkerStorePrefix n s).getMem (BitVec.ofNat 64 (checkerSavedAddress i))=s.getReg (checkerSavedReg i) := by
  induction n with
  | zero => intro i inside; omega
  | succ n ih =>
    intro i inside
    rw [checker_store_succ,checker_store_step_memory _ ⟨n,by omega⟩ _
      ((checker_store_register n s (by omega) .x8).trans metadata)]
    by_cases same : i.val=n
    · have eq : i=⟨n,by omega⟩ := Fin.ext same
      rw [eq,ite_eq_left rfl,checker_store_register n s (by omega)]
    · have apart : BitVec.ofNat 64 (checkerSavedAddress i)≠BitVec.ofNat 64 (checkerSavedAddress ⟨n,by omega⟩) := by
        have left := checker_saved_byte_range i 0 (by decide)
        have right := checker_saved_byte_range ⟨n,by omega⟩ 0 (by decide)
        apply word_of_nat_ne _ _ (by omega) (by omega)
        unfold checkerSavedAddress
        change checkingMetadataBase+1024+8*i.val≠checkingMetadataBase+1024+8*n
        omega
      rw [ite_eq_right apart]
      exact ih (by omega) i (by omega)
theorem checker_store_pc (n : Nat) (s : MachineState) (small : n≤4) :
    (checkerStorePrefix n s).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  induction n with
  | zero => rw [checker_store_zero]; exact (BitVec.add_zero _).symm
  | succ n ih =>
    rw [checker_store_succ,checker_store_opcode ⟨n,by omega⟩]
    change (checkerStorePrefix n s).pc+4=_
    rw [ih (by omega),BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (4*n)+BitVec.ofNat 64 4=BitVec.ofNat 64 (4*(n+1))
    rw [←BitVec.ofNat_add]
    congr 1
theorem checker_store_memory_frame (n : Nat) (s : MachineState) (small : n≤4) (query : Word)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase)
    (away : ∀ slot : Fin 4, query≠BitVec.ofNat 64 (checkerSavedAddress slot)) :
    (checkerStorePrefix n s).getMem query=s.getMem query := by
  induction n with
  | zero => rw [checker_store_zero]
  | succ n ih =>
    rw [checker_store_succ,checker_store_step_memory _ ⟨n,by omega⟩ _
      ((checker_store_register n s (by omega) .x8).trans metadata),ite_eq_right (away ⟨n,by omega⟩),ih (by omega)]
theorem checker_store_execution (s : MachineState) (pc : s.pc=4096+4*20)
    (metadata : s.getReg .x8=BitVec.ofNat 64 checkingMetadataBase) (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (4+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerStorePrefix 4 s) coins
          return result.charge 4 0) := by
  conv_lhs => rw [←checker_store_zero s]
  apply execute_unit_steps (states := fun n => checkerStorePrefix n s)
  intro i inside
  refine ⟨.base (checkerStoreOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_store_at i inside
    rw [checker_store_pc i s (by omega),pc]
  · rw [checker_store_succ,checker_store_opcode ⟨i,inside⟩]
    change (if accessValid ((checkerStorePrefix i s).getReg .x8+_) 8 then _ else _)=_
    rw [checker_store_register i s (by omega),metadata]
    have valid (slot : Fin 4) : accessValid (BitVec.ofNat 64 checkingMetadataBase+
        signExtend12 (BitVec.ofNat 12 (1024+8*slot.val))) 8=true := by fin_cases slot <;> decide +kernel
    exact ite_eq_left (valid ⟨i,inside⟩)
  · interval_cases i <;> rfl

@[irreducible] def checkerSavedState (s : MachineState) : MachineState := checkerStorePrefix 4 (checkerMetadataPrefix 2 s)
theorem checker_saved_state_eq (s : MachineState) : checkerSavedState s=checkerStorePrefix 4 (checkerMetadataPrefix 2 s) := by rw [checkerSavedState]
theorem checker_save_original (s : MachineState) : CheckerSavedABI s (checkerSavedState s) := by
  intro i
  rw [checker_saved_state_eq,checker_store_saved 4 _ (by decide) (checker_metadata_value s) i i.isLt]
  apply checker_metadata_register
  fin_cases i <;> decide
theorem checker_saved_state_metadata (s : MachineState) :
    (checkerSavedState s).getReg .x8=BitVec.ofNat 64 checkingMetadataBase := by
  rw [checker_saved_state_eq,checker_store_register 4 _ (by decide),checker_metadata_value]
theorem checker_saved_state_register (s : MachineState) (reg : Reg) (kept : reg≠.x8) :
    (checkerSavedState s).getReg reg=s.getReg reg := by
  rw [checker_saved_state_eq,checker_store_register 4 _ (by decide),checker_metadata_register s reg kept]
theorem checker_saved_state_memory_frame (s : MachineState) (query : Word)
    (away : ∀ slot : Fin 4, query≠BitVec.ofNat 64 (checkerSavedAddress slot)) :
    (checkerSavedState s).getMem query=s.getMem query := by
  rw [checker_saved_state_eq,checker_store_memory_frame 4 _ (by decide) query (checker_metadata_value s) away,
    checker_metadata_memory]
theorem checker_saved_state_pc (s : MachineState) : (checkerSavedState s).pc=s.pc+24 := by
  rw [checker_saved_state_eq,checker_store_pc 4 _ (by decide),checker_metadata_pc 2 s (by decide),BitVec.add_assoc]
  rfl
theorem checker_save_execution (s : MachineState) (pc : s.pc=4096+4*18) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (6+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSavedState s) coins
          return result.charge 6 0) := by
  rw [checking_manifest_image,checker_saved_state_eq]
  have nextPC : (checkerMetadataPrefix 2 s).pc=4096+4*20 := by rw [checker_metadata_pc 2 s (by decide),pc]; rfl
  rw [show 6+fuel=2+(4+fuel) by omega,checker_metadata_execution s pc,
    checker_store_execution _ nextPC (checker_metadata_value s)]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
