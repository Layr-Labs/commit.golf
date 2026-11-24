import CommitGolfCandidate.ChainedCheckerSave
import CommitGolfCandidate.ChainedCheckerEmpty

/-! Successful nonempty length admission preserves the public ABI before saving it. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerMinimumWord (s : MachineState) : Word :=
  (s.getReg .x16 <<< 9)-(s.getReg .x16 <<< 5)+(s.getReg .x16 <<< 1)
def CheckerAdmissionBounds (s : MachineState) : Prop :=
  (¬BitVec.ult (s.getReg .x17) (checkerMinimumWord s)) ∧
  (¬BitVec.ult (checkerMinimumWord s+1888+1888) (s.getReg .x17))
def checkerAdmissionIndices : List Nat := [0,1,2,3,4,5,7,8,9,11,12,13,14,18]

private theorem branch_register (t : MachineState) (condition : Prop) [Decidable condition]
    (left right : Word) (reg : Reg) :
    (if condition then t.setPC left else t.setPC right).getReg reg=t.getReg reg := by
  by_cases taken : condition
  · exact (congrArg (fun state : MachineState => state.getReg reg) (ite_eq_left taken)).trans MachineState.getReg_setPC
  · exact (congrArg (fun state : MachineState => state.getReg reg) (ite_eq_right taken)).trans MachineState.getReg_setPC
theorem checker_admission_register (n : Nat) (s : MachineState) (small : n≤13) (reg : Reg)
    (kept : reg∉[.x2,.x3,.x12]) : (checkerEmptyState n s).getReg reg=s.getReg reg := by
  have step (t : MachineState) (i : Fin 13) : (execInstrBr t (checkerEmptyOps.getD i.val .EBREAK)).getReg reg=t.getReg reg := by
    fin_cases i
    all_goals first | exact branch_register t _ _ _ reg | (cases reg <;> simp at kept <;> rfl)
  induction n with
  | zero => rw [checker_empty_state_zero]
  | succ n ih => rw [checker_empty_state_succ,step _ ⟨n,by omega⟩,ih (by omega)]
theorem checker_admission_minimum (s : MachineState) :
    (checkerEmptyState 5 s).getReg .x2=checkerMinimumWord s := by
  simp only [checker_empty_state_succ,checker_empty_state_zero]
  rfl
theorem checker_admission_maximum (s : MachineState) :
    (checkerEmptyState 8 s).getReg .x3=checkerMinimumWord s+1888+1888 := by
  rw [checker_empty_state_succ,checker_empty_state_succ]
  change ((checkerEmptyState 6 s).getReg .x2+1888)+1888=_
  rw [checker_empty_state_succ]
  change (execInstrBr (checkerEmptyState 5 s) (.BGEU .x17 .x2 8)).getReg .x2+1888+1888=_
  rw [show (execInstrBr (checkerEmptyState 5 s) (.BGEU .x17 .x2 8)).getReg .x2=
    (checkerEmptyState 5 s).getReg .x2 from branch_register _ _ _ _ _,checker_admission_minimum]

theorem checker_minimum_of_count (s : MachineState) (count : Nat) (small : count≤LENGTH)
    (input : s.getReg .x16=BitVec.ofNat 64 count) : checkerMinimumWord s=BitVec.ofNat 64 (482*count) := by
  have maximum : LENGTH*32<2^64 := by decide +kernel
  simp only [checkerMinimumWord,input,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 count*BitVec.ofNat 64 512-BitVec.ofNat 64 count*BitVec.ofNat 64 32+
    BitVec.ofNat 64 count*BitVec.ofNat 64 2=BitVec.ofNat 64 (482*count)
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_mul,←BitVec.ofNat_mul,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega),←BitVec.ofNat_add]
  congr 1
  omega
theorem checker_admission_bounds_of_length (s : MachineState) (count length : Nat) (small : count≤LENGTH)
    (countInput : s.getReg .x16=BitVec.ofNat 64 count) (lengthInput : s.getReg .x17=BitVec.ofNat 64 length)
    (lower : 482*count≤length) (upper : length≤482*count+3776) : CheckerAdmissionBounds s := by
  have maximum : 482*LENGTH+3776<2^64 := by decide +kernel
  have lowFit : 482*count<2^64 := by omega
  have highFit : 482*count+3776<2^64 := by omega
  have lengthFit : length<2^64 := by omega
  have highWord : BitVec.ofNat 64 (482*count)+1888+1888=BitVec.ofNat 64 (482*count+3776) := by
    change BitVec.ofNat 64 (482*count)+BitVec.ofNat 64 1888+BitVec.ofNat 64 1888=_
    rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  rw [CheckerAdmissionBounds,checker_minimum_of_count s count small countInput,lengthInput,highWord]
  simp only [BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,Nat.mod_eq_of_lt lowFit,
    Nat.mod_eq_of_lt highFit,Nat.mod_eq_of_lt lengthFit]
  omega
theorem checker_admission_raw_pointer (s : MachineState) :
    (checkerEmptyState 13 s).getReg .x12=BitVec.ofNat 64 (2^33)+s.getReg .x15 := by
  have raw (t : MachineState) :
      (execInstrBr (execInstrBr t (.ADDI .x12 .x0 1)) (.SLLI .x12 .x12 33)).getReg .x12=BitVec.ofNat 64 (2^33) := by
    change (1#64 <<< 33)=_
    rfl
  rw [checker_empty_state_succ]
  change (execInstrBr (checkerEmptyState 12 s) (.BNE .x16 .x0 16)).getReg .x12=_
  rw [show (execInstrBr (checkerEmptyState 12 s) (.BNE .x16 .x0 16)).getReg .x12=
    (checkerEmptyState 12 s).getReg .x12 from branch_register _ _ _ _ _]
  rw [checker_empty_state_succ]
  change (checkerEmptyState 11 s).getReg .x12+(checkerEmptyState 11 s).getReg .x15=_
  rw [checker_admission_register 11 s (by decide) .x15 (by decide)]
  have value : (checkerEmptyState 11 s).getReg .x12=BitVec.ofNat 64 (2^33) := by
    rw [checker_empty_state_succ,checker_empty_state_succ]
    exact raw (checkerEmptyState 9 s)
  rw [value]

private theorem admission_step_pc (s : MachineState) (i : Fin 13) (bounds : CheckerAdmissionBounds s)
    (nonempty : s.getReg .x16≠0#64) :
    (checkerEmptyState (i.val+1) s).pc=(checkerEmptyState i.val s).pc+
      BitVec.ofNat 64 (4*(checkerAdmissionIndices.getD (i.val+1) 0-checkerAdmissionIndices.getD i.val 0)) := by
  rw [checker_empty_state_succ]
  fin_cases i <;> try rfl
  · have taken : execInstrBr (checkerEmptyState 5 s) (.BGEU .x17 .x2 8)=
        (checkerEmptyState 5 s).setPC ((checkerEmptyState 5 s).pc+8) := by
      apply ite_eq_left
      rw [checker_admission_register 5 s (by decide) .x17 (by decide),checker_admission_minimum]
      exact bounds.1
    exact congrArg MachineState.pc taken
  · have taken : execInstrBr (checkerEmptyState 8 s) (.BGEU .x3 .x17 8)=
        (checkerEmptyState 8 s).setPC ((checkerEmptyState 8 s).pc+8) := by
      apply ite_eq_left
      rw [checker_admission_register 8 s (by decide) .x17 (by decide),checker_admission_maximum]
      exact bounds.2
    exact congrArg MachineState.pc taken
  · have taken : execInstrBr (checkerEmptyState 12 s) (.BNE .x16 .x0 16)=
        (checkerEmptyState 12 s).setPC ((checkerEmptyState 12 s).pc+16) := by
      apply ite_eq_left
      have count : (checkerEmptyState 12 s).getReg .x16≠0#64 := by
        rwa [checker_admission_register 12 s (by decide) .x16 (by decide)]
      change ((checkerEmptyState 12 s).getReg .x16 != 0#64)=true
      exact bne_iff_ne.mpr count
    exact congrArg MachineState.pc taken
theorem checker_admission_pc (n : Nat) (s : MachineState) (small : n≤13) (pc : s.pc=4096)
    (bounds : CheckerAdmissionBounds s) (nonempty : s.getReg .x16≠0#64) :
    (checkerEmptyState n s).pc=4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD n 0) := by
  induction n with
  | zero => rw [checker_empty_state_zero,pc]; rfl
  | succ n ih =>
    rw [admission_step_pc s ⟨n,by omega⟩ bounds nonempty,ih (by omega)]
    have bound : n<13 := by omega
    have arithmetic (i : Fin 13) :
        4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD i.val 0)+
          BitVec.ofNat 64 (4*(checkerAdmissionIndices.getD (i.val+1) 0-checkerAdmissionIndices.getD i.val 0))=
          4096+BitVec.ofNat 64 (4*checkerAdmissionIndices.getD (i.val+1) 0) := by
      fin_cases i <;> decide +kernel
    exact arithmetic ⟨n,bound⟩

theorem checker_admission_execution (s : MachineState) (pc : s.pc=4096) (bounds : CheckerAdmissionBounds s)
    (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (13+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerEmptyState 13 s) coins
          return result.charge 13 0) := by
  rw [checking_manifest_image]
  conv_lhs => rw [←checker_empty_state_zero s]
  apply execute_unit_steps (states := fun n => checkerEmptyState n s)
  intro i inside
  refine ⟨.base (checkerEmptyOps.getD i .EBREAK),?_,?_,?_⟩
  · have opcode : checkerEmptyOps.getD i .EBREAK=chainedCheckerOps.getD (checkerAdmissionIndices.getD i 0) .EBREAK := by
      interval_cases i <;> rfl
    rw [opcode]
    apply chained_checker_ops_at _ (by rw [chained_checker_ops_length]; interval_cases i <;> decide) _
      (checker_admission_pc i s (by omega) pc bounds nonempty)
  · rw [checker_empty_state_succ]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_admission_saved_abi (s : MachineState) : CheckerSavedABI s (checkerSavedState (checkerEmptyState 13 s)) := by
  intro slot
  exact (checker_save_original (checkerEmptyState 13 s) slot).trans
    (checker_admission_register 13 s (by decide) _ (by fin_cases slot <;> decide))
theorem checker_admission_save_execution (s : MachineState) (pc : s.pc=4096) (bounds : CheckerAdmissionBounds s)
    (nonempty : s.getReg .x16≠0#64) (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (19+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerSavedState (checkerEmptyState 13 s)) coins
          return result.charge 19 0) := by
  have nextPC : (checkerEmptyState 13 s).pc=4096+4*18 := checker_admission_pc 13 s (by decide) pc bounds nonempty
  rw [show 19+fuel=13+(6+fuel) by omega,checker_admission_execution s pc bounds nonempty,
    checker_save_execution _ nextPC]
  simp [Execution.charge,←Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
