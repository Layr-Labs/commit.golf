import CommitGolfCandidate.ChainedCheckerRecordInverseRun

/-! Actual record source advance, counter decrement and back/exit edges. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def checkerRecordAdvanceOps : List Instr :=
  [.ADDI .x18 .x18 482,.ADDI .x16 .x16 4095,.BEQ .x16 .x0 8,.JAL .x0 2088728]
@[irreducible] def checkerRecordAdvancePrefix (s : MachineState) (n : Nat) : MachineState :=
  (checkerRecordAdvanceOps.take n).foldl execInstrBr s
def checkerRecordAdvanceDone (s : MachineState) : Bool := s.getReg .x16 == 0
def checkerRecordAdvanceGuard (s : MachineState) : MachineState := execInstrBr s (.BEQ .x16 .x0 8)
def checkerRecordAdvanceJump (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 2088728)
@[irreducible] def checkerRecordAdvanceState (s : MachineState) : MachineState :=
  if checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2) then
    checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)
  else checkerRecordAdvanceJump (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2))
def checkerRecordAdvanceCycles (s : MachineState) : Nat :=
  if checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2) then 3 else 4

theorem checker_record_advance_eq (s : MachineState) : checkerRecordAdvanceState s=
    if checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2) then
      checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)
    else checkerRecordAdvanceJump (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)) := by
  rw [checkerRecordAdvanceState]

theorem checker_record_advance_at : OpsAt chainedCheckerImage (4096+4*2160) checkerRecordAdvanceOps :=
  chained_checker_slice_at 2160 4 _ (by rw [chained_checker_ops_length]; decide) (by decide +kernel)

theorem checker_record_advance_prefix_zero (s : MachineState) : checkerRecordAdvancePrefix s 0=s := by
  rw [checkerRecordAdvancePrefix]
  rfl

theorem checker_record_advance_prefix_succ (s : MachineState) (n : Nat) (small : n<2) :
    checkerRecordAdvancePrefix s (n+1)=
      execInstrBr (checkerRecordAdvancePrefix s n) (checkerRecordAdvanceOps.getD n .EBREAK) := by
  interval_cases n <;> unfold checkerRecordAdvancePrefix <;> rfl

theorem checker_record_advance_prefix_pc (s : MachineState) (n : Nat) (small : n≤2) :
    (checkerRecordAdvancePrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n <;> unfold checkerRecordAdvancePrefix
  · exact (BitVec.add_zero _).symm
  · rfl
  · change (s.pc+4)+4=s.pc+8
    rw [BitVec.add_assoc]; rfl

theorem checker_record_advance_source (s : MachineState) :
    (checkerRecordAdvancePrefix s 2).getReg .x18=s.getReg .x18+482 := by
  unfold checkerRecordAdvancePrefix
  rfl

theorem checker_record_advance_count (s : MachineState) :
    (checkerRecordAdvancePrefix s 2).getReg .x16=s.getReg .x16-1 := by
  unfold checkerRecordAdvancePrefix
  change s.getReg .x16+signExtend12 4095=_
  rw [BitVec.sub_eq_add_neg]
  rfl

theorem checker_record_advance_prefix_register (s : MachineState) (reg : Reg)
    (kept : reg∉[.x16,.x18]) : (checkerRecordAdvancePrefix s 2).getReg reg=s.getReg reg := by
  unfold checkerRecordAdvancePrefix
  cases reg <;> simp at kept <;> rfl

theorem checker_record_advance_prefix_byte (s : MachineState) (query : Word) :
    (checkerRecordAdvancePrefix s 2).getByte query=s.getByte query := by
  unfold checkerRecordAdvancePrefix
  rfl

private theorem advance_guard_register (s : MachineState) (reg : Reg) :
    (checkerRecordAdvanceGuard s).getReg reg=s.getReg reg := by
  by_cases done : checkerRecordAdvanceDone s
  · have same : checkerRecordAdvanceGuard s=s.setPC (s.pc+8) := ite_eq_left done
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC
  · have same : checkerRecordAdvanceGuard s=s.setPC (s.pc+4) := ite_eq_right done
    exact (congrArg (fun state : MachineState => state.getReg reg) same).trans MachineState.getReg_setPC

private theorem advance_guard_memory (s : MachineState) (query : Word) :
    (checkerRecordAdvanceGuard s).getMem query=s.getMem query := by
  by_cases done : checkerRecordAdvanceDone s
  · have same : checkerRecordAdvanceGuard s=s.setPC (s.pc+8) := ite_eq_left done
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC
  · have same : checkerRecordAdvanceGuard s=s.setPC (s.pc+4) := ite_eq_right done
    exact (congrArg (fun state : MachineState => state.getMem query) same).trans MachineState.getMem_setPC

private theorem advance_guard_pc (s : MachineState) : (checkerRecordAdvanceGuard s).pc=
    if checkerRecordAdvanceDone s then s.pc+8 else s.pc+4 := by
  change (if checkerRecordAdvanceDone s then s.setPC (s.pc+8) else s.setPC (s.pc+4)).pc=_
  split <;> rfl

private theorem advance_jump_register (s : MachineState) (offset : BitVec 21) (reg : Reg) :
    (execInstrBr s (.JAL .x0 offset)).getReg reg=s.getReg reg := by cases reg <;> rfl
private theorem advance_jump_byte (s : MachineState) (offset : BitVec 21) (query : Word) :
    (execInstrBr s (.JAL .x0 offset)).getByte query=s.getByte query := rfl
private theorem advance_jump_pc (s : MachineState) (offset : BitVec 21) :
    (execInstrBr s (.JAL .x0 offset)).pc=s.pc+signExtend21 offset := rfl

theorem checker_record_advance_register (s : MachineState) (reg : Reg) :
    (checkerRecordAdvanceState s).getReg reg=(checkerRecordAdvancePrefix s 2).getReg reg := by
  rw [checker_record_advance_eq]
  split
  · exact advance_guard_register _ reg
  · exact (advance_jump_register _ 2088728 reg).trans (advance_guard_register _ reg)

theorem checker_record_advance_byte (s : MachineState) (query : Word) :
    (checkerRecordAdvanceState s).getByte query=s.getByte query := by
  have guardByte (state : MachineState) : (checkerRecordAdvanceGuard state).getByte query=state.getByte query := by
    simp only [MachineState.getByte,advance_guard_memory]
  rw [checker_record_advance_eq]
  split
  · rw [guardByte,checker_record_advance_prefix_byte]
  · rw [show checkerRecordAdvanceJump=fun state => execInstrBr state (.JAL .x0 2088728) from rfl,
      advance_jump_byte,guardByte,checker_record_advance_prefix_byte]

theorem checker_record_advance_pc (s : MachineState) (pc : s.pc=4096+4*2160) :
    (checkerRecordAdvanceState s).pc=
      if checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2) then 4096+4*2164 else 4096+4*57 := by
  rw [checker_record_advance_eq]
  split <;> rename_i done
  · rw [advance_guard_pc,ite_eq_left done,checker_record_advance_prefix_pc _ 2 (by decide),pc]
    rfl
  · rw [show checkerRecordAdvanceJump=fun state => execInstrBr state (.JAL .x0 2088728) from rfl,
      advance_jump_pc,advance_guard_pc,ite_eq_right done,checker_record_advance_prefix_pc _ 2 (by decide),pc]
    rfl

theorem checker_record_advance_prefix_execution (s : MachineState) (pc : s.pc=4096+4*2160)
    (fuel : Nat) (coins : Bool) :
    execute chainedCheckerImage (2+fuel) s coins=
      (do let result ← execute chainedCheckerImage fuel (checkerRecordAdvancePrefix s 2) coins
          return result.charge 2 0) := by
  conv_lhs => rw [←checker_record_advance_prefix_zero s]
  apply execute_unit_steps (states := checkerRecordAdvancePrefix s)
  intro i inside
  refine ⟨.base (checkerRecordAdvanceOps.getD i .EBREAK),?_,?_,?_⟩
  · apply checker_record_advance_at i (by change i<4; omega)
    rw [checker_record_advance_prefix_pc s i (by omega),pc]
  · rw [checker_record_advance_prefix_succ s i inside]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem checker_record_advance_execution (s : MachineState) (pc : s.pc=4096+4*2160)
    (fuel : Nat) (coins : Bool) :
    execute (Artifact.submission.image .check) (checkerRecordAdvanceCycles s+fuel) s coins=
      (do let result ← execute (Artifact.submission.image .check) fuel (checkerRecordAdvanceState s) coins
          return result.charge (checkerRecordAdvanceCycles s) 0) := by
  rw [checking_manifest_image]
  have prefixPC : (checkerRecordAdvancePrefix s 2).pc=(4096+4*2160)+8 := by
    rw [checker_record_advance_prefix_pc s 2 (by decide),pc]; rfl
  have guardFetch : fetch chainedCheckerImage (checkerRecordAdvancePrefix s 2)=some (.base (.BEQ .x16 .x0 8)) :=
    checker_record_advance_at 2 (by decide) _ prefixPC
  have guardStep : ordinaryStep (checkerRecordAdvancePrefix s 2) (.base (.BEQ .x16 .x0 8))=
      some (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)) := rfl
  by_cases done : checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2)
  · rw [checkerRecordAdvanceCycles,ite_eq_left done,show 3+fuel=2+(fuel+1) by omega,
      checker_record_advance_prefix_execution s pc,
      execute_ordinary_step chainedCheckerImage _ _ _ fuel coins guardFetch guardStep]
    simp [checker_record_advance_eq,done,Execution.charge,instructionCycles,←Nat.add_assoc]
  · have jumpPC : (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)).pc=(4096+4*2160)+12 := by
      rw [advance_guard_pc,ite_eq_right done,prefixPC,BitVec.add_assoc]; rfl
    have jumpFetch : fetch chainedCheckerImage (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2))=
        some (.base (.JAL .x0 2088728)) := checker_record_advance_at 3 (by decide) _ jumpPC
    have jumpStep : ordinaryStep (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2)) (.base (.JAL .x0 2088728))=
        some (checkerRecordAdvanceJump (checkerRecordAdvanceGuard (checkerRecordAdvancePrefix s 2))) := rfl
    rw [checkerRecordAdvanceCycles,ite_eq_right done,show 4+fuel=2+((fuel+1)+1) by omega,
      checker_record_advance_prefix_execution s pc,
      execute_ordinary_step chainedCheckerImage _ _ _ (fuel+1) coins guardFetch guardStep,
      execute_ordinary_step chainedCheckerImage _ _ _ fuel coins jumpFetch jumpStep]
    simp [checker_record_advance_eq,done,Execution.charge,instructionCycles,←Nat.add_assoc]

theorem checker_record_advance_counter (s : MachineState) (n : Nat)
    (count : s.getReg .x16=BitVec.ofNat 64 (n+1)) :
    (checkerRecordAdvanceState s).getReg .x16=BitVec.ofNat 64 n := by
  rw [checker_record_advance_register,checker_record_advance_count,count]
  have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
  rw [one]
  simpa only [Nat.add_sub_cancel] using BitVec.ofNat_sub_ofNat_of_le (n+1) 1 (by decide) (by omega)

theorem checker_record_advance_done (s : MachineState) (n : Nat) (fit : n<2^64)
    (count : s.getReg .x16=BitVec.ofNat 64 (n+1)) :
    checkerRecordAdvanceDone (checkerRecordAdvancePrefix s 2)=decide (n=0) := by
  have next := checker_record_advance_counter s n count
  rw [checker_record_advance_register] at next
  rw [checkerRecordAdvanceDone,next]
  change (n%2^64 == 0)=decide (n=0)
  rw [Nat.mod_eq_of_lt fit]
  cases n <;> rfl

end CommitGolfCandidate.Chained.Native
