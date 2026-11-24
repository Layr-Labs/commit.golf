import CommitGolfCandidate.ChainedRecordFrame

/-! Actual scratch reset and record-loop cursor/counter/branch instructions. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def recordResetOps : List Instr := [.ADDI .x7 .x0 1,.SLLI .x7 .x7 33,.ADD .x7 .x7 .x17]
def recordResetPrefix (s : MachineState) (count : Nat) : MachineState :=
  (recordResetOps.take count).foldl execInstrBr s
def recordPostOps : List Instr :=
  [.ADDI .x6 .x20 0,.ADDI .x29 .x29 4095,.BEQ .x29 .x0 8,.JAL .x0 2088896]
def recordPostPrefix (s : MachineState) (count : Nat) : MachineState :=
  (recordPostOps.take count).foldl execInstrBr s
def recordDone (s : MachineState) : Bool := s.getReg .x29 == 0
def recordGuard (s : MachineState) : MachineState := execInstrBr s (.BEQ .x29 .x0 8)
def recordJump (s : MachineState) : MachineState := execInstrBr s (.JAL .x0 2088896)
def recordPostState (s : MachineState) : MachineState :=
  if recordDone (recordPostPrefix s 2) then recordGuard (recordPostPrefix s 2)
  else recordJump (recordGuard (recordPostPrefix s 2))
def recordPostCycles (s : MachineState) : Nat := if recordDone (recordPostPrefix s 2) then 3 else 4

theorem record_reset_metadata (s : MachineState) :
    (recordResetPrefix s 3).getReg .x7=s.getReg .x17+0x200000000 := by
  change ((1 : Word)<<<33)+s.getReg .x17=_
  rw [BitVec.add_comm]
  rfl
theorem record_reset_register (s : MachineState) (reg : Reg) (different : reg≠.x7) :
    (recordResetPrefix s 3).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem record_reset_byte (s : MachineState) (query : Word) :
    (recordResetPrefix s 3).getByte query=s.getByte query := rfl
theorem record_reset_pc (s : MachineState) (n : Nat) (small : n≤3) :
    (recordResetPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n
  · simp [recordResetPrefix]
  · rfl
  · change (s.pc+4)+4=s.pc+8
    rw [BitVec.add_assoc]; rfl
  · change ((s.pc+4)+4)+4=s.pc+12
    rw [BitVec.add_assoc,BitVec.add_assoc]; rfl

theorem record_post_prefix_pc (s : MachineState) (n : Nat) (small : n≤2) :
    (recordPostPrefix s n).pc=s.pc+BitVec.ofNat 64 (4*n) := by
  interval_cases n
  · simp [recordPostPrefix]
  · rfl
  · change (s.pc+4)+4=s.pc+8
    rw [BitVec.add_assoc]; rfl
theorem record_post_output (s : MachineState) : (recordPostPrefix s 2).getReg .x6=s.getReg .x20 := by
  change s.getReg .x20+0=_
  exact BitVec.add_zero _
theorem record_post_count (s : MachineState) : (recordPostPrefix s 2).getReg .x29=s.getReg .x29-1 := by
  change s.getReg .x29+signExtend12 4095=_
  rw [BitVec.sub_eq_add_neg]
  rfl
theorem record_post_prefix_register (s : MachineState) (reg : Reg) (a : reg≠.x6) (b : reg≠.x29) :
    (recordPostPrefix s 2).getReg reg=s.getReg reg := by cases reg <;> first | contradiction | rfl
theorem record_post_prefix_byte (s : MachineState) (query : Word) :
    (recordPostPrefix s 2).getByte query=s.getByte query := rfl

theorem record_guard_register (s : MachineState) (reg : Reg) : (recordGuard s).getReg reg=s.getReg reg := by
  by_cases done : recordDone s
  · have same : recordGuard s=s.setPC (s.pc+8) := ite_eq_left done
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : recordGuard s=s.setPC (s.pc+4) := ite_eq_right done
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
theorem record_guard_memory (s : MachineState) (query : Word) : (recordGuard s).getMem query=s.getMem query := by
  by_cases done : recordDone s
  · have same : recordGuard s=s.setPC (s.pc+8) := ite_eq_left done
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : recordGuard s=s.setPC (s.pc+4) := ite_eq_right done
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
theorem record_guard_pc (s : MachineState) : (recordGuard s).pc=if recordDone s then s.pc+8 else s.pc+4 := by
  change (if recordDone s then s.setPC (s.pc+8) else s.setPC (s.pc+4)).pc=_
  split <;> rfl
private theorem jump_register (s : MachineState) (offset : BitVec 21) (reg : Reg) :
    (execInstrBr s (.JAL .x0 offset)).getReg reg=s.getReg reg := by
  cases reg <;> rfl
private theorem jump_byte (s : MachineState) (offset : BitVec 21) (query : Word) :
    (execInstrBr s (.JAL .x0 offset)).getByte query=s.getByte query := rfl
theorem record_jump_register (s : MachineState) (reg : Reg) : (recordJump s).getReg reg=s.getReg reg :=
  jump_register s 2088896 reg
theorem record_jump_byte (s : MachineState) (query : Word) : (recordJump s).getByte query=s.getByte query :=
  jump_byte s 2088896 query
theorem record_jump_pc (s : MachineState) : (recordJump s).pc=s.pc+signExtend21 2088896 := rfl
theorem record_post_register (s : MachineState) (reg : Reg) :
    (recordPostState s).getReg reg=(recordPostPrefix s 2).getReg reg := by
  unfold recordPostState
  split <;> simp only [record_jump_register,record_guard_register]
theorem record_post_byte (s : MachineState) (query : Word) : (recordPostState s).getByte query=s.getByte query := by
  have guardByte (st : MachineState) : (recordGuard st).getByte query=st.getByte query := by
    simp only [MachineState.getByte,record_guard_memory]
  unfold recordPostState
  split <;> simp only [record_jump_byte,guardByte,record_post_prefix_byte]
theorem record_post_pc (s : MachineState) (pc : s.pc=12364) :
    (recordPostState s).pc=if recordDone (recordPostPrefix s 2) then 12380 else 4120 := by
  unfold recordPostState
  split <;> rename_i done <;>
    simp only [record_jump_pc,record_guard_pc,done,↓reduceIte,record_post_prefix_pc s 2 (by decide),pc]
  all_goals rfl

theorem opening_record_control_layout :
    openingControllerOps=openingControllerOps.take 6++recordResetOps++openingControllerOps.drop 9 ∧
    openingControllerOps=openingControllerOps.take 2067++recordPostOps++openingControllerOps.drop 2071 := by decide
theorem controller_record_control_at (image : Image) (base : Word) (code : OpsAt image base openingControllerOps) :
    OpsAt image (base+24) recordResetOps ∧ OpsAt image (base+8268) recordPostOps := by
  constructor
  · rw [opening_record_control_layout.1,List.append_assoc] at code
    have afterPrefix := ops_at_right image base (openingControllerOps.take 6) _ code
    rw [List.length_take,opening_controller_ops_length] at afterPrefix
    exact ops_at_left image _ _ _ afterPrefix
  · rw [opening_record_control_layout.2,List.append_assoc] at code
    have afterPrefix := ops_at_right image base (openingControllerOps.take 2067) _ code
    rw [List.length_take,opening_controller_ops_length] at afterPrefix
    exact ops_at_left image _ _ _ afterPrefix

theorem record_reset_execution (image : Image) (base : Word) (code : OpsAt image base recordResetOps)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (3+fuel) s coins=
      (do let result ← execute image fuel (recordResetPrefix s 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states:=recordResetPrefix s)
  intro i inside
  refine ⟨.base (recordResetOps.getD i .EBREAK),?_,?_,?_⟩
  · apply code i inside
    rw [record_reset_pc s i (by omega),pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
theorem record_post_prefix_execution (image : Image) (base : Word) (code : OpsAt image base recordPostOps)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins=
      (do let result ← execute image fuel (recordPostPrefix s 2) coins
          return result.charge 2 0) := by
  apply execute_unit_steps (states:=recordPostPrefix s)
  intro i inside
  refine ⟨.base (recordPostOps.getD i .EBREAK),?_,?_,?_⟩
  · apply code i (by change i<4; omega)
    rw [record_post_prefix_pc s i (by omega),pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem record_post_execution (image : Image) (base : Word) (code : OpsAt image base recordPostOps)
    (s : MachineState) (pc : s.pc=base) (fuel : Nat) (coins : Bool) :
    execute image (recordPostCycles s+fuel) s coins=
      (do let result ← execute image fuel (recordPostState s) coins
          return result.charge (recordPostCycles s) 0) := by
  have prefixPC : (recordPostPrefix s 2).pc=base+8 := by rw [record_post_prefix_pc _ 2 (by decide),pc]; rfl
  have guardFetch : fetch image (recordPostPrefix s 2)=some (.base (.BEQ .x29 .x0 8)) := by
    exact code 2 (by decide) _ prefixPC
  have ordinary : ordinaryStep (recordPostPrefix s 2) (.base (.BEQ .x29 .x0 8))=
      some (recordGuard (recordPostPrefix s 2)) := rfl
  by_cases done : recordDone (recordPostPrefix s 2)
  · rw [recordPostCycles,ite_eq_left done,show 3+fuel=2+(fuel+1) by omega,
      record_post_prefix_execution image base code s pc,
      execute_ordinary_step image _ _ _ fuel coins guardFetch ordinary]
    simp [recordPostState,done,Execution.charge,instructionCycles,←Nat.add_assoc]
  · have jumpPC : (recordGuard (recordPostPrefix s 2)).pc=base+12 := by
      rw [record_guard_pc,ite_eq_right done,prefixPC,BitVec.add_assoc]
      rfl
    have jumpFetch : fetch image (recordGuard (recordPostPrefix s 2))=some (.base (.JAL .x0 2088896)) := by
      exact code 3 (by decide) _ jumpPC
    have jumpStep : ordinaryStep (recordGuard (recordPostPrefix s 2)) (.base (.JAL .x0 2088896))=
        some (recordJump (recordGuard (recordPostPrefix s 2))) := rfl
    rw [recordPostCycles,ite_eq_right done,show 4+fuel=2+((fuel+1)+1) by omega,
      record_post_prefix_execution image base code s pc,
      execute_ordinary_step image _ _ _ (fuel+1) coins guardFetch ordinary,
      execute_ordinary_step image _ _ _ fuel coins jumpFetch jumpStep]
    simp [recordPostState,done,Execution.charge,instructionCycles,←Nat.add_assoc]

theorem record_reset_ready (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat) (sourceReg : s.getReg .x5=BitVec.ofNat 64 source)
    (outputReg : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (memory : BytesAt s (BitVec.ofNat 64 source) (rawFieldsBytes (recordRawFields record)++suffix))
    (ordered : output≤source) (separate : source+498+suffix.length≤metadata)
    (capacity : metadata+34≤MEMORY_BYTES) :
    RawFieldsReady (recordRawFields record) suffix [] [] (recordResetPrefix s 3) source output metadata := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [record_reset_register _ _ (by decide),sourceReg]
  · simpa only [List.length_nil,Nat.add_zero,record_reset_register s .x6 (by decide)] using outputReg
  · simpa only [List.length_nil,Nat.add_zero,record_reset_metadata] using scratch
  · intro index inside
    rw [record_reset_byte]
    exact memory index inside
  · intro index inside; simp at inside
  · intro index inside; simp at inside
  · simpa using ordered
  · simpa only [record_raw_fields_length] using separate
  · rw [List.length_nil,Nat.add_zero,record_raw_fields_count]
    unfold MEMORY_BYTES at capacity
    omega

theorem record_post_counter (s : MachineState) (n : Nat) (count : s.getReg .x29=BitVec.ofNat 64 (n+1)) :
    (recordPostState s).getReg .x29=BitVec.ofNat 64 n := by
  rw [record_post_register,record_post_count,count]
  have one : (1 : Word)=BitVec.ofNat 64 1 := by decide
  rw [one]
  simpa only [Nat.add_sub_cancel] using BitVec.ofNat_sub_ofNat_of_le (n+1) 1 (by decide) (by omega)

theorem record_post_done (s : MachineState) (n : Nat) (fit : n<2^64)
    (count : s.getReg .x29=BitVec.ofNat 64 (n+1)) :
    recordDone (recordPostPrefix s 2)=decide (n=0) := by
  have next := record_post_counter s n count
  rw [record_post_register] at next
  rw [recordDone,next]
  change (n%2^64 == 0)=decide (n=0)
  rw [Nat.mod_eq_of_lt fit]
  cases n <;> rfl

end CommitGolfCandidate.Chained.Native
