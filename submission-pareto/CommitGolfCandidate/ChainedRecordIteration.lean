import CommitGolfCandidate.ChainedRecordControl

/-! One complete native record-loop iteration, including the real back/exit edge. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def recordIterationState (record : InteriorCodec.Record) (s : MachineState) : MachineState :=
  recordPostState (recordPackedState record (recordResetPrefix s 3))
def recordIterationCycles (record : InteriorCodec.Record) (s : MachineState) : Nat :=
  3+recordPackCycles record (recordResetPrefix s 3)+
    recordPostCycles (recordPackedState record (recordResetPrefix s 3))

theorem record_iteration_execution (record : InteriorCodec.Record) (suffix : Proof) (s : MachineState)
    (source output metadata : Nat) (pc : s.pc=4120)
    (sourceReg : s.getReg .x5=BitVec.ofNat 64 source) (outputReg : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (memory : BytesAt s (BitVec.ofNat 64 source) (rawFieldsBytes (recordRawFields record)++suffix))
    (ordered : output≤source) (separate : source+498+suffix.length≤metadata)
    (capacity : metadata+34≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (recordIterationCycles record s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordIterationState record s) coins
          return result.charge (recordIterationCycles record s) 0) := by
  have code := controller_record_control_at openingControllerImage 4096 opening_controller_ops_at
  have ready := record_reset_ready record suffix s source output metadata sourceReg outputReg scratch memory
    ordered separate capacity
  have bodyPC : (recordResetPrefix s 3).pc=4132 := by
    rw [record_reset_pc _ 3 (by decide),pc]
    rfl
  have postPC := record_pack_pc record suffix (recordResetPrefix s 3) source output metadata ready capacity bodyPC
  rw [show recordIterationCycles record s+fuel=
      3+(recordPackCycles record (recordResetPrefix s 3)+
        (recordPostCycles (recordPackedState record (recordResetPrefix s 3))+fuel)) by
        unfold recordIterationCycles; omega,
    record_reset_execution openingControllerImage 4120 code.1 s pc,
    record_pack_execution record suffix (recordResetPrefix s 3) source output metadata ready capacity bodyPC,
    record_post_execution openingControllerImage 12364 code.2 _ postPC]
  simp [recordIterationState,recordIterationCycles,Execution.charge,←Nat.add_assoc]

theorem record_iteration_bound (record : InteriorCodec.Record) (s : MachineState) :
    recordIterationCycles record s≤2273 := by
  have pack := record_pack_bound record (recordResetPrefix s 3)
  have post : recordPostCycles (recordPackedState record (recordResetPrefix s 3))≤4 := by
    unfold recordPostCycles
    split <;> omega
  unfold recordIterationCycles
  omega

theorem record_iteration_range_execution (record : InteriorCodec.Record) (s : MachineState)
    (source output metadata n : Nat) (pc : s.pc=4120)
    (sourcePointer : s.getReg .x5=BitVec.ofNat 64 source)
    (outputPointer : s.getReg .x6=BitVec.ofNat 64 output)
    (scratch : s.getReg .x17+0x200000000=BitVec.ofNat 64 metadata)
    (count : s.getReg .x29=BitVec.ofNat 64 (n+1)) (countFit : n<2^64)
    (sourceRoom : source+498≤MEMORY_BYTES) (outputRoom : output+497≤MEMORY_BYTES)
    (metaRoom : metadata+34≤MEMORY_BYTES) :
    (∀ fuel coins, execute openingControllerImage (recordIterationCycles record s+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (recordIterationState record s) coins
          return result.charge (recordIterationCycles record s) 0)) ∧
    (recordIterationState record s).pc=(if n=0 then 12380 else 4120) ∧
    (recordIterationState record s).getReg .x5=BitVec.ofNat 64 (source+498) ∧
    (recordIterationState record s).getReg .x29=BitVec.ofNat 64 n ∧
    ∃ increment : Nat, increment≤497 ∧
      (recordIterationState record s).getReg .x6=BitVec.ofNat 64 (output+increment) := by
  have code := controller_record_control_at openingControllerImage 4096 opening_controller_ops_at
  have bodyPC : (recordResetPrefix s 3).pc=4132 := by
    rw [record_reset_pc _ 3 (by decide),pc]
    rfl
  obtain ⟨packRun,packPC,packSource,increment,incrementBound,packOutput⟩ :=
    record_pack_range_execution record (recordResetPrefix s 3) source output metadata bodyPC
      (by rw [record_reset_register _ .x5 (by decide),sourcePointer])
      (by rw [record_reset_register _ .x6 (by decide),outputPointer])
      (by rw [record_reset_metadata,scratch]) sourceRoom outputRoom metaRoom
  have packedCount : (recordPackedState record (recordResetPrefix s 3)).getReg .x29=
      BitVec.ofNat 64 (n+1) := by
    rw [record_pack_control _ _ .x29 (by simp),record_reset_register _ .x29 (by decide),count]
  have done := record_post_done _ n countFit packedCount
  refine ⟨?_,?_,?_,record_post_counter _ n packedCount,increment,incrementBound,?_⟩
  · intro fuel coins
    rw [show recordIterationCycles record s+fuel=
      3+(recordPackCycles record (recordResetPrefix s 3)+
        (recordPostCycles (recordPackedState record (recordResetPrefix s 3))+fuel)) by
          unfold recordIterationCycles; omega,
      record_reset_execution openingControllerImage 4120 code.1 s pc,packRun,
      record_post_execution openingControllerImage 12364 code.2 _ packPC]
    simp [recordIterationState,recordIterationCycles,Execution.charge,←Nat.add_assoc]
  · rw [recordIterationState,record_post_pc _ packPC,done]
    by_cases empty : n=0 <;> simp [empty]
  · rw [recordIterationState,record_post_register,
      record_post_prefix_register _ .x5 (by decide) (by decide)]
    exact packSource
  · rw [recordIterationState,record_post_register,record_post_output]
    exact packOutput

end CommitGolfCandidate.Chained.Native
