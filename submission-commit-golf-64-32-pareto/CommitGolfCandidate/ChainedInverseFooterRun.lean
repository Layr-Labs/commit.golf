import CommitGolfCandidate.ChainedInverseFooterControl

/-! Exact variable-count footer execution through opaque iteration equations. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option Elab.async false
attribute [local irreducible] execute

@[irreducible] def inverseFooterIterate (step : MachineState → MachineState) : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => inverseFooterIterate step n (step s)
theorem inverse_footer_iterate_zero (step : MachineState → MachineState) (s : MachineState) :
    inverseFooterIterate step 0 s=s := by rw [inverseFooterIterate]
theorem inverse_footer_iterate_succ (step : MachineState → MachineState) (n : Nat) (s : MachineState) :
    inverseFooterIterate step (n+1) s=inverseFooterIterate step n (step s) := by rw [inverseFooterIterate]

@[irreducible] def inverseFooterRowsState : Nat → MachineState → MachineState :=
  inverseFooterIterate inverseFooterFieldState
theorem inverse_footer_rows_zero (s : MachineState) : inverseFooterRowsState 0 s=s := by
  rw [inverseFooterRowsState,inverse_footer_iterate_zero]
theorem inverse_footer_rows_succ (n : Nat) (s : MachineState) :
    inverseFooterRowsState (n+1) s=inverseFooterRowsState n (inverseFooterFieldState s) := by
  rw [inverseFooterRowsState,inverse_footer_iterate_succ]

structure InverseFooterReady (n : Nat) (s : MachineState) (source output metadata : Nat) : Prop where
  sourcePointer : s.getReg .x5=BitVec.ofNat 64 source
  outputPointer : s.getReg .x6=BitVec.ofNat 64 output
  metaPointer : s.getReg .x7=BitVec.ofNat 64 metadata
  skip : s.getReg .x9=1#64
  count : s.getReg .x22=BitVec.ofNat 64 n
  sourceRoom : source+29*n+1≤MEMORY_BYTES
  outputRoom : output+30*n≤MEMORY_BYTES
  metaRoom : metadata+2*n≤MEMORY_BYTES

theorem inverse_footer_ready_step (n : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady (n+1) s source output metadata) :
    InverseFooterReady n (inverseFooterFieldState s) (source+29) (output+30) (metadata+2) := by
  constructor
  · rw [inverse_footer_field_register _ .x5 (by decide),inverse_field_source,ready.sourcePointer]
    exact (BitVec.ofNat_add _ _).symm
  · rw [inverse_footer_field_register _ .x6 (by decide),inverse_field_destination,ready.outputPointer,
      ready.skip,BitVec.add_assoc]
    change BitVec.ofNat 64 output+BitVec.ofNat 64 30=BitVec.ofNat 64 (output+30)
    exact (BitVec.ofNat_add _ _).symm
  · rw [inverse_footer_field_register _ .x7 (by decide),inverse_field_descriptor,ready.metaPointer]
    exact (BitVec.ofNat_add _ _).symm
  · rw [inverse_footer_field_register _ .x9 (by decide),
      inverse_field_frame _ _ .x9 (by decide) (by decide) (by decide) (by decide)]
    exact ready.skip
  · rw [inverse_footer_field_count,ready.count]
    have result := BitVec.ofNat_sub_ofNat_of_le (n+1) 1 (by decide : 1<2^64) (by omega)
    simpa only [Nat.add_sub_cancel] using result
  · have := ready.sourceRoom; omega
  · have := ready.outputRoom; omega
  · have := ready.metaRoom; omega

theorem inverse_footer_body_pc (s : MachineState) : (inverseFieldState 29 s).pc=s.pc+480 := by
  rw [inverseFieldState,inverse_field_tail_pc _ 4 (by decide),low_copy_pc,BitVec.add_assoc]
  rfl

theorem inverse_footer_rows_ready (n : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady n s source output metadata) :
    InverseFooterReady 0 (inverseFooterRowsState n s) (source+29*n) (output+30*n) (metadata+2*n) := by
  induction n generalizing s source output metadata with
  | zero => simpa only [inverse_footer_rows_zero,Nat.mul_zero,Nat.add_zero] using ready
  | succ n ih =>
    have next := inverse_footer_ready_step n s source output metadata ready
    have result := ih (inverseFooterFieldState s) (source+29) (output+30) (metadata+2) next
    simpa only [inverse_footer_rows_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,
      Nat.add_left_comm] using result

theorem inverse_footer_field_execution (image : Image) (base : Word) (code : OpsAt image base inverseFooterOps)
    (s : MachineState) (pc : s.pc=base+4)
    (source : (s.getReg .x5).toNat+30≤MEMORY_BYTES)
    (output : (s.getReg .x6).toNat+30≤MEMORY_BYTES)
    (metadata : (s.getReg .x7).toNat+2≤MEMORY_BYTES) (fuel : Nat) (coins : Bool) :
    execute image (122+fuel) s coins=
      (do let result ← execute image fuel (inverseFooterFieldState s) coins
          return result.charge 122 0) := by
  have bodyCode := inverse_footer_body_at image base code
  have access := field_build_access 29 s source (by omega) metadata
  have destination : accessValid ((lowCopyState 29 s).getReg .x6) 1=true := by
    rw [low_copy_destination]
    exact byte_access_offset _ 29 output
  have bodyPC : (inverseFieldState 29 s).pc=base+484 := by
    rw [inverse_footer_body_pc,pc,BitVec.add_assoc]
    rfl
  have control := inverse_footer_control_execution image (base+484)
    (inverse_footer_control_at image base code) (inverseFieldState 29 s) bodyPC fuel coins
  rw [show 122+fuel=4*29+4+(2+fuel) by omega,
    inverse_field_execution image (base+4) 29 bodyCode.1 bodyCode.2 s pc access.1 access.2.2.1 destination,
    control]
  simp [inverse_footer_control_two,inverseFooterFieldState,Execution.charge,←Nat.add_assoc]

theorem inverse_footer_rows_execution (image : Image) (base : Word) (code : OpsAt image base inverseFooterOps)
    (n : Nat) (s : MachineState) (source output metadata : Nat)
    (ready : InverseFooterReady n s source output metadata)
    (pc : s.pc=if n=0 then base+492 else base+4) (fuel : Nat) (coins : Bool) :
    execute image (122*n+fuel) s coins=
      (do let result ← execute image fuel (inverseFooterRowsState n s) coins
          return result.charge (122*n) 0) := by
  have memoryBound : MEMORY_BYTES≤2^64 := by decide
  induction n generalizing s source output metadata with
  | zero => simp only [Nat.mul_zero,Nat.zero_add,inverse_footer_rows_zero,Execution.charge]
            simp
  | succ n ih =>
    have sourceFit : source<2^64 := by have := ready.sourceRoom; omega
    have outputFit : output<2^64 := by have := ready.outputRoom; omega
    have metaFit : metadata<2^64 := by have := ready.metaRoom; omega
    have sourceNumber : (s.getReg .x5).toNat=source := by
      rw [ready.sourcePointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt sourceFit]
    have outputNumber : (s.getReg .x6).toNat=output := by
      rw [ready.outputPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt outputFit]
    have metaNumber : (s.getReg .x7).toNat=metadata := by
      rw [ready.metaPointer,BitVec.toNat_ofNat,Nat.mod_eq_of_lt metaFit]
    have startPC : s.pc=base+4 := by simpa using pc
    have nextPC : (inverseFooterFieldState s).pc=if n=0 then base+492 else base+4 :=
      inverse_footer_field_pc s base n startPC ready.count (by have := ready.metaRoom; omega)
    have next := inverse_footer_ready_step n s source output metadata ready
    have rest := ih (inverseFooterFieldState s) (source+29) (output+30) (metadata+2) next nextPC
    rw [show 122*(n+1)+fuel=122+(122*n+fuel) by omega,
      inverse_footer_field_execution image base code s startPC
        (by rw [sourceNumber]; have := ready.sourceRoom; omega)
        (by rw [outputNumber]; have := ready.outputRoom; omega)
        (by rw [metaNumber]; have := ready.metaRoom; omega),rest,inverse_footer_rows_succ]
    simp [Execution.charge,Nat.mul_add,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Chained.Native
