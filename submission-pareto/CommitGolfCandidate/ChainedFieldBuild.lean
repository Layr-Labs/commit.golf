import CommitGolfCandidate.ChainedLowCopy

/-! Construct a low-byte body and its exact value/width descriptor natively. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def fieldBuildState (n : Nat) (s : MachineState) : MachineState := fieldDescriptorPrefix (lowCopyState n s) 5

theorem native_field_descriptor (low : Proof) (high : List Bool) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low) (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length)
    (value : s.getByte (s.getReg .x5+BitVec.ofNat 64 low.length)=tailBitsWord 8 high)
    (width : s.getReg .x10=BitVec.ofNat 64 high.length) :
    BytesAt (fieldBuildState low.length s) (s.getReg .x7) (descriptorBytes [high]) := by
  have last : (lowCopyState low.length s).getByte ((lowCopyState low.length s).getReg .x5)=tailBitsWord 8 high := by
    rw [low_copy_source,native_low_copy_plan low s body ahead,write_byte_list_preserves]
    · exact value
    · intro index inside
      exact ahead low.length (by omega) index inside
  have lastWidth : (lowCopyState low.length s).getReg .x10=BitVec.ofNat 64 high.length := by
    rw [low_copy_frame _ _ .x10 (by decide) (by decide) (by decide)]
    exact width
  have result := field_descriptor_memory (lowCopyState low.length s) high last lastWidth
  rw [low_copy_frame _ _ .x7 (by decide) (by decide) (by decide)] at result
  exact result

theorem native_field_low_body (low : Proof) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low) (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length)
    (apart : ∀ index, index<low.length →
      s.getReg .x6+BitVec.ofNat 64 index≠s.getReg .x7 ∧ s.getReg .x6+BitVec.ofNat 64 index≠s.getReg .x7+1)
    (fit : low.length<2^64) : BytesAt (fieldBuildState low.length s) (s.getReg .x6) low := by
  intro index inside
  change (fieldDescriptorPrefix (lowCopyState low.length s) 5).getByte _=_
  rw [field_descriptor_byte,low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),
    ite_eq_right (apart index inside).2,ite_eq_right (apart index inside).1,
    native_low_copy_plan low s body ahead]
  exact write_byte_list_read _ _ low fit index inside

theorem field_build_source (n : Nat) (s : MachineState) :
    (fieldBuildState n s).getReg .x5=(s.getReg .x5+BitVec.ofNat 64 n)+s.getReg .x9 := by
  rw [fieldBuildState,field_descriptor_source,low_copy_source,
    low_copy_frame _ _ .x9 (by decide) (by decide) (by decide)]

theorem field_build_destination (n : Nat) (s : MachineState) :
    (fieldBuildState n s).getReg .x6=s.getReg .x6+BitVec.ofNat 64 n := by
  rw [fieldBuildState,field_descriptor_frame _ .x6 (by decide) (by decide) (by decide),low_copy_destination]

theorem field_build_descriptor_pointer (n : Nat) (s : MachineState) :
    (fieldBuildState n s).getReg .x7=s.getReg .x7+2 := by
  rw [fieldBuildState,field_descriptor_pointer,low_copy_frame _ _ .x7 (by decide) (by decide) (by decide)]

theorem field_build_execution (image : Image) (base : Word) (n : Nat)
    (copyCode : LowCopyAt image base n) (descriptorCode : FieldDescriptorAt image (base+BitVec.ofNat 64 (16*n)))
    (s : MachineState) (pc : s.pc=base) (ready : LowCopyReady n s)
    (source : accessValid ((lowCopyState n s).getReg .x5) 1=true)
    (value : accessValid ((lowCopyState n s).getReg .x7) 1=true)
    (width : accessValid ((lowCopyState n s).getReg .x7+1) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (4*n+5+fuel) s coins=
      (do let result ← execute image fuel (fieldBuildState n s) coins
          return result.charge (4*n+5) 0) := by
  have nextPC : (lowCopyState n s).pc=base+BitVec.ofNat 64 (16*n) := by rw [low_copy_pc,pc]
  rw [Nat.add_assoc,low_copy_execution image base n copyCode s pc ready,
    field_descriptor_execution image _ descriptorCode _ nextPC source value width]
  simp [fieldBuildState,Execution.charge,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end CommitGolfCandidate.Chained.Native
