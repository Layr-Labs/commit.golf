import CommitGolfCandidate.ChainedInverseFieldTail

/-! Native reconstruction of low bytes and a parsed high byte into a raw field. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] execute

def inverseFieldState (n : Nat) (s : MachineState) : MachineState :=
  inverseFieldTailPrefix (lowCopyState n s) 4

theorem native_inverse_field_plan (low : Proof) (high : BitVec 8) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length)
    (value : s.getByte (s.getReg .x7)=high)
    (apart : ∀ index, index<low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index)
    (query : Word) :
    (inverseFieldState low.length s).getByte query=
      writeByteList s.getByte (s.getReg .x6) (low++[high]) query := by
  have loaded : (lowCopyState low.length s).getByte ((lowCopyState low.length s).getReg .x7)=high := by
    rw [low_copy_frame _ _ .x7 (by decide) (by decide) (by decide),
      native_low_copy_plan low s body ahead,write_byte_list_preserves _ _ low _ apart]
    exact value
  rw [inverseFieldState,inverse_field_tail_byte,loaded,low_copy_destination,
    native_low_copy_plan low s body ahead,write_byte_list_append]
  rfl

theorem native_inverse_field_bytes (low padding : Proof) (high : BitVec 8) (s : MachineState)
    (body : BytesAt s (s.getReg .x5) low)
    (ahead : CopyAhead (s.getReg .x5) (s.getReg .x6) low.length)
    (value : s.getByte (s.getReg .x7)=high)
    (apart : ∀ index, index<low.length → s.getReg .x7≠s.getReg .x6+BitVec.ofNat 64 index)
    (pad : BytesAt s (s.getReg .x6+BitVec.ofNat 64 (low.length+1)) padding)
    (fit : low.length+1+padding.length<2^64) :
    BytesAt (inverseFieldState low.length s) (s.getReg .x6) ((low++[high])++padding) := by
  rw [bytes_at_append]
  constructor
  · intro index inside
    rw [native_inverse_field_plan low high s body ahead value apart]
    exact write_byte_list_read _ _ _ (by simp; omega) index inside
  · simp only [List.length_append,List.length_singleton]
    intro index inside
    rw [native_inverse_field_plan low high s body ahead value apart,write_byte_list_preserves]
    · exact pad index inside
    · intro written before same
      rw [byte_offset_add] at same
      have impossible := byte_offset_inj (s.getReg .x6) (low.length+1+index) written
        (by omega) (by simp only [List.length_append,List.length_singleton] at before; omega) same
      simp only [List.length_append,List.length_singleton] at before
      omega

theorem inverse_field_source (n : Nat) (s : MachineState) :
    (inverseFieldState n s).getReg .x5=s.getReg .x5+BitVec.ofNat 64 n := by
  rw [inverseFieldState,inverse_field_tail_frame _ .x5 (by decide) (by decide) (by decide),low_copy_source]

theorem inverse_field_destination (n : Nat) (s : MachineState) :
    (inverseFieldState n s).getReg .x6=(s.getReg .x6+BitVec.ofNat 64 n)+s.getReg .x9 := by
  rw [inverseFieldState,inverse_field_tail_destination,low_copy_destination,
    low_copy_frame _ _ .x9 (by decide) (by decide) (by decide)]

theorem inverse_field_descriptor (n : Nat) (s : MachineState) :
    (inverseFieldState n s).getReg .x7=s.getReg .x7+2 := by
  rw [inverseFieldState,inverse_field_tail_descriptor,low_copy_frame _ _ .x7 (by decide) (by decide) (by decide)]

theorem inverse_field_frame (n : Nat) (s : MachineState) (reg : Reg)
    (source : reg≠.x5) (destination : reg≠.x6) (descriptor : reg≠.x7) (temporary : reg≠.x11) :
    (inverseFieldState n s).getReg reg=s.getReg reg := by
  rw [inverseFieldState,inverse_field_tail_frame _ reg destination descriptor temporary,
    low_copy_frame _ _ reg source destination temporary]

theorem inverse_field_execution (image : Image) (base : Word) (n : Nat)
    (copyCode : LowCopyAt image base n)
    (tailCode : InverseFieldTailAt image (base+BitVec.ofNat 64 (16*n)))
    (s : MachineState) (pc : s.pc=base) (ready : LowCopyReady n s)
    (source : accessValid ((lowCopyState n s).getReg .x7) 1=true)
    (destination : accessValid ((lowCopyState n s).getReg .x6) 1=true) (fuel : Nat) (coins : Bool) :
    execute image (4*n+4+fuel) s coins=
      (do let result ← execute image fuel (inverseFieldState n s) coins
          return result.charge (4*n+4) 0) := by
  have nextPC : (lowCopyState n s).pc=base+BitVec.ofNat 64 (16*n) := by rw [low_copy_pc,pc]
  rw [Nat.add_assoc,low_copy_execution image base n copyCode s pc ready,
    inverse_field_tail_execution image _ tailCode _ nextPC source destination]
  simp [inverseFieldState,Execution.charge,Nat.add_assoc]

end CommitGolfCandidate.Chained.Native
